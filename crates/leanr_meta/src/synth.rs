//! Tabled type-class-synthesis engine: table state, table keys, and
//! waiter/answer bookkeeping (task B4), plus the RESOLUTION DRIVER
//! itself ([`MetaCtx::synth_instance`], task B5).
//!
//! Everything above the "The resolution driver (task B5)" banner is
//! table mechanics; everything below it drives resolution. Much of the
//! doc that follows was written by B4 while the driver was still
//! unwritten and phrases open questions as constraints ON B5 -- each
//! such passage now carries a note recording how B5 answered it, and
//! the two structural HARD REQUIREMENTS (universe-level refresh and the
//! append-only consumer arena) are answered at
//! [`MetaCtx::refresh_instance_levels`] and [`ConsumerNode`]'s own doc
//! respectively. B4's original framing is kept rather than rewritten,
//! because the reasoning it records is what makes those answers
//! checkable.
//!
//! oracle: `Lean.Meta.SynthInstance` (`SynthInstance.lean`), toolchain
//! leanprover/lean4:v4.33.0-rc1 -- specifically `Instance`/`GeneratorNode`
//! (:40-52), `ConsumerNode` (:54-59), `Waiter` (:61-66), the `MkTableKey`
//! namespace and `mkTableKey` (:92-199), `Answer`/`TableEntry` (:232-239),
//! and `SynthInstance.State` (:244-254) -- plus `Lean.Meta.
//! AbstractMVarsResult` (`Meta/Basic.lean:338-346`), which `Answer.result`
//! is typed by. The driver half transcribes `main` (:676-690), `synth`
//! (:668-674), `step` (:660-667), `generate` (:625-658), `resume`
//! (:635-651), `consume` (:534-579), `newSubgoal` (:281-292),
//! `mkGeneratorNode?` (:243-256), `mkTableKeyFor` (:298-302),
//! `getSubgoals` (:317-337), `tryResolve` (:345-420), `tryAnswer`
//! (:441-449), `wakeUp` (:422-434), `mkAnswer` (:453-459) and
//! `addAnswer` (:463-478), plus `Lean.Meta.abstractMVars`
//! (`Meta/AbstractMVars.lean:127-133`) and `openAbstractMVarsResult`
//! (`Meta/Basic.lean:424-429`) -- the two algorithms B4 named as a seam
//! it was leaving to B5.
//!
//! # `Mul N` agrees with the oracle's `#synth`
//!
//! `Mul N` over the `Instances.olean` fixture resolves to `instMulN`
//! here, matching the pinned toolchain's own `#synth Mul N` exactly (not
//! merely a defeq alternative). This was NOT always true: an earlier
//! version of `DiscrTree::process` (B1) inverted `getUnify`'s
//! `visitStar`-then-`visitNonStar` order (`DiscrTree/Main.lean:606`), so
//! candidates reached `generate` in the opposite try-order and this
//! goal resolved to `Semigroup.toMul instSemigroupN` instead -- still a
//! genuine inhabitant of the goal (defeq, never unsound), but a
//! DIFFERENT term from the oracle's. That was pinned as a characterized
//! divergence by
//! `mul_n_matches_the_oracles_synth_answer_via_the_corrected_discr_tree_order`
//! below (formerly named for the divergence it characterized); B1 has
//! since been corrected to match the oracle's order, and that same test
//! now pins the positive result: leanr's canonical instance term for
//! this goal agrees with Lean's `#synth`, which is what Task B7's tier-1
//! differential gate needs to compare against an oracle dump.
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
//! # Dead-code allow, narrowed
//!
//! B5's tabled-resolution driver has landed (`synth_instance` /
//! `synth_instance_main` / `synth_instance_body` below), and every item
//! in this module -- and, transitively, every item in
//! `instances.rs`/`discr_path.rs`/`discr_tree.rs` -- is now reachable
//! from it. The blanket `#![allow(dead_code)]` this module used to carry
//! is gone; the one narrow, per-item allow that remains sits on
//! `synth_instance` itself (its own doc comment explains why: it is the
//! crate's typeclass-synthesis ENTRY POINT, but has no non-test caller
//! until the elaborator layer lands, owner M4b). No other item in this
//! module carries an allow.

use std::collections::HashMap;

use leanr_kernel::bank::levels::LevelRow;
use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId, LevelsId, NameId};
use leanr_kernel::{abstract_fvars, instantiate, instantiate_level_params, instantiate_rev};
use leanr_kernel::{Nat, MAX_REC_DEPTH};

use crate::instances::Instance;
use crate::metactx::MetaSnapshot;
use crate::{LMVarId, MVarId, MetaCtx, MetaError, TransparencyMode};

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
///
/// **B5 closed the `mctx`/`typeHasMVars` seams recorded above**:
/// `mctx` is this crate's [`MetaSnapshot`] (the assignment maps + the
/// postponed queue — see `metactx.rs`), re-entered via
/// `MetaCtx::with_synth_mctx`, which is this crate's `withMCtx`
/// analogue; `type_has_mvars` is the oracle's `typeHasMVars` verbatim
/// (`mvarType.hasMVar`, :253), read by `generate`'s canonical-instances
/// short-circuit.
pub(crate) struct GeneratorNode {
    pub goal: ExprId,
    pub key: GoalKey,
    pub remaining: Vec<Instance>,
    /// oracle: `GeneratorNode.mctx` (:49) — the state every candidate
    /// trial for this node restarts from.
    pub mctx: MetaSnapshot,
    /// oracle: `GeneratorNode.typeHasMVars` (:52, set at :253 from
    /// `mvarType.hasMVar`).
    pub type_has_mvars: bool,
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
///
/// **B5's answer to that HARD constraint: option (a), APPEND-ONLY.**
/// [`SynthState::consumers`] is a module-PRIVATE field whose only
/// mutator is [`SynthState::push_consumer`] (there is no `consumers_mut`,
/// no `IndexMut`, and no other `&mut` path to a slot anywhere in this
/// crate), so a slot, once pushed, is immutable for the rest of the
/// search and `next` below is frozen at exactly the position the waiter
/// that points at it was waiting on. Advancing to the next subgoal
/// builds a WHOLE NEW node with `next + 1` and pushes it, mirroring the
/// oracle's own `resume` (:650), which likewise constructs a new
/// `ConsumerNode` with `subgoals := rest` and never touches the
/// waited-on snapshot.
#[derive(Clone)]
pub(crate) struct ConsumerNode {
    pub key: GoalKey,
    pub mvar: MVarId,
    pub subgoals: Vec<ExprId>,
    pub next: usize,
    /// oracle: `ConsumerNode.mctx` (:57).
    pub mctx: MetaSnapshot,
    /// oracle: `ConsumerNode.size` (:58) — "instance size so far",
    /// checked against `synthInstance.maxSize` in `addAnswer` (:466).
    pub size: usize,
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
///
/// **B5 closed the `result?`/`resumeStack` seams recorded above**:
/// [`SynthState::result`] is the oracle's `result?` (:250, set by
/// `wakeUp`'s `.root` arm) and [`SynthState::resume_stack`] is its
/// `resumeStack` (:245), re-represented as `(consumer index, Answer)`
/// pairs rather than `(ConsumerNode × Answer)` values, per the
/// index-into-an-arena re-representation this module already chose for
/// [`Waiter`].
///
/// # Determinism
///
/// `answers` is a `HashMap`, but nothing in this module or its driver
/// ever ITERATES it — every access is a keyed `get`/`get_mut`/`insert`.
/// The order-significant sequences (`generators`, `resume_stack`,
/// `TableEntry::waiters`, `TableEntry::answers`, `GeneratorNode::
/// remaining`) are all `Vec`s, walked in a fixed direction. Global
/// Constraints: "no `HashMap` iteration on any order-significant path".
#[derive(Default)]
pub(crate) struct SynthState {
    pub answers: HashMap<GoalKey, TableEntry>,
    pub generators: Vec<GeneratorNode>,
    /// **APPEND-ONLY ARENA — see [`ConsumerNode`]'s own doc for why this
    /// is a correctness requirement and not a style preference.**
    /// Deliberately NOT `pub`: [`SynthState::push_consumer`] is the only
    /// mutator and [`SynthState::consumer`] the only reader, both
    /// defined below, so no code path anywhere can obtain a `&mut` to a
    /// slot an outstanding `Waiter::Consumer` still points at. B4's own
    /// shape had this field `pub`; narrowing it is how option (a) of
    /// that task's HARD constraint is ENFORCED rather than merely
    /// promised.
    consumers: Vec<ConsumerNode>,
    /// oracle: `State.resumeStack` (:245), as `(consumer arena index,
    /// the answer that woke it)`.
    pub resume_stack: Vec<(usize, Answer)>,
    /// oracle: `State.result?` (:250).
    pub result: Option<AbstractMVarsResult>,
    pub step: u64,
}

impl SynthState {
    /// Push a brand-new consumer node and return its arena index. The
    /// ONLY mutator of `consumers` — see that field's own doc.
    pub(crate) fn push_consumer(&mut self, node: ConsumerNode) -> usize {
        self.consumers.push(node);
        self.consumers.len() - 1
    }

    /// Read back an (immutable, frozen-at-push-time) consumer node.
    /// Panics on an out-of-range index: every index handed out came from
    /// `push_consumer` on this same state and the arena never shrinks,
    /// so this is an internal-invariant violation, the same posture
    /// `add_waiter`/`add_answer` take for a missing entry.
    pub(crate) fn consumer(&self, idx: usize) -> &ConsumerNode {
        self.consumers
            .get(idx)
            .expect("consumer: index out of range -- the arena is append-only")
    }

    /// oracle: `findEntry?` (:288-289).
    pub(crate) fn find_entry(&self, key: &GoalKey) -> Option<&TableEntry> {
        self.answers.get(key)
    }
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

// =======================================================================
// abstractMVars / openAbstractMVarsResult (task B5 -- the seam B4 named)
// =======================================================================

/// Per-call scratch state for [`MetaCtx::abstract_mvars`]. oracle:
/// `Lean.Meta.AbstractMVars.State` (`Meta/AbstractMVars.lean:15-26`),
/// minus the fields this crate's re-shaping does not need: `ngen`
/// (fresh fvar names come off `MetaCtx::expr_mvar_gen` instead -- see
/// [`MVarAbstractor::fresh_fvar`]), `mctx` (threaded as `ctx` here, the
/// same choice [`KeyNormalizer`] made), `lctx` (the oracle accumulates
/// abstracted binder types into a `LocalContext` purely so its final
/// `mkLambdaFVars` can look them up; this walk carries them in the
/// parallel `fvar_types`/`fvar_names` vecs instead and never touches
/// `MetaCtx::lctx` at all, so abstraction leaves no residue in the
/// caller's local context), and `abstractLevels` (the oracle's own
/// `abstractMVars` entry point, :127, hardcodes it `true`; the `false`
/// setting belongs to `abstractMVars'`, which synthesis never calls).
struct MVarAbstractor<'a, 'e> {
    ctx: &'a mut MetaCtx<'e>,
    next_param_idx: u64,
    param_names: Vec<NameId>,
    lmap: HashMap<LMVarId, LevelId>,
    emap: HashMap<MVarId, ExprId>,
    /// The fresh fvars standing in for abstracted expr mvars, in
    /// abstraction order (oracle: `State.fvars`), with their already-
    /// abstracted types and binder names alongside.
    fvars: Vec<ExprId>,
    fvar_types: Vec<ExprId>,
    fvar_names: Vec<Option<NameId>>,
    /// oracle: `State.mvars` -- the ORIGINAL mvar expressions, which
    /// `AbstractMVarsResult.mvars` reports back.
    mvars: Vec<ExprId>,
    /// `` `_abstMVar `` interned once (oracle: `Name.mkNum `_abstMVar
    /// s.nextParamIdx`, :63).
    abst_prefix: NameId,
    depth: u32,
}

impl<'a, 'e> MVarAbstractor<'a, 'e> {
    fn new(ctx: &'a mut MetaCtx<'e>) -> Result<MVarAbstractor<'a, 'e>, MetaError> {
        let base = Some(ctx.view.store);
        let s = ctx.scratch.intern_str(base, "_abstMVar")?;
        let abst_prefix = ctx.scratch.name_str(base, None, s)?;
        Ok(MVarAbstractor {
            ctx,
            next_param_idx: 0,
            param_names: Vec::new(),
            lmap: HashMap::new(),
            emap: HashMap::new(),
            fvars: Vec::new(),
            fvar_types: Vec::new(),
            fvar_names: Vec::new(),
            mvars: Vec::new(),
            abst_prefix,
            depth: 0,
        })
    }

    /// [`KeyNormalizer::guarded`]'s body again, for the same reason (see
    /// the module-level `RED_ZONE`/`STACK_CHUNK` doc).
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

    /// Mint `` `_abstMVar.<nextParamIdx> `` (oracle: :63-66).
    fn fresh_param_name(&mut self) -> Result<NameId, MetaError> {
        let base = Some(self.ctx.view.store);
        let idx = self.next_param_idx;
        self.next_param_idx += 1;
        let idx_id = self.ctx.scratch.intern_nat(base, &Nat::from(idx))?;
        let n = self
            .ctx
            .scratch
            .name_num(base, Some(self.abst_prefix), idx_id)?;
        self.param_names.push(n);
        Ok(n)
    }

    /// oracle: `mkFreshFVarId` (:38-39) off the state's own `NameGenerator`.
    /// This crate has no `MetaM`-wide name generator to borrow, so the
    /// fresh fvar name comes off `MetaCtx::expr_mvar_gen` (a
    /// process-monotone counter already threaded through `MetaCtx` for
    /// `mk_aux_mvar`) under its own distinct prefix. These fvars are
    /// purely internal: every one of them is abstracted back into a
    /// `BVar` by [`MVarAbstractor::mk_lambda_over`] before the result
    /// escapes, so the name is never observable in the answer -- it only
    /// has to be distinct from any fvar ALREADY in the term being
    /// abstracted, which a dedicated prefix plus a monotone counter
    /// gives (the oracle's own `ngen` makes exactly the same
    /// freshness-by-construction argument).
    fn fresh_fvar(&mut self) -> Result<ExprId, MetaError> {
        let base = Some(self.ctx.view.store);
        let idx = self.ctx.expr_mvar_gen;
        self.ctx.expr_mvar_gen += 1;
        let prefix_str = self.ctx.scratch.intern_str(base, "_leanr_abst_fvar")?;
        let prefix = self.ctx.scratch.name_str(base, None, prefix_str)?;
        let idx_id = self.ctx.scratch.intern_nat(base, &Nat::from(idx))?;
        let name = self.ctx.scratch.name_num(base, Some(prefix), idx_id)?;
        Ok(self.ctx.scratch.expr_fvar(base, Some(name))?)
    }

    /// oracle: `abstractLevelMVars` (`Meta/AbstractMVars.lean:43-66`).
    /// Structurally [`KeyNormalizer::norm_level`] with a different
    /// naming scheme and a `param_names` side-effect; the two are kept
    /// separate rather than parametrized because they answer different
    /// oracle functions with different (accumulating vs. not)
    /// post-conditions.
    fn level(&mut self, l: LevelId) -> Result<LevelId, MetaError> {
        self.ctx.step()?;
        let base = Some(self.ctx.view.store);
        if self.ctx.scratch.level_flags(base, l) & 0b10 == 0 {
            return Ok(l);
        }
        self.guarded(|a| a.level_body(l))
    }

    fn level_body(&mut self, l: LevelId) -> Result<LevelId, MetaError> {
        let base = Some(self.ctx.view.store);
        match *self.ctx.scratch.level_row(base, l) {
            LevelRow::Zero | LevelRow::Param(_) => Ok(l),
            LevelRow::MVar(name) => {
                let Some(name) = name else { return Ok(l) };
                let lid = LMVarId(name);
                if let Some(v) = self.ctx.mctx.level_assignment(lid) {
                    return self.level(v);
                }
                if let Some(&renamed) = self.lmap.get(&lid) {
                    return Ok(renamed);
                }
                let pname = self.fresh_param_name()?;
                let renamed = self.ctx.scratch.level_param(base, Some(pname))?;
                self.lmap.insert(lid, renamed);
                Ok(renamed)
            }
            LevelRow::Succ(a) => {
                let a2 = self.level(a)?;
                if a2 == a {
                    Ok(l)
                } else {
                    Ok(self.ctx.scratch.level_succ(base, a2)?)
                }
            }
            LevelRow::Max(a, b) => {
                let (a2, b2) = (self.level(a)?, self.level(b)?);
                if a2 == a && b2 == b {
                    Ok(l)
                } else {
                    Ok(self.ctx.scratch.level_max(base, a2, b2)?)
                }
            }
            LevelRow::IMax(a, b) => {
                let (a2, b2) = (self.level(a)?, self.level(b)?);
                if a2 == a && b2 == b {
                    Ok(l)
                } else {
                    Ok(self.ctx.scratch.level_imax(base, a2, b2)?)
                }
            }
        }
    }

    /// oracle: `abstractExprMVars` (`Meta/AbstractMVars.lean:71-113`).
    fn expr(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        self.ctx.step()?;
        let d = self.ctx.data(e);
        if !d.has_expr_mvar() && !d.has_level_mvar() {
            return Ok(e);
        }
        self.guarded(|a| a.expr_body(e))
    }

    fn expr_body(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let base = Some(self.ctx.view.store);
        match self.ctx.node(e) {
            Node::MVar { id: Some(id) } => {
                let mid = MVarId(id);
                if let Some(v) = self.ctx.mctx.assignment(mid) {
                    return self.expr(v);
                }
                // oracle: `if decl.depth != mctx.depth then return e`
                // (:91-93) -- under this crate's flat-depth collapse
                // (see this module's doc), the only "treated as a
                // constant" case left is an mvar with no declaration at
                // all, which has no type to abstract by either.
                let Some(decl_ty) = self.ctx.mctx.decl(mid).map(|d| d.ty) else {
                    return Ok(e);
                };
                let user_name = self.ctx.mctx.decl(mid).and_then(|d| d.user_name);
                if let Some(&fvar) = self.emap.get(&mid) {
                    return Ok(fvar);
                }
                let inst_ty = self.ctx.instantiate_mvars(decl_ty)?;
                let ty = self.expr(inst_ty)?;
                let fvar = self.fresh_fvar()?;
                self.emap.insert(mid, fvar);
                self.fvars.push(fvar);
                self.fvar_types.push(ty);
                self.fvar_names.push(user_name);
                self.mvars.push(e);
                Ok(fvar)
            }
            Node::MVar { id: None } => Ok(e),
            Node::Sort { level } => {
                let l2 = self.level(level)?;
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
                    let lv2 = self.level(lv)?;
                    changed |= lv2 != lv;
                    new_list.push(lv2);
                }
                if !changed {
                    Ok(e)
                } else {
                    let levels2 = self.ctx.scratch.intern_level_list(base, &new_list)?;
                    Ok(self.ctx.scratch.expr_const(base, name, levels2)?)
                }
            }
            Node::App { f, arg } => {
                let (f2, a2) = (self.expr(f)?, self.expr(arg)?);
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
                let (t2, b2) = (self.expr(binder_type)?, self.expr(body)?);
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
                let (t2, b2) = (self.expr(binder_type)?, self.expr(body)?);
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
                let (t2, v2, b2) = (self.expr(ty)?, self.expr(value)?, self.expr(body)?);
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
                let e2 = self.expr(expr)?;
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
                let s2 = self.expr(structure)?;
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
                let s2 = self.expr(structure)?;
                if s2 == structure {
                    Ok(e)
                } else {
                    Ok(self.ctx.scratch.expr_proj(base, type_name, &idxn, s2)?)
                }
            }
            _ => Ok(e),
        }
    }

    /// `mkLambdaFVars s.fvars e` (oracle: `abstractMVars`, :131) --
    /// `assign.rs::mk_lambda_over_fvars`'s exact fold, except the binder
    /// name/type come from this walk's own parallel vecs rather than
    /// from `MetaCtx::lctx` (nothing here declares these fvars in a
    /// local context; see [`MVarAbstractor`]'s own doc). Every binder is
    /// `BinderInfo::Default`, matching `LocalContext.mkLocalDecl`'s own
    /// default at :110.
    fn mk_lambda_over(&mut self, body: ExprId) -> Result<ExprId, MetaError> {
        let base = Some(self.ctx.view.store);
        let mut r = body;
        let mut i = self.fvars.len();
        while i > 0 {
            i -= 1;
            r = abstract_fvars(
                self.ctx.scratch,
                base,
                r,
                std::slice::from_ref(&self.fvars[i]),
                &mut self.ctx.guard,
            )?;
            let ty = abstract_fvars(
                self.ctx.scratch,
                base,
                self.fvar_types[i],
                &self.fvars[..i],
                &mut self.ctx.guard,
            )?;
            r = self.ctx.scratch.expr_lam(
                base,
                self.fvar_names[i],
                ty,
                r,
                leanr_kernel::BinderInfo::Default,
            )?;
        }
        Ok(r)
    }
}

// =======================================================================
// The resolution driver (task B5)
// =======================================================================

/// oracle: `synthInstance.maxSize`'s default (`SynthInstance.lean:24-27`),
/// threaded by `main`'s `maxResultSize` parameter into `addAnswer`'s
/// own `cNode.size >= maxResultSize` guard (:466). Fixed here rather
/// than made configurable: this crate has no `Options` channel, and
/// `Config` (`config.rs`) models `whnf`/`isDefEq` knobs only.
const MAX_RESULT_SIZE: usize = 128;

impl<'e> MetaCtx<'e> {
    // -------------------------------------------------------------------
    // abstractMVars / openAbstractMVarsResult
    // -------------------------------------------------------------------

    /// oracle: `Lean.Meta.abstractMVars` (`Meta/AbstractMVars.lean:
    /// 127-133`) -- abstract every (assignable, current-depth)
    /// metavariable in `e`, returning the fresh universe params that
    /// replaced its level mvars, the expr mvars that were abstracted,
    /// and `fun (m_1 : A_1) .. (m_k : A_k) => e'`.
    pub(crate) fn abstract_mvars(&mut self, e: ExprId) -> Result<AbstractMVarsResult, MetaError> {
        // oracle: `let e ← instantiateMVars e` (:128). See
        // `normalize_goal_key`'s own doc for why this crate's
        // `instantiate_mvars` covers the EXPR side only, and why the
        // LEVEL side is folded into the walk's own mvar arm instead.
        let e = self.instantiate_mvars(e)?;
        let mut a = MVarAbstractor::new(self)?;
        let body = a.expr(e)?;
        let expr = a.mk_lambda_over(body)?;
        Ok(AbstractMVarsResult {
            param_names: a.param_names,
            mvars: a.mvars,
            expr,
        })
    }

    /// oracle: `Lean.Meta.openAbstractMVarsResult` (`Meta/Basic.lean:
    /// 424-429`): mint one fresh level mvar per abstracted param,
    /// substitute, then `lambdaMetaTelescope` the result back open,
    /// replacing exactly `numMVars` binders with fresh expr mvars.
    /// Returns only the resulting EXPRESSION -- the oracle's own
    /// `(mvars, binderInfos, e)` triple's first two components are
    /// unused by both of its synthesis call sites (`tryAnswer` :423-429
    /// and `wakeUp`'s trace at :430, which only ever `isDefEq`/print the
    /// expression).
    pub(crate) fn open_abstract_mvars_result(
        &mut self,
        r: &AbstractMVarsResult,
    ) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        let mut us = Vec::with_capacity(r.param_names.len());
        for _ in &r.param_names {
            us.push(self.fresh_level_mvar()?.1);
        }
        let mut e = instantiate_level_params(
            self.scratch,
            base,
            r.expr,
            &r.param_names,
            &us,
            &mut self.guard,
        )?;
        for _ in 0..r.num_mvars() {
            self.step()?;
            let Node::Lam {
                binder_type, body, ..
            } = self.node(e)
            else {
                // Unreachable by construction: `abstract_mvars` builds
                // exactly `num_mvars` leading lambdas. Stopping early is
                // incompleteness (a partially-opened answer simply fails
                // the caller's `isDefEq`), never a wrong assignment.
                break;
            };
            let (m, _) = self.mk_aux_mvar(binder_type)?;
            e = instantiate(self.scratch, base, body, m, &mut self.guard)?;
        }
        Ok(e)
    }

    // -------------------------------------------------------------------
    // main / synth / step
    // -------------------------------------------------------------------

    /// Synthesize an instance of `ty`. oracle: `Lean.Meta.SynthInstance.
    /// main` (`SynthInstance.lean:676-690`) composed with `synth`
    /// (:668-674) -- seed one root subgoal for `ty` and step the
    /// resolution loop until the root is answered or nothing is left to
    /// do.
    ///
    /// Returns the synthesized TERM (`Ok(Some(_))`), `Ok(None)` when the
    /// search completed with no answer, or an `Err` -- never a `false`
    /// stand-in for a budget or stuck condition:
    /// [`MetaError::StepBudgetExhausted`] (the deterministic per-step
    /// budget, this crate's replacement for the oracle's `checkSystem`
    /// heartbeat check at :662), [`MetaError::DepthBudgetExhausted`]
    /// (re-entrancy, via the `guarded` wrapper below), or
    /// [`MetaError::IsDefEqStuck`] propagated out of a subgoal
    /// unification, which is NEVER collapsed to "this candidate failed".
    ///
    /// The whole trial runs under ONE `checkpoint`/`rollback` pair, so a
    /// failed -- or successful -- synthesis leaves the caller's `mctx`
    /// exactly as it found it; the returned term is already fully
    /// instantiated and metavariable-free on the expr side (`mk_answer`
    /// -> `abstract_mvars`), so it survives that rollback.
    // Narrowed from this module's former blanket `#![allow(dead_code)]`
    // (removed by this task): `synth_instance` is the crate's typeclass-
    // synthesis ENTRY POINT, and every other item in this module and in
    // `instances.rs`/`discr_path.rs`/`discr_tree.rs` is now reachable
    // from it. The entry point itself IS reached from non-test code --
    // `whnf.rs::synth_pending_body` (M4a plan-4 task B6) calls it -- but
    // not yet from the ELABORATOR layer (oracle: `Lean.Elab.Term.synthes
    // izeInstMVarCore` / `synthesizeUsingDefault`,
    // `Elab/SyntheticMVars.lean`), which no task in this plan builds, so
    // some items below remain test-only. Owner: M4b. This one allow
    // covers the whole reachable chain below it; it is deliberately the
    // ONLY dead-code allow in this module.
    //
    // Visibility (M4a plan-4 task B7): `pub`, not `pub(crate)`, because
    // the tier-1 differential gate `crates/leanr_meta/tests/
    // oracle_synth.rs` is a separate crate and must call it. This
    // matches how every other entry point this crate's gates replay
    // against is already exposed (`MetaCtx::whnf`/`infer_type`/
    // `is_def_eq`). Behavior is unchanged; the `#[allow(dead_code)]`
    // above is kept because the ELABORATOR caller described there still
    // does not exist (a `pub` item in a lib crate is never dead-code-
    // linted, so the attribute is now belt-and-braces, retained so the
    // seam's ownership note stays attached to the item it describes).
    #[allow(dead_code)]
    pub fn synth_instance(&mut self, ty: ExprId) -> Result<Option<ExprId>, MetaError> {
        self.guarded(|ctx| ctx.synth_instance_main(ty))
    }

    fn synth_instance_main(&mut self, ty: ExprId) -> Result<Option<ExprId>, MetaError> {
        let snap = self.checkpoint();
        // oracle: `main` wraps the ENTIRE search in `withConfig`
        // (`SynthInstance.lean:963-964`):
        //   { c with isDefEqStuckEx := true, transparency := .instances,
        //            foApprox := true, ctxApprox := true,
        //            constApprox := false, univApprox := false }
        // `Config` is `Copy`, so the whole struct is saved/restored
        // around the search -- the same `whnf_default` save/restore
        // precedent (`whnf.rs:1548`) this module already used for
        // `transparency` alone, now widened to every field this crate
        // HAS a home for:
        //  - `transparency := .instances` -- as before.
        //  - `foApprox := true`, `constApprox := false` -- both real,
        //    consulted fields (`assign.rs::use_fo_approx`/
        //    `process_const_approx`); setting them narrows/widens
        //    higher-order unification exactly as the oracle does during
        //    synthesis.
        //  - `univApprox := false` -- the UNSAFE direction: this
        //    crate's `Config::default` has `univ_approx: true`
        //    (`config.rs`'s own doc says do not "fix" this back to
        //    `false` to match its siblings for the GENERAL defeq
        //    default, which is correct -- but `withConfig` overrides it
        //    to `false` for synthesis specifically, and until now this
        //    driver silently left it `true`, which is MORE PERMISSIVE
        //    than the oracle: a universe unification the oracle refuses
        //    could succeed here, admitting a candidate the oracle
        //    rejects. Fixed here.
        //  - `ctxApprox := true` -- set for fidelity to the wrapper, but
        //    it is presently a NO-OP in this crate: no call site reads
        //    `cfg.ctx_approx` anywhere (`grep` confirms the only
        //    occurrences are `config.rs`'s own declaration/default/
        //    tests). The plan-3 ctxApprox rescue lives in the oracle's
        //    slow term-rewriting path, which this crate has not built;
        //    a naive graft of it onto the bool-result path was reverted
        //    as unsound (plan-3 notes). Setting the flag here does not
        //    resurrect that graft -- it just matches the field to the
        //    oracle's wrapper for the day a real consultation site
        //    lands.
        //  - `isDefEqStuckEx := true` -- NAMED SEAM, not settable: this
        //    crate has no `Config` field for it at all
        //    (`config.rs`'s own doc: "spec-mandated to become a typed
        //    error variant..., so it is not tracked here"), and every
        //    site that would branch on it (`level.rs`, `assign.rs`) has
        //    the `false` case hard-coded into the control flow itself,
        //    not gated through a field this function could flip.
        //    Actually wiring it through requires those sites to grow a
        //    real `MetaError::IsDefEqStuck`-throwing branch, which is
        //    out of this task's scope (`synth.rs`/`instances.rs`(doc)/
        //    `config.rs` only). Owner M4b, citing
        //    `SynthInstance.lean:958-968` and `level.rs`'s own
        //    `isDefEqStuckEx` seam doc.
        //  - `preprocess`/`preprocessOutParam`, and
        //    `withNewMCtxDepth (allowLevelAssignments := true)` -- NAMED
        //    SEAM, no field/mechanism in this crate at all (no
        //    preprocessing pass over the goal type before search; no
        //    mctx-depth model at tier 1, per `level.rs`'s own "Depth /
        //    read-only seam"). Owner M4b, citing
        //    `SynthInstance.lean:958-968`.
        let saved_cfg = self.cfg;
        self.cfg.transparency = TransparencyMode::Instances;
        self.cfg.fo_approx = true;
        self.cfg.ctx_approx = true;
        self.cfg.const_approx = false;
        self.cfg.univ_approx = false;
        let r = self.synth_instance_body(ty);
        self.cfg = saved_cfg;
        self.rollback(snap);
        r
    }

    fn synth_instance_body(&mut self, ty: ExprId) -> Result<Option<ExprId>, MetaError> {
        // oracle: `main` (:676-690) -- `mkFreshExprMVar type`,
        // `mkTableKey type`, `newSubgoal .. Waiter.root`, then `synth`.
        let ty = self.instantiate_mvars(ty)?;
        let (mvar, _id) = self.mk_aux_mvar(ty)?;
        let key = self.normalize_goal_key(ty)?;
        let mut st = SynthState::default();
        let root_mctx = self.checkpoint();
        self.new_subgoal(&mut st, &root_mctx, key, mvar, Waiter::Root)?;
        // oracle: `synth` (:668-674) -- step until a result appears or
        // `step` reports there is nothing left to do.
        while st.result.is_none() {
            if !self.synth_step(&mut st)? {
                break;
            }
        }
        match st.result.take() {
            None => Ok(None),
            Some(result) => Ok(Some(self.open_abstract_mvars_result(&result)?)),
        }
    }

    /// oracle: `step` (`SynthInstance.lean:660-667`) -- resume before
    /// generate, and `false` when both stacks are empty. `checkSystem`
    /// (:661) becomes `MetaCtx::step`, this crate's deterministic
    /// counter (Global Constraints: a step counter, never
    /// `maxHeartbeats`).
    fn synth_step(&mut self, st: &mut SynthState) -> Result<bool, MetaError> {
        self.step()?;
        st.step += 1;
        if !st.resume_stack.is_empty() {
            self.resume(st)?;
            Ok(true)
        } else if !st.generators.is_empty() {
            self.generate(st)?;
            Ok(true)
        } else {
            Ok(false)
        }
    }

    /// This crate's `withMCtx` (oracle: `Lean.MonadMCtx.withMCtx`, used
    /// pervasively throughout `SynthInstance.lean` to run a step under a
    /// NODE's recorded metavariable context rather than the ambient
    /// one). Restores the caller's own state afterwards, on the error
    /// path too. Note `MetaSnapshot` covers assignments + the postponed
    /// queue, NOT declarations: an mvar declared inside `f` stays
    /// declared afterwards, which is harmless (declarations are
    /// monotone and nothing outside `f` ever names those mvars) and is
    /// the same collapse `metactx.rs::checkpoint`'s own doc records.
    fn with_synth_mctx<R>(
        &mut self,
        snap: &MetaSnapshot,
        f: impl FnOnce(&mut Self) -> Result<R, MetaError>,
    ) -> Result<R, MetaError> {
        let outer = self.checkpoint();
        self.rollback(snap.clone());
        let r = f(self);
        self.rollback(outer);
        r
    }

    // -------------------------------------------------------------------
    // newSubgoal / mkGeneratorNode? / mkTableKeyFor
    // -------------------------------------------------------------------

    /// oracle: `newSubgoal` (`SynthInstance.lean:281-292`) -- build a
    /// generator node for `mvar` under `mctx` and register a brand-new
    /// table entry seeded with exactly `waiter`. When there are no
    /// candidate instances at all, `mkGeneratorNode?` returns `none` and
    /// the oracle registers NOTHING: no generator, and -- deliberately
    /// -- no table entry either, so `waiter` is simply never woken and
    /// that branch of the search dies. Reproduced exactly.
    fn new_subgoal(
        &mut self,
        st: &mut SynthState,
        mctx: &MetaSnapshot,
        key: GoalKey,
        mvar: ExprId,
        waiter: Waiter,
    ) -> Result<(), MetaError> {
        let node = self.with_synth_mctx(mctx, |ctx| ctx.mk_generator_node(key, mvar))?;
        if let Some(node) = node {
            st.generators.push(node);
            st.new_entry(key);
            st.add_waiter(&key, waiter);
        }
        Ok(())
    }

    /// oracle: `mkGeneratorNode?` (`SynthInstance.lean:243-256`).
    fn mk_generator_node(
        &mut self,
        key: GoalKey,
        mvar: ExprId,
    ) -> Result<Option<GeneratorNode>, MetaError> {
        let mvar_type = self.infer_type(mvar)?;
        let mvar_type = self.instantiate_mvars(mvar_type)?;
        let instances = self.get_instances(mvar_type)?;
        if instances.is_empty() {
            return Ok(None);
        }
        let d = self.data(mvar_type);
        Ok(Some(GeneratorNode {
            goal: mvar,
            key,
            // `get_instances` delivers TRY order already (element 0
            // first) -- see `instances.rs`'s "Consumption contract for
            // callers (B5)". `generate` below consumes the front; it
            // must NOT re-reverse.
            remaining: instances,
            mctx: self.checkpoint(),
            type_has_mvars: d.has_expr_mvar() || d.has_level_mvar(),
        }))
    }

    /// oracle: `mkTableKeyFor` (`SynthInstance.lean:298-302`) -- the key
    /// of the mvar's TYPE. `normalize_goal_key` (B4) already runs
    /// `instantiate_mvars` itself, so that step is not repeated here.
    fn mk_table_key_for(&mut self, mvar: ExprId) -> Result<GoalKey, MetaError> {
        let ty = self.infer_type(mvar)?;
        self.normalize_goal_key(ty)
    }

    // -------------------------------------------------------------------
    // generate / tryResolve / getSubgoals
    // -------------------------------------------------------------------

    /// oracle: `generate` (`SynthInstance.lean:625-660`) -- try the next
    /// instance on the generator stack's top node.
    fn generate(&mut self, st: &mut SynthState) -> Result<(), MetaError> {
        let top = st.generators.len() - 1;
        // oracle: `if gNode.currInstanceIdx == 0 then pop` (:627-628) --
        // here, "no candidates left in the front-to-back cursor".
        if st.generators[top].remaining.is_empty() {
            st.generators.pop();
            return Ok(());
        }
        let key = st.generators[top].key;
        let goal = st.generators[top].goal;
        let mctx = st.generators[top].mctx.clone();
        // oracle: the `backward.synthInstance.canonInstances`
        // short-circuit (:636-655). That option's default is `true`
        // (:29-32) and this crate has no `Options` channel to turn it
        // off, so the guard is transcribed unconditionally.
        if !st.generators[top].type_has_mvars {
            if let Some(entry) = st.find_entry(&key) {
                if entry.answers.iter().any(|a| a.result.num_mvars() == 0) {
                    st.generators.pop();
                    return Ok(());
                }
            }
        }
        // oracle: `modifyTop { currInstanceIdx := idx }` (:657) happens
        // BEFORE `tryResolve`, i.e. a candidate is consumed whether or
        // not it resolves. Removing from the front here has the same
        // effect (and cannot leave a failed candidate to be retried).
        let inst = st.generators[top].remaining.remove(0);
        let resolved = self.with_synth_mctx(&mctx, |ctx| ctx.try_resolve(goal, &inst))?;
        if let Some((mctx2, subgoals)) = resolved {
            let Node::MVar { id: Some(id) } = self.node(goal) else {
                // Every `GeneratorNode.goal` is an `Expr.mvar` by
                // construction (`main`/`consume` only ever pass one).
                return Err(MetaError::MVar(
                    "generate: generator goal is not a metavariable reference".into(),
                ));
            };
            self.consume(
                st,
                ConsumerNode {
                    key,
                    mvar: MVarId(id),
                    subgoals,
                    next: 0,
                    mctx: mctx2,
                    size: 0,
                },
            )?;
        }
        Ok(())
    }

    /// oracle: `tryResolve` (`SynthInstance.lean:345-420`). Runs under
    /// the generator node's `mctx` (the caller's `with_synth_mctx`), in
    /// which `mvar` is unassigned.
    ///
    /// **NAMED SEAM -- `forallTelescopeReducing mvarType` (:351), owned
    /// by M4b.** The oracle telescopes a FORALL-shaped synthesis goal
    /// (`∀ xs, C ..`) and solves `C ..` in the extended context, then
    /// re-abstracts with `mkLambdaFVars xs instVal (etaReduce := true)`
    /// (:361); `getSubgoals` correspondingly builds each subgoal mvar at
    /// type `∀ xs, A_i` and applies it to `xs` so `?m xs` stays a
    /// higher-order pattern (:317-330). None of that is transcribed
    /// here: this function handles the `xs = #[]` case only. Rather than
    /// answer `None` for a forall-shaped goal -- a SILENT WRONG ANSWER,
    /// since such goals are genuinely solvable -- it reports
    /// [`MetaError::Unsupported`], which is an unanswered question, not
    /// a negative verdict. Not exercised by either fixture (every goal
    /// in `Instances.olean`/`InstancesCyclic.olean` is a bare class
    /// application).
    ///
    /// This is the correct loud direction, but its BLAST RADIUS is
    /// strictly larger than the oracle's: the oracle handles a
    /// forall-shaped goal wherever it turns up in the search (root goal
    /// or any nested subgoal) and keeps exploring every other branch,
    /// whereas here a single forall-shaped subgoal anywhere in the
    /// search aborts the WHOLE `synth_instance` call via `?`, even if
    /// other candidates or other branches would have answered. M4b
    /// should be aware this seam is not "isolated to the unsupported
    /// goal" the way the oracle's per-branch handling is.
    fn try_resolve(
        &mut self,
        mvar: ExprId,
        inst: &Instance,
    ) -> Result<Option<(MetaSnapshot, Vec<ExprId>)>, MetaError> {
        let mvar_type = self.infer_type(mvar)?;
        let mvar_type = self.instantiate_mvars(mvar_type)?;
        // `forallTelescopeReducing` reduces before looking, so the check
        // has to too -- a goal whose head unfolds to a forall must not
        // slip through as if it were a bare class application.
        let reduced = self.whnf(mvar_type)?;
        if matches!(self.node(reduced), Node::Forall { .. }) {
            return Err(MetaError::Unsupported(
                "synth.rs::try_resolve: forall-shaped synthesis goal needs \
                 forallTelescopeReducing (SynthInstance.lean:351) -- seam owned by M4b"
                    .into(),
            ));
        }
        let (mvars, inst_val, inst_type_body) = self.get_subgoals(inst)?;
        // oracle: `subgoals := inst.synthOrder.map (mvars[·]!)` (:334).
        // `synth_order` is decoded from untrusted `.olean` bytes (Global
        // Constraints), so an out-of-range index is possible in
        // principle; the oracle's `!` would panic. Dropping the
        // candidate instead is incompleteness only -- NAMED SEAM, no
        // real toolchain output can produce it (Lean computed the order
        // against this very declaration's own telescope at
        // registration).
        let mut subgoals = Vec::with_capacity(inst.synth_order.len());
        for &i in &inst.synth_order {
            match mvars.get(i) {
                Some(&m) => subgoals.push(m),
                None => return Ok(None),
            }
        }
        if !self.is_def_eq(mvar_type, inst_type_body)? {
            return Ok(None);
        }
        // oracle: :361-416 -- `mkLambdaFVars xs instVal` is the identity
        // for `xs = #[]`. Then: assign `mvar` DIRECTLY when the goal
        // type is metavariable-free (:412-414, the expensive redundant
        // recheck skipped), else re-unify (:415-416, whose `isDefEqArgs`
        // side effects elaboration depends on).
        let goal_body = self.instantiate_mvars(mvar_type)?;
        if !self.data(goal_body).has_expr_mvar() {
            let Node::MVar { id: Some(id) } = self.node(mvar) else {
                return Err(MetaError::MVar(
                    "try_resolve: goal is not a metavariable reference".into(),
                ));
            };
            self.mctx.assign(MVarId(id), inst_val)?;
        } else if !self.is_def_eq(mvar, inst_val)? {
            return Ok(None);
        }
        Ok(Some((self.checkpoint(), subgoals)))
    }

    /// oracle: `getSubgoals` (`SynthInstance.lean:317-337`), specialized
    /// to the `xs = #[]` case -- see [`MetaCtx::try_resolve`]'s own
    /// doc for the named seam covering `xs != #[]`. With no telescope
    /// variables, `mkForallFVars xs d` is `d`, `mkAppN mvar xs` is
    /// `mvar`, and the whole thing reduces to: peel each `forallE`
    /// binder off the instance's type, mint a fresh metavariable at that
    /// binder's (substituted) type, apply it, and `whnf` whenever the
    /// type stops being a syntactic forall to see whether more binders
    /// hide behind a definition.
    ///
    /// Returns `(all binder mvars in order, instVal, instTypeBody)`.
    #[allow(clippy::type_complexity)]
    fn get_subgoals(
        &mut self,
        inst: &Instance,
    ) -> Result<(Vec<ExprId>, ExprId, ExprId), MetaError> {
        let base = Some(self.view.store);
        // **HARD REQUIREMENT (B3's named seam, closed here).** oracle:
        // `getInstances` (:222-226) hands `tryResolve` a candidate whose
        // `val` is `e.val.updateConst! (← us.mapM (fun _ =>
        // mkFreshLevelMVar))` -- EVERY universe argument replaced by a
        // fresh level metavariable. `Instance::val` as stored by
        // `instances.rs` is `mkConstWithLevelParams`, i.e. still the
        // declaration's own RIGID `Level.param`s, so the refresh has to
        // happen HERE, before anything unifies against it.
        let mut inst_val = self.refresh_instance_levels(inst.val)?;
        let mut inst_type = self.infer_type(inst_val)?;
        let mut mvars: Vec<ExprId> = Vec::new();
        let mut subst: Vec<ExprId> = Vec::new();
        loop {
            self.step()?;
            if let Node::Forall {
                binder_type, body, ..
            } = self.node(inst_type)
            {
                let d = instantiate_rev(self.scratch, base, binder_type, &subst, &mut self.guard)?;
                let (m, _) = self.mk_aux_mvar(d)?;
                subst.push(m);
                inst_val = self.scratch.expr_app(base, inst_val, m)?;
                inst_type = body;
                mvars.push(m);
            } else {
                let t = instantiate_rev(self.scratch, base, inst_type, &subst, &mut self.guard)?;
                inst_type = self.whnf(t)?;
                inst_val = instantiate_rev(self.scratch, base, inst_val, &subst, &mut self.guard)?;
                subst.clear();
                if !matches!(self.node(inst_type), Node::Forall { .. }) {
                    break;
                }
            }
        }
        let inst_val = instantiate_rev(self.scratch, base, inst_val, &subst, &mut self.guard)?;
        let inst_type_body =
            instantiate_rev(self.scratch, base, inst_type, &subst, &mut self.guard)?;
        Ok((mvars, inst_val, inst_type_body))
    }

    /// **HARD REQUIREMENT 1 (universe-level refresh).** oracle:
    /// `getInstances`'s `val := e.val.updateConst! (← us.mapM (fun _ =>
    /// mkFreshLevelMVar))` (`SynthInstance.lean:222-226`). See
    /// `instances.rs`'s module doc ("`val`'s level params are NOT
    /// refreshed here") for why this could not live at
    /// table-construction time (no live `mctx` there to mint into) and
    /// what goes wrong without it: a universe-polymorphic instance's
    /// levels stay RIGID params, so unification against the goal's
    /// levels spuriously fails -- or, in the unlucky param-vs-param
    /// case, "succeeds" for the wrong reason.
    ///
    /// A non-`Const` `val` is returned unchanged: the oracle `panic!`s
    /// there ("global instance is not a constant", :227), and
    /// `InstanceTable::build` only ever stores the `val` of a decoded
    /// `InstanceEntry`, which `addInstance` always builds as a `Const`.
    fn refresh_instance_levels(&mut self, val: ExprId) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        let Node::Const { name, levels } = self.node(val) else {
            return Ok(val);
        };
        let arity = self.scratch.level_list_at(base, levels).len();
        if arity == 0 {
            return Ok(val);
        }
        let mut fresh = Vec::with_capacity(arity);
        for _ in 0..arity {
            fresh.push(self.fresh_level_mvar()?.1);
        }
        let base = Some(self.view.store);
        let levels2 = self.scratch.intern_level_list(base, &fresh)?;
        Ok(self.scratch.expr_const(base, name, levels2)?)
    }

    // -------------------------------------------------------------------
    // consume / addAnswer / mkAnswer / wakeUp
    // -------------------------------------------------------------------

    /// oracle: `consume` (`SynthInstance.lean:534-579`) -- process the
    /// consumer's next subgoal.
    ///
    /// **`consume`'s subgoal RE-FILTER (:535-548).** The oracle rebuilds
    /// `cNode.subgoals` on EVERY entry, dropping any subgoal that has
    /// been assigned incidentally while solving an earlier one (its own
    /// comment cites `@Submodule.setLike`, where a local instance type
    /// depends on other local instances). This crate's `subgoals` is a
    /// FROZEN vec with a monotone `next` cursor rather than a shrinking
    /// list, so the same rule is expressed as a skip-if-assigned scan
    /// from `next` forward, run under the node's own `mctx` (assignment
    /// status is mctx-relative). Subgoals BEFORE `next` were already
    /// consumed, so not rescanning them is not a behavioral difference:
    /// the oracle's filter can only ever drop from the not-yet-processed
    /// tail, since the head it already destructured is gone from its
    /// list too.
    ///
    /// **NAMED SEAM -- `removeUnusedArguments?` (:556-575), owned by
    /// M4b.** When a subgoal's type has an unused leading argument, the
    /// oracle tables the ARGUMENT-STRIPPED goal instead and transports
    /// answers back through a transformer (Tomas Skrivan's
    /// optimization, :481-533). Not transcribed: it only ever applies to
    /// a `hasUnusedArguments` (i.e. FORALL-shaped, :484-486) subgoal
    /// type, which `try_resolve`'s own forall seam already refuses
    /// upstream, so this branch is unreachable here rather than silently
    /// skipped. Its absence is a tabling-granularity/perf difference, not
    /// a different answer.
    fn consume(&mut self, st: &mut SynthState, mut c: ConsumerNode) -> Result<(), MetaError> {
        let mctx = c.mctx.clone();
        let next = self.with_synth_mctx(&mctx, |ctx| {
            let mut next = c.next;
            while next < c.subgoals.len() {
                let assigned = match ctx.node(c.subgoals[next]) {
                    Node::MVar { id: Some(id) } => ctx.mctx.is_assigned(MVarId(id)),
                    // Not an mvar reference at all: nothing left to
                    // solve for it, so treat it as done (the oracle's
                    // `.mvarId!` would panic; every subgoal this driver
                    // builds IS an mvar reference).
                    _ => true,
                };
                if assigned {
                    next += 1;
                } else {
                    break;
                }
            }
            Ok(next)
        })?;
        c.next = next;

        // oracle: `| [] => addAnswer cNode` (:550).
        if c.next >= c.subgoals.len() {
            return self.add_answer(st, c);
        }
        let mvar = c.subgoals[c.next];
        let key = self.with_synth_mctx(&mctx, |ctx| ctx.mk_table_key_for(mvar))?;
        // oracle: `let waiter := Waiter.consumerNode cNode` (:553) --
        // an IMMUTABLE SNAPSHOT of the node as it is right now. Here:
        // push it into the append-only arena and hand out its index.
        let idx = st.push_consumer(c);
        let waiter = Waiter::Consumer(idx);
        match st.find_entry(&key) {
            // oracle: `| some entry => ...` (:576-579) -- schedule a
            // resume for every answer already recorded, and join the
            // waiter list. THIS is what makes a cyclic instance graph
            // terminate: a goal reached a second time never spawns a
            // second generator.
            Some(entry) => {
                let existing: Vec<Answer> = entry.answers.clone();
                for a in existing {
                    st.resume_stack.push((idx, a));
                }
                st.add_waiter(&key, waiter);
                Ok(())
            }
            // oracle: `| none => newSubgoal cNode.mctx key mvar waiter`
            // (:558, the `removeUnusedArguments? = none` branch -- see
            // this function's own seam note).
            None => self.new_subgoal(st, &mctx, key, mvar, waiter),
        }
    }

    /// oracle: `addAnswer` (`SynthInstance.lean:463-478`).
    fn add_answer(&mut self, st: &mut SynthState, c: ConsumerNode) -> Result<(), MetaError> {
        // oracle: `if cNode.size ≥ maxResultSize then <trace only>`
        // (:466-467) -- the answer is simply not recorded.
        if c.size >= MAX_RESULT_SIZE {
            return Ok(());
        }
        let mctx = c.mctx.clone();
        let answer = self.with_synth_mctx(&mctx, |ctx| ctx.mk_answer(&c))?;
        // `SynthState::add_answer` (B4) is `addAnswer`'s table-touching
        // half: `isNewAnswer` dedup, store, and hand back the waiters to
        // wake. Waking them (`wakeUp`, :422-434) is this function's job.
        let woken = st.add_answer(&c.key, answer.clone());
        for w in woken {
            self.wake_up(st, &answer, w);
        }
        Ok(())
    }

    /// oracle: `mkAnswer` (`SynthInstance.lean:453-459`). Runs under
    /// `cNode.mctx` (the caller's `with_synth_mctx`).
    fn mk_answer(&mut self, c: &ConsumerNode) -> Result<Answer, MetaError> {
        let base = Some(self.view.store);
        let mvar_expr = self.scratch.expr_mvar(base, Some(c.mvar.0))?;
        let val = self.instantiate_mvars(mvar_expr)?;
        let result = self.abstract_mvars(val)?;
        let result_type = self.infer_type(result.expr)?;
        Ok(Answer {
            result,
            result_type,
            size: c.size + 1,
        })
    }

    /// oracle: `wakeUp` (`SynthInstance.lean:422-434`). The root arm
    /// accepts an answer only when it abstracted NO expr metavariables
    /// (`answer.result.numMVars == 0`, :428) -- an answer still
    /// parametric in an unsolved metavariable is not a solution to the
    /// original query. Level params are explicitly fine (the oracle's
    /// own comment at :424-427).
    fn wake_up(&mut self, st: &mut SynthState, answer: &Answer, waiter: Waiter) {
        match waiter {
            Waiter::Root => {
                if answer.result.num_mvars() == 0 {
                    st.result = Some(answer.result.clone());
                }
            }
            Waiter::Consumer(idx) => st.resume_stack.push((idx, answer.clone())),
        }
    }

    // -------------------------------------------------------------------
    // resume / tryAnswer
    // -------------------------------------------------------------------

    /// oracle: `resume` (`SynthInstance.lean:635-651`) composed with
    /// `getNextToResume` (:628-632). Note the oracle builds a WHOLE NEW
    /// `ConsumerNode` with `subgoals := rest` (:650) and never mutates
    /// the waited-on snapshot -- reproduced here by pushing a new arena
    /// node (via `consume`) with `next + 1`, leaving `consumers[idx]`
    /// untouched. See [`ConsumerNode`]'s doc for why that discipline is
    /// a correctness requirement.
    fn resume(&mut self, st: &mut SynthState) -> Result<(), MetaError> {
        let Some((idx, answer)) = st.resume_stack.pop() else {
            return Ok(());
        };
        let c = st.consumer(idx).clone();
        if c.next >= c.subgoals.len() {
            // oracle: `| [] => panic! "resume found no remaining
            // subgoals"` (:637). An internal-invariant violation, so a
            // structured caller-bug error rather than a verdict.
            return Err(MetaError::MVar(
                "resume: woken consumer has no remaining subgoals".into(),
            ));
        }
        let mvar = c.subgoals[c.next];
        let Some(mctx2) = self.try_answer(&c.mctx, mvar, &answer)? else {
            return Ok(());
        };
        self.consume(
            st,
            ConsumerNode {
                key: c.key,
                mvar: c.mvar,
                subgoals: c.subgoals,
                next: c.next + 1,
                mctx: mctx2,
                size: c.size + answer.size,
            },
        )
    }

    /// oracle: `tryAnswer` (`SynthInstance.lean:441-449`) -- reopen the
    /// abstracted answer fresh in THIS consumer's metavariable context
    /// and unify it with the subgoal.
    fn try_answer(
        &mut self,
        mctx: &MetaSnapshot,
        mvar: ExprId,
        answer: &Answer,
    ) -> Result<Option<MetaSnapshot>, MetaError> {
        self.with_synth_mctx(mctx, |ctx| {
            let val = ctx.open_abstract_mvars_result(&answer.result)?;
            if ctx.is_def_eq(mvar, val)? {
                Ok(Some(ctx.checkpoint()))
            } else {
                Ok(None)
            }
        })
    }
}

#[cfg(test)]
mod tests {
    use std::sync::atomic::{AtomicU64, Ordering};

    use super::*;
    use crate::test_support::{
        const_named, fresh_mvar, parse_goal, render_expr, render_name, with_cyclic_instances_ctx,
        with_instances_ctx,
    };
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

    // ===================================================================
    // Driver tests (task B5)
    // ===================================================================

    /// B5 Step-1 brief test: the goal `Add N` resolves, and the term the
    /// driver hands back really does inhabit the goal (`infer_type` of it
    /// is defeq the goal — the same property the kernel independently
    /// re-checks).
    #[test]
    fn synthesizes_simple_instance() {
        with_instances_ctx(|ctx| {
            let goal = parse_goal(ctx, "Add N");
            let inst = ctx.synth_instance(goal).unwrap().expect("an instance");
            let ty = ctx.infer_type(inst).unwrap();
            assert!(ctx.is_def_eq(ty, goal).unwrap());
        });
    }

    /// B5 Step-1 brief test: subgoal chaining. `Add (Prod N N)` needs
    /// `instAddProd {a b} [Add a] [Add b] : Add (Prod a b)` plus two
    /// `Add N` subgoals — the first goal in this crate whose answer is
    /// built by a CONSUMER node completing, not by a generator alone.
    ///
    /// Hand-checked against the pinned toolchain: `#synth Add (Prod N N)`
    /// = `@instAddProd N N instAddN instAddN`. `is_def_eq`-to-goal alone
    /// does not pin the TERM (B7's tier-1 gate compares terms, not just
    /// inhabitation), so this also asserts the head constant, the same
    /// idiom as `mul_n_matches_the_oracles_synth_answer_via_the_corrected_
    /// discr_tree_order`.
    #[test]
    fn synthesizes_via_subgoal_chaining() {
        with_instances_ctx(|ctx| {
            let goal = parse_goal(ctx, "Add (Prod N N)");
            let inst = ctx.synth_instance(goal).unwrap().expect("an instance");
            let head = ctx.get_app_fn(inst);
            let Node::Const { name: Some(n), .. } = ctx.node(head) else {
                panic!("synthesized term is not a constant application")
            };
            assert_eq!(
                render_name(ctx, n),
                "instAddProd",
                "matches the oracle's own `#synth Add (Prod N N)` answer's head constant"
            );
            let ty = ctx.infer_type(inst).unwrap();
            assert!(ctx.is_def_eq(ty, goal).unwrap());
        });
    }

    /// B5 Step-1 brief test: `Instances.olean` has no `Mul (Prod _ _)`
    /// instance at all, so this must be a clean `None` — not an error,
    /// not a budget exhaustion.
    #[test]
    fn no_instance_returns_none() {
        with_instances_ctx(|ctx| {
            let goal = parse_goal(ctx, "Mul (Prod N N)");
            assert_eq!(ctx.synth_instance(goal).unwrap(), None);
        });
    }

    /// B5 Step-5 brief test: a CYCLIC instance graph must TERMINATE.
    /// `InstancesCyclic.olean` derives `A a` only from `B a` and `B a`
    /// only from `A a`, with no base instance — a naive
    /// memoized-backtracking resolver diverges; a tabled one terminates
    /// because the second occurrence of the goal `A N` finds the table
    /// entry the first occurrence created and registers a waiter rather
    /// than spawning a second generator.
    ///
    /// The assertion is deliberately STRONGER than the brief's `matches!
    /// (.., Ok(_))`: the step budget is turned DOWN to 50_000 (from
    /// `DEFAULT_STEP_BUDGET`'s 10_000_000) and the result must still be
    /// `Ok(None)`. A budget error is an `Err`, so `Ok(None)` is
    /// positive evidence that termination came from tabling and not from
    /// the budget quietly cutting a real loop short — which is exactly
    /// the failure mode a `matches!(.., Ok(_))`-plus-huge-budget test
    /// cannot distinguish.
    #[test]
    fn cyclic_instances_terminate() {
        with_cyclic_instances_ctx(|ctx| {
            let goal = parse_goal(ctx, "A N");
            // Non-vacuity guard: if `InstancesCyclic.olean`'s instances
            // ever failed to decode, `get_instances` would return an
            // empty candidate list and the `Ok(None)` below would still
            // pass -- silently testing nothing about termination. Pin
            // that the cyclic goal really does have a registered
            // candidate (`instAofB`) before asserting the property that
            // actually matters.
            let insts = ctx.get_instances(goal).unwrap();
            assert_eq!(
                insts.len(),
                1,
                "the fixture must register exactly one candidate (instAofB) for `A N`"
            );
            ctx.set_step_budget(50_000);
            assert_eq!(
                ctx.synth_instance(goal),
                Ok(None),
                "a cyclic instance graph must terminate WITHOUT a budget error"
            );
        });
    }

    /// B5 Step-5 brief test. NOTE (PR-A finding, carried into this
    /// task's own brief): `Instances.olean`'s superclass chain is LINEAR
    /// (`Monoid -> Semigroup -> Mul`), not a multi-parent diamond, so
    /// "diamond" here is the REDUNDANT-PATH sense: `Mul N` is reachable
    /// BOTH directly (`instMulN`) and transitively (`Semigroup.toMul`
    /// applied to `instSemigroupN`, itself reachable again via
    /// `Monoid.toSemigroup`). Two candidates can therefore both produce
    /// an answer, and which one the driver returns must not vary between
    /// runs. Two calls in the SAME `MetaCtx` (so the fresh-mvar
    /// generators have already advanced for the second call) must render
    /// identically.
    #[test]
    fn diamond_resolves_deterministically() {
        with_instances_ctx(|ctx| {
            let goal = parse_goal(ctx, "Mul N");
            let a = ctx.synth_instance(goal).unwrap();
            let b = ctx.synth_instance(goal).unwrap();
            assert!(a.is_some(), "Mul N is reachable via instMulN");
            assert_eq!(
                a.map(|e| render_expr(ctx, e)),
                b.map(|e| render_expr(ctx, e))
            );
        });
    }

    /// **POSITIVE CONFIRMATION that leanr agrees with the oracle's
    /// `#synth`, no longer a divergence characterization.**
    ///
    /// Probed against the pinned toolchain (`#synth Mul N` over
    /// `tests/fixtures/Instances.lean`, v4.33.0-rc1): Lean answers
    /// `instMulN`. This crate now answers `instMulN` too -- the exact
    /// same term, not merely a defeq alternative.
    ///
    /// This test used to pin a CONFIRMED DIVERGENCE (named
    /// `mul_n_picks_the_wrong_candidate_first_because_of_the_discr_tree_order`,
    /// asserting `Semigroup.toMul instSemigroupN`): an earlier version of
    /// `DiscrTree::process` (B1) inverted the oracle's try-order (see
    /// below), so `get_instances` handed this driver
    /// `["Semigroup.toMul", "instMulN"]` where the oracle's own order is
    /// `["instMulN", "Semigroup.toMul"]`, and the driver -- correctly --
    /// returned the first candidate that produced an answer, which was
    /// therefore the wrong TERM (still a genuine inhabitant of the goal,
    /// defeq, never unsound, but a different term from the oracle's).
    ///
    /// Root cause, traced: `getUnify.process`'s non-root arm is
    /// `visitNonStar k args (← visitStar result)`
    /// (`DiscrTree/Main.lean:606`) -- `visitStar` runs FIRST and its
    /// output is the accumulator `visitNonStar` appends to, so the
    /// oracle's result array is `[<star matches>, <specific matches>]`,
    /// which `generate`'s back-to-front read (`SynthInstance.lean:
    /// 630-631`) turns into "specific candidate tried FIRST". B1 has
    /// been corrected (user decision, oracle wins over the plan's
    /// "specific-before-wildcard" wording -- see `discr_tree.rs`'s
    /// module doc, "Superseded plan wording") to match that order, so
    /// `get_instances`'s try-order now agrees with the oracle's, and so
    /// does the synthesized term.
    #[test]
    fn mul_n_matches_the_oracles_synth_answer_via_the_corrected_discr_tree_order() {
        with_instances_ctx(|ctx| {
            let goal = parse_goal(ctx, "Mul N");
            let insts = ctx.get_instances(goal).expect("get_instances");
            let order: Vec<String> = insts
                .iter()
                .map(|i| render_name(ctx, i.global_name.expect("global_name")))
                .collect();
            assert_eq!(
                order,
                vec!["instMulN".to_string(), "Semigroup.toMul".to_string()],
                "corrected try-order, matching the oracle's own getUnify order"
            );

            let inst = ctx.synth_instance(goal).unwrap().expect("an instance");
            let head = ctx.get_app_fn(inst);
            let Node::Const { name: Some(n), .. } = ctx.node(head) else {
                panic!("synthesized term is not a constant application")
            };
            assert_eq!(
                render_name(ctx, n),
                "instMulN",
                "matches the oracle's own `#synth Mul N` answer exactly"
            );
            // A genuine inhabitant of the goal, and now the SAME term
            // the oracle produces, not just a defeq alternative.
            let ty = ctx.infer_type(inst).unwrap();
            assert!(ctx.is_def_eq(ty, goal).unwrap());
        });
    }

    /// Pins the APPEND-ONLY arena discipline (this module's doc, point
    /// (3), and [`ConsumerNode`]'s own doc): advancing a consumer to its
    /// next subgoal must PUSH a new node, never mutate the slot an
    /// outstanding `Waiter::Consumer` points at. `SynthState::consumers`
    /// is module-private with `push_consumer` as its only mutator, so
    /// the compiler already enforces this -- this test pins the INTENT,
    /// so a future refactor that re-exposes the field (or adds an
    /// in-place `advance`) has to delete an explicit assertion rather
    /// than silently reintroduce the wrong-answer bug.
    #[test]
    fn advancing_a_consumer_does_not_disturb_an_outstanding_waiter() {
        with_instances_ctx(|ctx| {
            let goal = parse_goal(ctx, "Add N");
            let mvar = ctx.mk_aux_mvar(goal).expect("mvar").1;
            let node = ConsumerNode {
                key: GoalKey::for_test(7),
                mvar,
                subgoals: vec![goal, goal],
                next: 0,
                mctx: ctx.checkpoint(),
                size: 0,
            };
            let mut st = SynthState::default();
            let waited_on = st.push_consumer(node.clone());
            // "Advance": a NEW node at the next cursor position.
            let advanced = st.push_consumer(ConsumerNode { next: 1, ..node });
            assert_ne!(waited_on, advanced, "advancing must mint a new index");
            assert_eq!(
                st.consumer(waited_on).next,
                0,
                "the waited-on snapshot's cursor must be frozen"
            );
            assert_eq!(st.consumer(advanced).next, 1);
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
