# Synthesis onto real mctx depth — design

Status: approved in brainstorming 2026-10-02 (architectural path).
Follow-up of the macro/binop% P1 slice (`2026-10-01-macro-expansion-binop-design.md`
§ P1 "Not in P1", § Landed P1 open follow-ups) and of synth pi-goals
(`2026-10-02-synth-pi-goals-design.md` § Landed, follow-up "Synthesis onto
real depth").

Pinned oracle: `leanprover/lean4:v4.33.0-rc1`. Every citation below was
opened against that toolchain's `src/lean` while writing this spec.

## Goal

Typeclass synthesis in `leanr_meta` (`synth.rs`) currently runs its search
under a `checkpoint`/`rollback` pair. That pair reproduces the SCOPE of the
oracle's `withNewMCtxDepth` but not its READ-ONLY-ness: the caller's
metavariables stay assignable inside the search. `try_synth_instance`
compensates with a syntactic pre-test (`has_mvar_outside_out_params`: "the
goal mentions an expr mvar outside an out-param position → `Undef`").

Move the search onto the real mctx-depth model that #59 built
(`with_new_mctx_depth`, the read-only arms, `Config::is_def_eq_stuck_ex`), so
that the "ask me again later" answer is detected DYNAMICALLY, as in the
oracle, and the syntactic pre-test can be deleted.

**Success:**
- `synth_instance` runs its search under `with_new_mctx_depth(true, …)` with
  `is_def_eq_stuck_ex = true`.
- The syntactic pre-test is gone; `try_synth_instance` is a one-to-one port
  of `trySynthInstance`.
- Residue 2 (all-polymorphic candidate set) and residue 3 (zero candidates)
  of `try_synth_instance`'s doc are closed, with discriminating evidence.
- Every existing corpus (synth, elab, op) stays green; rows move only toward
  the oracle.

**Scope (the user's choice): core + forced neighbours.** Neighbouring depth
seams (`unstuckMVar`, the DiscrTree stuck cases) enter the slice only if a
corpus row or a discriminating test shows a regression without them (§ Task
4). Everything else stays a named seam.

**Approach (the user's choice): A.** One plan, one PR, four corpus-gated
tasks. The single escape hatch: if `unstuckMVar` is forced, the slice splits
into two PRs (§ Task 4).

## The oracle model

- `synthInstanceCore?` (`SynthInstance.lean:958-1006`) wraps everything in
  `withConfig { isDefEqStuckEx := true, transparency := .instances,
  foApprox := true, ctxApprox := true, constApprox := false,
  univApprox := false }` (`:963-964`). Inside it: `instantiateMVars`
  (`:967`), `preprocess` (`:968`), then
  `withNewMCtxDepth (allowLevelAssignments := true)` (`:978`) around
  `preprocessOutParam` + `SynthInstance.main` (`:979-1002`). After that
  block closes: `applyAbstractResult?` (`:1003`), which runs
  `assignOutParams` at the OUTER depth.
- `withNewMCtxDepthImp` (`Basic.lean:1974-1980`) saves the whole state,
  bumps the depth, clears `postponed`, runs the body, and in `finally`
  restores the saved mctx and `postponed` wholesale.
- `trySynthInstance` (`SynthInstance.lean:1014-1017`): `synthInstance?` with
  `isDefEqStuckExceptionId` caught and mapped to `LOption.undef`. No
  syntactic pre-test.
- `synthPendingImp` (`SynthInstance.lean:1033-…`) catches the same exception
  around its `synthInstance?` call (`:1052`) and treats it as `none`, i.e.
  returns `false`.
- Under `isDefEqStuckEx`, the DiscrTree keys a read-only mvar as `.star`
  (`DiscrTree/Main.lean:397-412`; the comment there explains why: `.other`
  would wrongly report "no candidates"). leanr's `discr_path.rs` stars every
  mvar, so the INDEX already agrees; residue 2/3 behaviour is decided by
  unification alone.
- Stuck throw sites reachable from synthesis: the non-assignable/
  non-assignable branch of `isDefEq` (`ExprDefEq.lean:1952-1956`; ported in
  #59), the level arm (ported in #59), `unstuckMVar`'s fallback
  (`ExprDefEq.lean:1985-2025`, NOT ported) and DiscrTree's
  reducible/matcher/recursor cases (`DiscrTree/Main.lean:359-386`, NOT
  ported).

## Task 1 — the driver change (`synth.rs`)

- `synth_instance_main` additionally sets `self.cfg.is_def_eq_stuck_ex =
  true`. The existing whole-`Config` save/restore restores it.
- `synth_instance_preprocessed` replaces `let snap = self.checkpoint(); …
  self.rollback(snap)` with `self.with_new_mctx_depth(true, |ctx| …)` around
  the `preprocess_out_param` dispatch and `synth_instance_body`. The closure
  returns the `Result<Option<AbstractMVarsResult>, _>`;
  `apply_abstract_result` runs outside it, unchanged. The existing ordering
  rule ("unwrap `abst?` only after the boundary") now holds structurally.
- Effect: the caller's mvars sit at a depth below `mctx.depth()`, so an
  attempt to assign one inside the search hits #59's read-only arms
  (`assign.rs`, `level.rs`) and, under the flag, throws
  `MetaError::IsDefEqStuck`. Outer LEVEL mvars stay assignable
  (`allow_level_assignments = true`). Search-local mvars, including
  `preprocess_out_param`'s replacements, are minted at the new depth and stay
  assignable.
- The `ctx_approx` restriction guard (`expr_mvar_depth(id) !=
  mctx.depth()`, `check_assignment.rs`) becomes exact without code change:
  caller mvars are no longer at the current depth.
- Comment hygiene: the named-SEAM bullets for `isDefEqStuckEx` and
  `withNewMCtxDepth` in `synth_instance_main`, the "WEAKER guard" note, and
  the rollback-stand-in prose in `synth_instance_preprocessed`,
  `synth_instance_body`, `assign_out_params` and `apply_abstract_result` are
  rewritten to describe the real depth boundary.

**Gate:** the pre-test is still in place, so `meta:fast`, the elab corpus and
the op corpus must replay BYTE-IDENTICAL. Any diff is a depth bug, not a
semantics change, and stops the task.

## Task 2 — `synth_pending` catches Stuck (`whnf.rs`)

Once synthesis runs read-only, `synth_instance` can actually return
`Err(IsDefEqStuck)`. Callers:

- `try_synth_instance` (used by `leanr_elab`'s `synthetic/ladder.rs`,
  `builtin/op/to_expr.rs`, and `leanr_meta`'s `coe.rs` ×3) already maps it
  to `LOption::Undef`. No change.
- `synth_pending` (`whnf.rs`, the `with_mvar_context(mvar, |s|
  s.synth_instance(ty))` call) propagates it today; its doc names that as a
  seam. **Change:** match `Err(MetaError::IsDefEqStuck)` onto the same path
  as `Ok(None)` (return `false`, assign nothing). Every other error still
  propagates. This is oracle-faithful (`:1052`), so it does not conflict with
  the crate rule that `is_def_eq` never collapses Stuck to `false`; the seam
  doc is rewritten to say so.

**Test:** a `whnf.rs` unit test with a pending instance mvar whose class goal
mentions an outer, unassigned, non-out-param mvar, and two candidate
instances that pin it differently, so the search hits the read-only arm.
Assert `synth_pending` returns `Ok(false)` and leaves the mvar unassigned.
Mutation "drop the catch" must turn it into `Err(IsDefEqStuck)`. Also look
for an oracle-observable elab row (defeq's `synthPending` meeting a stuck
instance and unification failing cleanly); if none is in reach, the unit
test is the gate and § Landed records that.

## Task 3 — delete the pre-test; close residues 2 and 3

**Change.** `try_synth_instance` becomes `instantiate_mvars` →
`synth_instance` → `Stuck ↦ Undef`. `has_mvar_outside_out_params` is deleted
if nothing else calls it. The residue essay in the doc comment collapses to
a short note: Stuck is detected dynamically by the read-only arms; residues
1–3 are closed.

**Must still postpone, now via a dynamic Stuck** (existing rows/tests; this
is the evidence that the dynamic path REPLACES the syntactic one):
- bare `useWrap` (no expected type): `Wrap ?a` with `instWrapNat` and
  `instWrapUnit`; `Nat =?= ?a` with `?a` read-only throws. Asserted in
  `crates/leanr_elab/tests/synthetic_smoke.rs` (the `elab_and_synthesize
  ("useWrap")` stuck test).
- The `GetElem` worked example: `Get Cell ?i ?e`, `?i` in a non-out
  position.
- `pairW n Nat.zero`'s `CoeT Nat n (Wrapper ?a)`.

**Residue 2 — all-polymorphic candidates (oracle `.some`; leanr `Undef`
today).** New Elab0 support, appended after the existing classes:
`class Any (a : Type)`, `instance instAnyAll {a : Type} : Any a`,
`def useAny {a : Type} [Any a] (x : a) : a`. New row `tc/useAnyHole`:
`useAny _`. `?a` is never pinned; the search assigns only its own
`?b := ?a`; the oracle answers with `?a` left as a natural mvar, which the
dumper keeps (it does not throw). Before the change leanr postpones and then
raises `StuckSyntheticMVar`; after it, leanr matches. **Probe the oracle
first** (`prelude` + `import Elab0`, `LEAN_PATH=tests/fixtures/elab`); if it
throws, pick a variant whose `?a` is fixed only after synthesis, and record
the substitution in § Landed. Adding to Elab0 means `fixtures:regen-elab`
and a recommitted `Elab0.olean`; every existing row must stay byte-identical,
and only the new rows are added. The Elab0 header comment's "must NEVER gain
a default instance" rule extends to `Any`.

**Residue 3 — zero candidates.** Both sides error, so no corpus row is
possible. Meta unit test: `try_synth_instance(NoInst ?a)` returns
`LOption::None` (today `Undef`). Elab test in `synthetic_smoke.rs`:
`useNoInst _` (Elab0's `NoInst` has zero instances; Amendment 1 item 4) changes its error kind
from `StuckSyntheticMVar` to `InstanceSynthesisFailed`, matching the
oracle's "failed to synthesize" (confirm by probe).

**Mutations:**
1. Restore the pre-test → the residue 2 row and the residue 3 tests fail.
2. Drop `is_def_eq_stuck_ex = true` → `useWrap` silently picks a candidate;
   the `useWrap` and `GetElem` rows fail.
3. `allow_level_assignments = false` → expected to fail a
   universe-polymorphic row. If nothing fails, it is a survivor and is
   recorded as such.

## Task 4 — evidence-gated neighbours

Run the full gate (`mise run ci`, which includes fmt/clippy, `meta:fast`,
and the elab/op corpora). Triage each remaining diff or failure one at a
time:

- **`unstuckMVar`** (`ExprDefEq.lean:1985-2025`). Forced if a previously
  green row now errors with Stuck while the oracle answers, AND the stuck
  mvar is a synthetic instance mvar the oracle would have synthesized via
  `synthPending`. If forced, **the slice stops and splits**: tasks 1–3 ship
  as PR 1, and `unstuckMVar` + `isDefEqOnFailure` become PR 2 with its own
  spec addendum.
- **DiscrTree stuck cases** (`DiscrTree/Main.lean:359-386`: reducible,
  matcher or recursor heads with mvars under the flag). Forced only if a row
  shows leanr returning a candidate or `.none` where the oracle reports
  `.undef`. Small, so it lands in this PR.
- **Anything else** is recorded under § Landed as a named seam with an
  owner. No silent widening.

## Testing discipline

- Every task's test gets its mutation actually run (plan briefs have shipped
  non-discriminating tests before).
- Oracle probes use `prelude` + `import Elab0` / `import ElabOp` with
  `LEAN_PATH=tests/fixtures/elab`, never stock Init.
- Every oracle citation in code comments is opened against the pinned
  source before commit; sweep the branch for drift at the end.
- `mise run ci` runs blocking, in-turn, before every push.

## Housekeeping (same PR)

- Correct `2026-10-02-synth-pi-goals-design.md` § Landed (the Prod/Option
  follow-up). On the ElabOp environment the oracle ALSO fails
  `Inhabited (Prod Nat Nat)`, `BEq (Prod Nat Nat)` and `BEq (Option Nat)`:
  `instInhabitedProd`, `instBEqProd` and `Option.instBEq` are not in
  `ElabOp.olean`. The recorded "oracle answers" came from stock Init. Not a
  bug.
- Mark "synthesis onto real depth" closed in the seam/follow-up lists of the
  macro/binop% and synth pi-goals specs, pointing here.

## Not in this slice

- `unstuckMVar` / `isDefEqOnFailure` unless forced (then a second PR, § Task
  4).
- The DiscrTree stuck cases unless forced.
- Nondep R9 (`elim_mvar`'s `newMVarKind`).
- The synthesis cache (`cache.synthInstance`, `:969-976`): leanr has none.
- `checkMayHaveSideEffects` / `check result` (needs a Meta-layer `check`).
- Declarations made inside a depth scope persisting after it with their
  inner depth stamp (#59 open follow-up).

## Plan shape

One plan, one PR, four tasks matching §§ Task 1–4, on branch
`synth-real-depth`. Touches `leanr_meta` (`synth.rs`, `whnf.rs`), the Elab0
fixture and corpus, and `leanr_elab` tests. Merge on green CI per the
standing workflow.

## Amendment 1 (plan-writing, 2026-10-02)

Found while writing the plan; each item stays inside the approved scope
(core + forced neighbours) and changes no decision.

1. **Task 1 also ports four depth-only checks in `synth.rs`.** The oracle
   treats lower-depth mvars as CONSTANTS in `MkTableKey.normLevel`
   (`SynthInstance.lean:120`), `MkTableKey.normExpr` via
   `MVarId.isAssignable` (`:145`; `MetavarContext.lean:483-486`),
   `AbstractMVars` level (`AbstractMVars.lean:56-60`) and expr (`:89-93`).
   leanr's four walks (`KeyNormalizer::norm_level_body`/`norm_expr_body`,
   `MVarAbstractor::level_body`/`expr_body`) collapse that to "every
   declared mvar is current-depth" (the module doc's "flat-depth collapse").
   Under real depth that collapse would abstract a caller's mvar out of an
   answer and `wake_up`'s `num_mvars == 0` root check would reject it. Each
   becomes a real depth comparison against `mctx.depth()`.
2. **Task 1's gate is not fully byte-identical.** Three committed pins
   document the current divergence and flip toward the oracle:
   - `oracle_synth.rs` `SEAM_EXCLUSIONS` entry `mvarGoal/synth/0`
     (`OfN ?n N`; oracle `some (instOfNN ?n)`) closes: the entry and its
     sibling `seam_excluded_mvar_goal_is_incompleteness_not_an_error` are
     deleted, and the gate's `compared` count goes 37 → 38.
   - `exc_record_stuck_synth_0_pins_leanrs_current_divergent_answer`
     (`Add ?a`; oracle throws `isDefEqStuck`) flips from
     `Ok(Some(instAddN))` to `Err(IsDefEqStuck)`, as its own failure
     message instructs.
   - `synth.rs`'s `pi_goal_with_mvar_body_does_not_error` (`N → Add ?a`)
     flips from answering `fun _ => instAddN` to `Err(IsDefEqStuck)`, with
     `?a` left unassigned.
   Everything else stays byte-identical.
3. **The elab/op byte-identical gate runs at the end of Task 2, not
   Task 1.** `synth_pending` calls `synth_instance` directly, so between
   the two tasks an elab row could surface `Err(IsDefEqStuck)` that Task 2's
   catch removes. Task 1 gates on `leanr_meta` alone.
4. **Residue 3 gets an oracle row after all, at the meta layer.** The
   elab-level "both sides error" argument holds, but `dump_synth.lean`
   calls `synthInstance?`, which answers `NoInst ?a` cleanly with `none`.
   Task 3 adds the Synth0 query `noInstMVar/synth/0` (no fixture change:
   Synth0 already has the zero-instance `NoInst`) and an `oracle_synth.rs`
   test that runs `try_synth_instance` on it and expects `LOption::None`.
   The elab-level test stays, but its source is `useNoInst _`, not bare
   `useNoInst`: a bare head never reaches instance synthesis (probe: `#check
   useNoInst` prints the signature). Probed against the pinned oracle on
   Elab0: `useNoInst _` → "failed to synthesize instance of type class
   NoInst ?m"; `useWrap _` stays postponed; and residue 2's `useAny _` →
   `@useAny ?m.1 (@instAnyAll ?m.1) ?m.3`.

## Landed

Commits (`git log --oneline main..HEAD`, before this docs commit):

```
2a4c0f0 leanr_elab: docs no longer describe the deleted syntactic pre-test
dfe88b6 leanr_meta: try_synth_instance reads IsDefEqStuck dynamically; drop the syntactic pre-test
fe793b6 leanr_meta: restore depth-guard test doc; reorder synth_pending tests
bcaa479 leanr_meta: synth_pending catches IsDefEqStuck (SynthInstance.lean:1052)
91c912d leanr_meta: fix stale try_synth_instance doc after real depth
44b300b leanr_meta: run typeclass synthesis under real mctx depth + isDefEqStuckEx
e68f4b3 docs: synth-real-depth plan; spec amendment 1 (depth-only walks, pins, residue-3 oracle row)
6007403 docs: synthesis onto real mctx depth — design spec
```

**Mutations (all reverted).**
- Task 1: (a) checkpoint/rollback instead of the depth block, killed
  (`pi_goal_with_mvar_body_is_stuck`, `exc_record_stuck_synth_0_is_stuck_in_leanr_too`,
  `oracle_synth_gate`); (b) drop `is_def_eq_stuck_ex = true`, killed; (c)
  `decl(mid).is_some()` in `norm_expr`, killed; (d) drop the level depth
  check in `norm_level`, killed; (e), (f) drop the level / expr depth check
  in `MVarAbstractor`, killed; (h1), (h2) compare `level_assign_depth()`,
  killed; **(g) `with_new_mctx_depth(false, ..)` SURVIVED**: no test or
  corpus row distinguishes `allowLevelAssignments` true from false (open
  seam).
- Task 2: (a) drop `| Err(IsDefEqStuck)` in `synth_pending_body`, killed
  (`synth_pending_treats_a_stuck_search_as_no_progress`); (b) widen to
  `Err(_) => Ok(false)`, killed (`synth_pending_still_propagates_a_budget_error`).
  The budget error is raised inside the nested `synth_instance` search;
  `synth_pending` has no `step()` of its own.
- Task 3: (1) restore the syntactic pre-test, killed (3 tests:
  `no_inst_mvar_goal_is_none_not_undef`, `oracle_elab_gate` `tc/useAnyHole`,
  `hole_against_a_class_without_instances_is_a_synthesis_failure`); (2)
  `is_def_eq_stuck_ex = false` in synthesis, killed (26 tests); (3)
  `IsDefEqStuck` mapped to `LOption::None` in `try_synth_instance`, killed
  (25 tests).

**Citations corrected.** `DiscrTree/Main.lean:395-411` is `:397-412`
(`if cfg.isDefEqStuckEx` at 397, `return (.star, #[])` at 412); fixed in
`synth.rs` (Task 1) and in this spec's § The oracle model (final sweep).
Also fixed in the final sweep: `level.rs`'s claim that synthesis's
`SynthInstance.lean:963` setting "stays a follow-up", and `synth.rs`'s
comment that `with_new_mctx_depth` restores the caller's mctx "wholesale"
(it restores assignments and `postponed`; declarations made inside persist,
`metactx.rs` ~537-540).

**Triage outcome.** Full `mise run ci` was green with Tasks 1-3 in
place. No neighbour was forced: neither `unstuckMVar` nor the DiscrTree
stuck cases. Two smoke tests moved from `StuckCoercion` to `TypeMismatch`
(`anon_ctor_smoke.rs` `eq_counts_fields_after_its_promoted_parameters`;
`binder_smoke.rs` `fun_more_binders_than_expected_pi_levels_is_a_type_mismatch`,
renamed from `..._is_a_stuck_coercion`). These are not forced neighbours:
the oracle probe on Elab0 shows `trySynthInstance` returns `.none` for the
`CoeT` goal, so `mkCoe` fails immediately (`TermElabM.lean:1307`, `:1322`);
the old expectations encoded the pre-test's over-approximation.

**Corpus counts.** synth compared 37 -> 39 (Task 1: 37 -> 38 by closing the
`mvarGoal/synth/0` seam exclusion; Task 3: 38 -> 39 with
`noInstMVar/synth/0`); elab floor 345 -> 346 (`tc/useAnyHole`); op floor
99 unchanged.

**Open seams.**
- `unstuckMVar` + `isDefEqOnFailure` (`ExprDefEq.lean:1985-2025`), not ported.
- DiscrTree stuck cases (`DiscrTree/Main.lean:359-386`), not ported.
- Nondep R9.
- The synthesis cache.
- `checkMayHaveSideEffects` / `check result`.
- Inner-scope declarations persisting with an inner depth stamp
  (`with_new_mctx_depth` restores assignments and `postponed` only).
- `allowLevelAssignments` true/false is not test-distinguished (mutation (g)).
