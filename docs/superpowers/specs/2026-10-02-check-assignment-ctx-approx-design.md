# `checkAssignment` with `isSubPrefixOf` and `ctxApprox` — design spec

## Where this sits

The macro/binop% slice closed in #61. Its spec,
`2026-10-01-macro-expansion-binop-design.md` § Landed › P3, ranks one
open follow-up as TOP PRIORITY: `assign.rs` `mk_lambda_over_fvars`
abstracts with raw `abstract_fvars` and has no `elimMVarDeps`. As a
result, plain `fun (n : Nat) (x : F n) => x + F.mk _` returns a silently
wrong `Ok`. That section also recorded a reverted experiment: routing
through `MetaCtx::mk_lambda` fixes the binder repros, but regresses
`op/postponed-binop-operand` with `DepthBudgetExhausted`. A separate
follow-up recorded `(fun a => LT.lt a 2) z0` hitting
`DepthBudgetExhausted` on main, with the note "likely the same
leanr_meta slice, not bisected".

The user scoped this slice to both items (option A of the brainstorm).
A probe, recorded below, found that the two items share one root cause,
and that cause is not elimMVarDeps.

Pinned oracle: `leanprover/lean4:v4.33.0-rc1`, and the pin does not
change. Every citation below was opened against that toolchain's
`src/lean` while writing this spec. Several existing leanr doc comments
cite older line numbers, for example `check_assignment_scope`'s
`ExprDefEq.lean:1083-1130` and `:864-1030`. The plan corrects every
cite it touches.

## Evidence (probe, 2026-10-02)

The probe ran in a throwaway worktree, which has since been deleted.
Nothing from it was kept. It used three instruments: a backtrace taken
where `MetaCtx::guarded` first returns `DepthBudgetExhausted`, a dump of
each metavariable `elim_mvar` visits once recursion is deep, and a
compact backtrace recorded at every `MetavarContext::assign`.

**Both depth failures are the same infinite cycle**, entirely inside
one `elim_mvar_deps` call:
`elim_mvar → mk_aux_mvar_type_with → abstract_range_aux → visit →
elim_app → elim → elim_mvar`, repeated about 333k–1M times.

- `op/postponed-binop-operand`, `(fun x => x.1 + 0) (PProd.mk 1 2)`,
  with the `mk_lambda` swap: `x : ?T`, `?T := PProd ?9 ?10`, and
  `?9 := ?11 := ?15`. `?11` has an empty context (it is the type of the
  literal `1` in `PProd.mk 1 2`). `?15` sees `x` (it was minted inside
  the `fun`). `?11 := ?15` was made by
  `is_def_eq_mvar_mvar → process_assignment → check_types_and_assign`.
- `(fun a => LT.lt a 2) z0` on main, with no swap: the binder type
  `?0` (empty context) `:= ?3` (the type of `2`, which sees `a`). It
  was assigned through the same path. It loops in `elab_fun`'s own
  `mk_lambda`, which already runs elimMVarDeps.

These assignments leave the metavariable state cyclic. `?inner`'s
context contains `x`, and `x`'s type instantiates to a term that
contains `?inner`. To eliminate `?inner`, `elim_mvar` reverts `x`,
which means abstracting `x`'s type, which reaches `?inner` again.

**The cause is the scope seam in `check_assignment_scope`'s `MVar` arm**
(`assign.rs`): `SEAM: isSubPrefixOf … every declared mvar is treated as
mutually visible`. The oracle's `isDefEqQuickMVarMVar`
(`ExprDefEq.lean:1963-1976`) makes the same first attempt
(`processAssignment t s`) as leanr's `is_def_eq_mvar_mvar`, but the
oracle's `checkAssignment` then catches the problem:

- `CheckAssignmentQuick.check`'s mvar arm (`:1075`):
  `!mvarDecl'.lctx.isSubPrefixOf mvarDecl.lctx fvars` → `false`, which
  falls through to the slow path (`:1164-1168`).
- `CheckAssignment.checkMVar` (`:880-938`): the inner mvar's context is
  not a sub-prefix (`:897`), the depths are equal, the mvar is not
  syntheticOpaque, `ctxApprox` is on (`setElabConfig`, live since #57),
  and the outer context IS a sub-prefix of the inner one (`:905`). So it
  mints `?aux` in the inner context with `x` erased (`:936`), assigns
  `?inner := ?aux`, and the outer mvar gets `?aux`. The result is
  well-scoped, so there is no cycle.

leanr ports neither the real sub-prefix test nor the slow path. The
setElabConfig spec deferred `checkAssignmentAux` until "a corpus record
depends on `ctxApprox`". The six repros below are those records.

**Measured outcomes** (probe build, ElabOp fixture):

| source | main | with the `mk_lambda` swap only |
|---|---|---|
| `(fun x => x.1 + 0) (PProd.mk 1 2)` | Ok | `DepthBudgetExhausted` |
| `(fun a => LT.lt a 2) z0` | `DepthBudgetExhausted` | same |
| `(fun a => a + 2) z0` | `DepthBudgetExhausted` | same |
| `(fun a => BEq.beq a 2) z0` | `DepthBudgetExhausted` | same |
| `fun (n : Nat) (x : F n) => x + F.mk _` | Ok, **wrong term** | Ok |
| `fun (n : Nat) (x : F n) (z : Z) => x + F.mk _ + z` | `InstanceSynthesisFailed` | Ok |
| `fun (n : Nat) => @HAdd.hAdd _ _ _ _ (V.mk : V n) (V.mk : V _)` | `StuckSyntheticMVar` | Ok |

The oracle accepts all seven (macro/binop% spec § Landed › P3). The
swap's `Ok`s were not compared against oracle terms in the probe. The
corpus rows below do that.

## Design

### Structure

**New module `crates/leanr_meta/src/check_assignment.rs`.** `assign.rs`
is about 2,800 lines, so this follows the precedent `mk_binding.rs` set.
It ports the oracle's two namespaces one-to-one:

| oracle | leanr |
|---|---|
| `LocalContext.isSubPrefixOf` / `isSubPrefixOfAux` (`LocalContext.lean:534-552`) | `LocalCtxSnapshot::is_sub_prefix_of(&self, other: &LocalCtxSnapshot, except_fvars: &[ExprId]) -> bool`, walking `local_names` |
| `CheckAssignmentQuick.check` (`ExprDefEq.lean:1039-1086`) | `check_assignment_scope` / `_body`, moved here from `assign.rs` |
| `CheckAssignment.check` / `checkFVar` / `checkMVar` / `checkApp` / `assignToConstFun` / `checkAssignmentAux` (`:803-1037`) | `check_assignment_aux(mvar_id, fvars, has_ctx_locals, v) -> Result<Option<ExprId>, MetaError>` and its private helpers |

`is_sub_prefix_of` is an ordered-subsequence test. The oracle walks
`PArray (Option LocalDecl)`, which may contain holes. `local_names` is a
compacted positional `Vec` (the order is preserved, and erased entries
are removed). Holes never match, so the test gives the same answer on
both representations. leanr_kernel is untouched.

### The quick check (`CheckAssignmentQuick.check`)

The `MVar` arm becomes the oracle's six fallthroughs (`:1070-1077`), in
order. Each returns `false`, meaning "use the slow path", not "reject":

1. assigned;
2. `id == mvar_id`;
3. undeclared;
4. `has_ctx_locals`;
5. `!decl'.lctx.is_sub_prefix_of(decl.lctx, fvars)`;
6. delayed-assigned.

(1)–(3) and (6) are not new conditions, but leanr either treats them
differently today or does not distinguish them. (5) is the seam this
slice closes. The `FVar` arm already matches `:1059-1069`, and its
genuine-let `false` stops being a final refusal because the slow path's
`checkFVar` now follows the value.

The oracle keeps a pointer-set `visited`. leanr's `ExprId`s are
hash-consed, so a `HashSet<ExprId>` is the faithful analogue. It is
added only if a test shows the walk repeats subterms. It is not needed
for correctness.

### The slow path (`CheckAssignment`)

`check_assignment_aux` returns `Ok(None)` for the oracle's two internal
exception ids, `outOfScopeExceptionId` and `checkAssignmentExceptionId`
(`run`, `:840-847`). A private two-variant enum carries them inside the
module, and they never surface as `MetaError`. A real `MetaError`
(budget, depth, malformed term) propagates. The cache is a
`HashMap<ExprId, ExprId>` scoped to one `check_assignment_aux` call,
matching `checkCache` under `run`'s fresh state.

- **`check`** (`:987-1035`): return early when there is no mvar and no
  fvar, then a structural rebuild per node kind. `app` goes to
  `check_app`. On either internal failure, if `e` is a head-beta target,
  it retries `check_app(head_beta(e))` (`:1004-1021`). The oracle's own
  commented-out `whnfR` fallback (`:1024-1034`) is not ported.
- **`check_fvar`** (`:851-878`): in the mvar's context → keep. A
  genuine let in the ambient context (`nondep := false`) → `check` its
  value (the rescue). Otherwise, in `fvars` → keep, else out-of-scope.
  A `have` takes the `fvars` test, as the oracle's comment requires.
- **`check_mvar`** (`:880-938`): `id == mvar_id` → failure. Assigned →
  `check` the value. `has_ctx_locals` → failure (`:890`).
  Delayed-assigned → occurs-check `mvar_id` against `mvar_id_pending`.
  Sub-prefix with `fvars` subtracted → keep. A depth mismatch (P1's
  `expr_mvar_depth` vs the mctx depth) or syntheticOpaque → failure.
  `!(ctx_approx && decl.lctx.is_sub_prefix_of(inner.lctx, []))` →
  failure. Otherwise build `to_erase` with the oracle's fold
  (`:920-930`), including the "an `fvars` entry depending on an erased
  one is erased too" rule via `local_decl_depends_on`. Erase from the
  inner context, filter the local instances, `check` the inner type,
  mint `?aux` with `mk_aux_mvar_at`, assign `inner := ?aux`, and return
  `?aux`.
- **`check_app`** (`:958-985`): if the head is an mvar, `ctx_approx` is
  on, and every argument is an fvar, `check` the head, then the
  arguments. On out-of-scope, unless the head is no longer an mvar or
  is delayed-assigned: `check` the inferred type, mint `?new` in the
  ASSIGNED mvar's context, and `assign_to_const_fun`. Otherwise check
  the head and the arguments structurally.
- **`assign_to_const_fun`** (`:946-952`): `forall_bounded_telescope`,
  then `mk_lambda_fvars_with_let_deps`, then a recursive
  `check_assignment_aux(mvar, [], false, v)`, then
  `check_types_and_assign`.

### The driver

`check_assignment` stays in `assign.rs` and follows `:1151-1172`
exactly:

1. Occurs-check every fvar's type.
2. If `v` has no mvar and no fvar, return it.
3. Compute `has_ctx_locals = fvars.any(in mvar's own lctx)` (`:1161`).
   Today leanr derives this from the quasi-pattern path; it becomes the
   oracle's direct computation.
4. If the quick check passes, use `v`. Otherwise use
   `check_assignment_aux(instantiate_mvars(v))`, or `None` if that
   fails.
5. Run `type_occurs_check` on the RESULT.

The rewritten term is what the callers assign. This is the reason the
earlier "graft the rescue into the bool check" attempt was ill-formed,
as `check_assignment_scope_body`'s doc comment records: the oracle
assigns the rewritten term, never the original `v`.

### The elimMVarDeps swap

`mk_lambda_fvars_with_let_deps` calls `MetaCtx::mk_lambda`
(`mk_binding` → `elim_mvar_deps` + `abstract_range`), and
`mk_lambda_over_fvars` is deleted. Its doc comment says it exists only
because `leanr_kernel::subst::mk_lambda` is not exported, and
`MetaCtx::mk_lambda` now fills that role. The let-guard and its
`hasLetDeclsInBetween` seam are unchanged.

### Side effects and rollback

`check_mvar`'s `inner := ?aux` and `assign_to_const_fun` assign during
a check, as the oracle does. `is_def_eq_mvar_mvar` already wraps its
first direction in `checkpoint()`/`rollback`, which is the oracle's
`checkpointDefEq`, so a failed direction undoes them. The aux
DECLARATIONS outlive a rollback. That is the known P1 item ("inner
decls persist after rollback"). They are unreferenced and harmless, and
stay out of scope.

## Seams closed

- `check_assignment_scope`'s `isSubPrefixOf` tier-1 seam.
- The "`ctxApprox` is ON during elaboration … and still inert here"
  seam.
- The genuine-let `checkFVar` rescue seam. Its pin,
  `check_fvar_seam_shows_only_with_zeta_delta_off`, flips: both halves
  of the loop expect `true` and `?m := N.zero`, which is the measured
  oracle answer recorded in that test's own doc comment. The test is
  renamed to state agreement.
- The elimMVarDeps gap in `mk_lambda_fvars_with_let_deps` (macro/binop%
  § Landed › P3, TOP PRIORITY).
- The `(fun a => LT.lt a 2) z0` family (same section).

## Testing

**Oracle-differential corpus** (`tests/fixtures/elab/dump_elab.lean`
→ `op-queries.jsonl`, regenerated with `mise run fixtures:regen`). Row
ids are provisional. `CORPUS_FLOOR` in `oracle_op.rs` rises to match.

| row | source | discriminates |
|---|---|---|
| `op/depth`, `op/depth-mid`, `op/stuck` | restored to their original `fun`-binder spellings (P3's R2 respelled them over `vx`/`k0`/`fx`/`z0`) | elimMVarDeps in `process_assignment` |
| `op/binder-F-hole` | `fun (n : Nat) (x : F n) => x + F.mk _` | the silent wrong `Ok` |
| `op/binder-F-hole-chain` | `fun (n : Nat) (x : F n) (z : Z) => x + F.mk _ + z` | `InstanceSynthesisFailed` |
| `meta/at-hadd-V` | `fun (n : Nat) => @HAdd.hAdd _ _ _ _ (V.mk : V n) (V.mk : V _)` | `StuckSyntheticMVar` |
| `meta/beta-lt`, `meta/beta-add`, `meta/beta-beq` | `(fun a => LT.lt a 2) z0`, `(fun a => a + 2) z0`, `(fun a => BEq.beq a 2) z0` | the ill-scoped mvar-to-mvar cycle |
| `op/rel-no-default` | back to `x < 2` if P3 avoided that spelling for this reason (the plan checks P3's record) | same |

`op/postponed-binop-operand` is unchanged and must stay green. It is
the row that drives `check_mvar`'s restriction.

**`check_app` / `assign_to_const_fun`**: none of the repros reaches
this path (`?f x` with `x` out of scope). The plan probes the oracle
for a source term whose answer depends on it. If one exists, it becomes
a corpus row. If not, the arm gets unit tests and a written note that
no differential record exists, the posture setElabConfig took.

**Unit tests** (`check_assignment.rs`, `test_support` fixtures):

- `is_sub_prefix_of`: extra declarations in the larger context,
  `except_fvars` subtraction, order sensitivity, empty contexts, and
  equal contexts.
- Quick-check `MVar` arm: each fallthrough, (1)–(6).
- `check_mvar`: the restriction erases `x`; a dependent `fvars` entry
  is erased too; local instances are filtered; `inner` is assigned
  `?aux`. Refused for syntheticOpaque, for a depth mismatch, with
  `ctx_approx` off, and with `has_ctx_locals`.
- `check_fvar`'s let rescue, a `have` not rescued, and out-of-scope.
- The head-beta retry in `check`.
- Driver: the RETURNED term is the rewritten one, and
  `type_occurs_check` runs on it.
- Rollback: a failed first direction in `is_def_eq_mvar_mvar` leaves
  no restriction assignment behind.
- The flipped `check_fvar` pin.

**Mutations.** Plan briefs have shipped non-discriminating tests
before, so each task names its mutations, runs them, and records which
named test kills each one. The minimum set:

- `is_sub_prefix_of` always `true`;
- `except_fvars` ignored;
- quick-check arm (5) removed;
- the driver never calls the slow path;
- the driver assigns the original `v` instead of the rewritten term;
- `check_mvar` skips `inner := ?aux`;
- the `to_erase` dependent-entry rule removed;
- `ctx_approx` gate removed;
- the head-beta retry removed;
- `check_fvar`'s let rescue removed;
- the `mk_lambda` swap reverted.

P3's T3 mutations (d) and (h), which survived as unobservable, are
re-run against the restored binder rows.

**Regression gate**: the full `mise run ci`, including every elab
corpus (`oracle_elab`, `oracle_op`, `seam_audit`), not just op. The
stricter quick check touches every assignment that mentions an mvar.

## Risks

1. **Changed answers anywhere.** The quick check gets strictly
   stricter, so assignments that passed by the permissive seam now
   take the slow path and may be restricted, rewritten or rejected.
   Every corpus is a gate, and a changed answer is diagnosed against
   the oracle, never re-pinned to match leanr.
2. **Rollback completeness.** See § Side effects. The rollback unit
   test is the guard.
3. **`has_ctx_locals`.** The oracle's slow path refuses every mvar when
   it is set (`:890`), so quasi-pattern behaviour can become stricter.
   The existing quasi-pattern tests gate it, plus a named refusal test.
4. **Cost.** The slow path runs only when the quick check fails, and
   it is cached per call. The ElabOp replay time (about 5.4 s in debug)
   is the smoke check.

## Out of scope

- The synth pi-goal gap (`SynthInstance.lean:740-742`). The suffix's
  `instance : BEq Bool` stays.
- The `hasLetDeclsInBetween`/`addLetDeps` seam in
  `mk_lambda_fvars_with_let_deps`.
- The oracle's commented-out `whnfR` fallback in `check`.
- Aux declarations that outlive a rollback (P1's open item).
- leanr_kernel: no change.

## Plan shape

One plan and one PR, with four tasks:

- **T1** — `is_sub_prefix_of` and the slow `check_assignment_aux`
  family in `check_assignment.rs`, unit-tested and not yet wired in.
- **T2** — wire the driver and make the quick check's `MVar` arm real.
  Behaviour changes here, so every corpus must stay green and the
  `check_fvar` pin flips.
- **T3** — the `mk_lambda` swap and the rollback test.
- **T4** — the corpus rows and restorations, the `check_app` oracle
  probe, P3 T3 (d)/(h), and the spec § Landed close-out (this spec and
  macro/binop% § Landed › P3).

T1 comes before T2 so that the stricter quick check never ships
without the slow path behind it.

## Landed

PR #62 (branch `check-assignment-ctx-approx`), four tasks:
T1 7959a10, T2 ddb6840, T3 eee69ad + 62262c2, T4 (corpus rows and this
close-out). Oracle pin unchanged (`leanprover/lean4:v4.33.0-rc1`).

**Corpus** (`op-queries.jsonl`, `CORPUS_FLOOR` 81 -> 90): `op/depth`,
`op/depth-mid`, `op/stuck` restored to their `fun`-binder spellings; the
closed spellings are kept as `op/depth-closed`, `op/depth-mid-closed`,
`op/stuck-closed` (records byte-identical to the old ones apart from the
id). New: `op/binder-F-hole`, `meta/at-hadd-V`, `meta/beta-lt`,
`meta/beta-add`, `meta/beta-beq`, `op/rel-lt-beta`. The oracle accepts all
of them (no `sorryAx`), and leanr matches every record. No pre-existing
record changed in any task.

Mutations (each applied, run, reverted):
- T1: (a) `is_sub_prefix_of` always true and (b) `except` ignored:
  `is_sub_prefix_of_is_an_ordered_subsequence_test`. (c) no
  `inner := ?aux`: `check_mvar_restricts_an_inner_mvar_under_ctx_approx`.
  (d) the dependent-`fvars` rule removed:
  `check_mvar_erases_a_dependent_fvars_entry`. (e) `ctx_approx` gate
  removed: `check_mvar_refuses_without_ctx_approx`. (f) depth comparison
  removed: `check_mvar_refuses_synthetic_opaque_and_other_depth`. (g)
  head-beta retry removed: `check_retries_a_head_beta_target`. (h) let
  rescue removed: `check_fvar_follows_lets_not_haves`. (i) `rescuable`
  always false: `check_app_rescues_an_out_of_scope_mvar_app`. (j)
  `has_ctx_locals` return removed: `check_mvar_refuses_under_has_ctx_locals`.
  All KILLED.
- T2: (a) driver assigns the original `v`, and (d) driver never calls the
  slow path: `driver_returns_the_slow_path_rewrite`,
  `check_fvar_follows_a_genuine_let_value_in_both_zeta_modes`. (b) no
  rollback in `is_def_eq_mvar_mvar`:
  `failed_first_direction_rolls_back_the_restriction`. (c) quick-check arm
  (5) dropped and (e) delayed test -> `true`:
  `quick_check_mvar_arm_falls_through_on_each_condition`. (f) `&except` ->
  `&[]` in `check_mvar`: `check_mvar_subtracts_fvars_before_the_sub_prefix_test`.
  (g) "keep what the outer ctx has" branch deleted:
  `check_mvar_restriction_keeps_what_the_outer_ctx_has`. All KILLED. The
  `check_fvar` pin flipped as planned (now
  `check_fvar_follows_a_genuine_let_value_in_both_zeta_modes`). Those two
  killers of (f) and (g) were added by the controller during T2 review: the
  brief's tests put the assigned mvar in an EMPTY ctx, where neither
  mutation is observable. Both put the assigned `?o` in a non-empty ctx
  `{a}`. `check_mvar_subtracts_fvars_before_the_sub_prefix_test` has the
  inner mvar in `{a, y}` with `fvars = [y]`, which is a sub-prefix only
  once `y` is subtracted, so the inner mvar stays unassigned.
  `check_mvar_restriction_keeps_what_the_outer_ctx_has` has the inner mvar
  in `{a, x}`, and the restriction keeps `a` and drops `x`.
- T3: (a) swap reverted to raw abstraction: KILLED by
  `process_assignment_eliminates_mvar_deps_on_the_pattern_fvars`. (b)
  quick-check arm (5) skipped with the swap in place: KILLED by
  `oracle_op_gate` (`op/postponed-binop-operand`, `DepthBudgetExhausted`,
  as the § Evidence probe predicted) plus two unit tests.
- T4, P3's survivors re-run against the restored binder rows: P3 T3 (d)
  (drop the final `is_def_eq_guarded(ty, max)` in `to_expr`) still
  SURVIVES the whole op corpus, binder rows included: with no unknown leaf
  every leaf type is already `max`, so the homogeneous instance's
  out-param already equals `max`. P3 T3 (h) (`result_is_out_param_support:
  true` in `apply_op`) is now KILLED, by `meta/beta-add` (`TypeMismatch`);
  whether the restored binder rows alone kill it was not separately
  verified.

T3 test variant: the elimMVarDeps unit test uses a syntheticOpaque `?i`
(a natural `?i` succeeds via `?i := ?m x` and never reaches the swap). It
asserts that `?m`'s value, after stripping leading lambdas, has a fresh
`?i'` head delay-assigned with fvars `[x]` and pending `?i`, so it does not
depend on the binder shape (see the eta seam below).

**`checkApp` / `assignToConstFun` coverage.** Mutation (i) (`rescuable`
always false) survives `oracle_op`, `oracle_elab` and `seam_audit`. The
oracle was probed against ElabOp, with each query run twice: as the dumper
runs it, and with the `elabTerm` + `synthesizeSyntheticMVarsNoPostponing`
block wrapped in `withConfig (fun c => { c with ctxApprox := false })`
inside `.run'`. The queries were the plan's candidates c1-c4, the controls
`op/binder-F-hole`, `op/depth`, `meta/beta-lt`,
`op/postponed-binop-operand` and `meta/at-hadd-V` (rows that take this
slice's `checkMVar` restriction), and four extra guesses:
`fun (n : Nat) (x : V n) => (V.mk : V _) + x`,
`(fun (g : Nat → Nat) => g 0) (fun k => k + 1)`,
`fun (a : Nat) => (fun x => x + a) 1` and
`fun (n : Nat) (x : F n) => (F.mk _ : F _) + x`.

Two results:
- The off-switch takes effect. `(← getConfig).ctxApprox` was read back
  inside the block, both after `elabTerm` and after the synthesis fixpoint.
  It was `false` for every query in the off-run and `true` in the on-run.
- The answers do not change. The on and off outputs are byte-identical for
  every query, controls included, and neither run elaborated with errors.
  Not even the controls are `ctxApprox`-dependent at the oracle's level.
  The likely reason, not verified: when the restriction is refused,
  `isDefEqQuickMVarMVar` succeeds with the opposite assignment direction.
  Also, instance synthesis forces `ctxApprox := true` whatever the
  setting (`SynthInstance.lean:964`).

So `checkApp`/`assignToConstFun` has unit coverage
(`check_app_rescues_an_out_of_scope_mvar_app`) and no differential record.
Mutation (i) survives the corpus. Candidates tried: c1-c4, plus the
controls and the four extra queries above.

Deviations from this spec:
- `is_sub_prefix_of` takes `except: &[NameId]`, not `&[ExprId]`: the
  `LocalCtxSnapshot` has no `Store` to decode an `ExprId`. Callers map
  through `MetaCtx::fvar_ids`.
- The slow path's private helpers are `ca_`-prefixed so they do not clash
  with `check.rs`'s `check`/`check_app`.
- `mk_binding` (`metactx.rs`) used to refuse a `have` as a SEAM. It now
  abstracts a nondep ldecl as a Default binder, as the oracle does with
  `generalizeNondepLet := true` (`MetavarContext.lean:1330-1332`). A
  genuine let is still refused.
- `op/binder-F-hole-chain` is not a separate row: its source is identical
  to the restored `op/stuck`.
- `op/rel-no-default` keeps its `x.1 < 2` spelling (its record pins
  `withSynthesizeLight`). The `(fun a => a < 2) z0` spelling is a new row,
  `op/rel-lt-beta`.

Final-review fix pass:
- `occurs_check` (`assign.rs`) now follows a delayed-assigned mvar to its
  `mvarIdPending`, as the oracle's `occursCheck.visitMVar`
  (`Util/OccursCheck.lean:26-35`) does. Delayed assignments do reach it
  now: `elimMVarDeps` on the `process_assignment` path makes them. No
  oracle corpus record changed answer under full `mise run ci`, so the
  port was kept.
- Mutations (each applied, run, reverted): (k) the port's delayed
  follow removed (`None => Ok(true)`): KILLED by
  `check_mvar_occurs_check_follows_a_delayed_pending_chain`. (l)
  `check_mvar`'s occurs check at the pending mvar (`:892-896`) removed:
  KILLED by `check_mvar_occurs_check_at_a_delayed_pending_mvar` (and the
  chain test). (m) `mk_binding` uses a `have`'s VALUE as the binder type:
  KILLED by `mk_binding_generalizes_a_have_and_refuses_a_let`, now
  declared with value `Nat.zero` and type `Nat`. Before the fix the value
  and type were both `Nat`, so (m) was unobservable.

Open follow-ups:
- ~~**P1 — Eta SEAM.** The oracle's `mkLambdaFVarsWithLetDeps` passes
  `etaReduce := true` (`ExprDefEq.lean:551,554`), and `mkLambda'`
  (`MetavarContext.lean:1281-1291`) reduces a `.app f (.bvar 0)` body.
  leanr's `mk_binding` does not eta-reduce. This is more than "equal up to
  eta": (a) after `elimMVarDeps` the body is exactly the delayed head
  `?i' #0`, so the oracle assigns `?m := ?i'` and leanr assigns
  `?m := fun x => ?i' x`. Where `?m` occurs UNAPPLIED, `instantiateMVars`
  differs: the oracle's bare delayed `?i'` (no args) never instantiates
  and stays an mvar, while leanr's `fun x => ?i' x` instantiates to
  `fun x => val` once `?i` is assigned, so leanr can succeed where the
  oracle reports an unassigned mvar. (b) Plain `?f x =?= g x` gives
  syntactically different final terms (`congrArg (fun x => g x) h` vs
  `congrArg g h`), visible to an oracle-differential corpus. Not a
  regression: the deleted `mk_lambda_over_fvars` never eta-reduced
  either. No corpus record shows it yet. Port sketch: an `eta_reduce`
  flag on `mk_binding`, used only by `mk_lambda_fvars_with_let_deps`; the
  cost is re-checking the corpus. Documented on
  `mk_lambda_fvars_with_let_deps` (`assign.rs`).~~ CLOSED (§ Landed › Eta follow-up).
- `checkApp`/`assignToConstFun`: no differential record (above).
- P3 T3 (d) remains unobservable (above).

### Eta follow-up (branch `eta-reduce-seam`)

Closes P1 above. `MetaCtx::mk_binding` takes an `eta_reduce` flag. Its
lambda arm is a port of `mkLambda'` (`MetavarContext.lean:1281-1291`),
applied to each binder from the innermost out: a body
`.app f (.bvar 0)` whose `f` has no loose `#0` becomes `f` lowered by
one. `mk_lambda`/`mk_forall` pass `false`. The new `mk_lambda_eta`
passes `true`, and its only caller is `mk_lambda_fvars_with_let_deps`
(`ExprDefEq.lean:551,554`).

**Corpus** (`op-queries.jsonl`, `CORPUS_FLOOR` 90 -> 94):
`meta/eta-congrFun'`, `meta/eta-congrFun`, `meta/eta-partial`, and the
control `meta/eta-blocked`. Each has the shape
`fun (g : …) => (congrFun' _ : ∀ (a : Nat), g a = g a)`. `?f`/`?g` are
minted outside `∀ a`, so `?f a =?= g a` is a Miller pattern, and the
oracle assigns `?f := g`. Before the fix, leanr built
`fun a => g a` and diverged on the first three. The control
(`g a a`, where `#0` is loose in the head) matches either way. The
binder is spelled `(a : Nat)` because leanr does not yet handle the
bare-ident `∀ a,` binder (`expandForall`).

Mutations (each applied, run, reverted):
- (i) `mk_lambda_fvars_with_let_deps` back to `mk_lambda`: KILLED by
  `oracle_op_gate` (3 records),
  `process_assignment_eta_reduces_the_pattern_lambda`, and
  `process_assignment_eliminates_mvar_deps_on_the_pattern_fvars`. The
  last now asserts `?m := ?i'` exactly, not a shape-agnostic check.
- (ii) the `has_loose_bvar(f, 0)` test dropped: KILLED by
  `oracle_op_gate` (`meta/eta-blocked`, "unexpected bound variable")
  and `mk_lambda_eta_reduces_per_binder_as_mk_lambda_prime`.
- (iii) only the innermost binder reduced: KILLED by
  `mk_lambda_eta_reduces_per_binder_as_mk_lambda_prime` alone. It
  survives the corpus, because no record has a multi-argument pattern
  (`?f a b`), and Prelude has no `{f : α → β → γ}` lemma that would
  produce one.

Full `mise run ci` is green, and no pre-existing record changed answer.

~~Open: `synth.rs`'s `try_resolve` pi-goal SEAM (`SynthInstance.lean:361`)
also calls `mkLambdaFVars … (etaReduce := true)`. Whoever ports
pi-shaped synthesis goals should use `mk_lambda_eta`.~~ CLOSED [synth pi-goals slice: `2026-10-02-synth-pi-goals-design.md` § Landed]; `try_resolve` uses `mk_lambda_eta`.
