# letToHave — nondependent `let` → `have` in declarations — design

Status: draft for review, 2026-10-07. This is worktree D of the post-#81
parallel batch (A error first lines, C `variable {x}` update, B term-level
`open … in`, D this). It merges after B.

## Goal

A `let` in a definition's type or value must reach the kernel with the same
`nondep` flag the oracle gives it. Today every `let`/`have` left in a
declaration's final type or value raises the seam ``"`let`/`have` in a
declaration's type or value (letToHave) — later M4"``
(`command/def.rs:400-413`). leanr already elaborates `let` (nondep = false)
and `have` (nondep = true), and the kernel `LetE` already carries the flag
(nondep slice, #48). What's missing is the oracle's post-elaboration pass,
`Meta.letToHave`. That pass rewrites every `let` that is not
*definitionally used* into a `have`.

Success means that the 29 probed `lth/*` file rows (in `target/designD/`)
match the oracle and the seam is gone. The one exception is
`lth/instance`, because leanr has not ported the `instance` command.

## Oracle behaviour (v4.33.0-rc1, lines opened)

**Callers**
- `addNonRecAux` runs `abstractNestedProofs`, then `letToHaveType`, then
  `letToHaveValue` when `cleanupValue` is set (`PreDefinition/Basic.lean:183-185`).
  Nonrecursive defs pass `cleanupValue := true`.
- `letToHaveValue` (`:99-108`) skips the value when `cleanup.letToHave` is
  off, the declaration is `unsafe`, its kind is `theorem`, `example` or
  `opaque`, or its type is a Prop.
- `letToHaveType` (`:113-118`) skips only `example`.
- The async theorem header also runs `Meta.letToHave type`
  (`MutualDef.lean:1293-1296`; leanr cites this at `def.rs:250`).
- Axioms never run it.

**`Meta.letToHave`** (`Meta/LetToHave.lean:440-443`) runs `instantiateMVars`
and then `main`.

**`main`** (`:416-431`):
- It returns `e` unchanged unless `hasDepLet e` (`:67`), meaning some
  `letE (nondep := false)` exists.
- Otherwise it runs `visit` under `withTrackingZetaDelta`,
  `withTransparency .all` and `withInferTypeConfig`.
- `withTrackingZetaDelta` (`Meta/Basic.lean:1243-1245`) means
  `withFreshCache`, `trackZetaDelta := true`, and a cleared
  `zetaDeltaFVarIds` that is restored on exit.

**`visit`** (`:398-412`) is a purpose-built type checker. It caches results
per `ExprStructEq` and carries a context `letFVars`, the dependent lets in
scope. It does full checking only while `letFVars` is non-empty
(`Context.check`).

**`visitLambdaLet`** (`:302-368`) enters a whole lambda/let telescope:
- A let's value is checked against its declared type only under an
  enclosing dependent let (`:325-328`).
- A let joins `letFVars` only if it is itself dependent (`:331`).
- `finalize` (`:338-368`) rebuilds the telescope. A non-dependent `ldecl`
  becomes `nondep := true` iff its fvar is **not** in `zetaDeltaFVarIds`.
  An existing `have` stays a `have`.

**How a let gets recorded as used (unfolded):**
1. The `.fvar` arm of `whnfEasyCases` (`Meta/WHNF.lean:397-409`), when
   `trackZetaDelta` is on. Under `withInferTypeConfig` `zetaDelta` is true,
   so every genuine let-fvar that whnf unfolds is recorded.
2. `visitDepExpr` (`:164-181`), reached through `checkMVar` for
   delayed-assigned mvars. After `instantiateMVars` a finished
   declaration has none of these. It is unreachable from file rows, so it
   gets a unit-test pin only.

**Approximation:** this is a conservative check. A `let` that `isDefEq`
unfolds without needing to stays a `let`. This approximation is part of the
observable behaviour, so leanr must reproduce it rather than compute the
precise answer.

## Approach

**Recommended: A, a faithful port.** Port `LetToHave.lean` as written: the
same `visit` traversal, `Context.check` gating, cache and `finalize`. Record
zeta-delta unfolds through a tracking channel in `MetaCtx` that whnf's
let-fvar arm writes to.

**Rejected:**
- **B, a precise check.** For each `let`, test whether `fun x : t => b` is
  type-correct with leanr's existing checker. That classifies strictly
  more lets as `have` than the oracle's approximation does, so it is a
  silent wrong answer. It is also quadratic on nested lets.
- **C, syntactic occurrence.** "x occurs in the body, so dependent" is
  wrong both ways: `lth/defDep` (`let T := Nat; (Nat.zero : T)`) gives `have`
  on the oracle, because the ascription leaves no reference to `T`.

## Components

### 1. `leanr_meta`: zeta-delta tracking (new `MetaCtx` state, TCB-neutral)

- New fields on `MetaCtx`: `track_zeta_delta: bool` and
  `zeta_delta_fvar_ids: HashSet<FVarId>` (or the crate's id-set type).
- `whnf.rs:248-268`, the `Node::FVar` arm of the easy cases: when the let
  value is followed and `track_zeta_delta` is on, insert the fvar. This is
  exactly the seam that the module doc there already names
  (`trackZetaDelta` channel). `zetaDeltaSet` and `isImplementationDetail`
  stay seamed: no elab path sets them.
- `with_tracking_zeta_delta(f)` saves and clears the set, sets the flag,
  and runs `f` under a **fresh cache scope**, then restores all three on
  every exit path. The fresh cache scope covers `whnf_cache`,
  `whnf_core_cache`, `infer_cache`, `defeq_cache_perm` and
  `defeq_cache_transient`. The caches are swapped out and swapped back, not
  cleared for good, as `mk_binding.rs:678`'s `withFreshCache` scope does;
  reuse that helper if it generalises.
- `zeta_delta_fvar_ids()` accessor.
- This is an additive, TCB-neutral `leanr_meta` interface change under
  the M4b accessor-precedent amendment. `leanr_kernel` is untouched.

**Audit (part of the work, not optional):** every leanr path that follows a
let-fvar's value must either go through the whnf arm or record. Candidates
named by the design probe: `assign.rs:976/1071`,
`check_assignment.rs:105/302/394`, `transform.rs:119`. For each one, decide
whether the oracle counterpart records (only `whnfEasyCases` and
`visitDepExpr` do). Make leanr match, and write the outcome down in the
plan.

### 2. `leanr_meta/src/let_to_have.rs` (new module)

A port of `LetToHave.lean` (449 lines, about 330 of them code; expect
500–700 lines of Rust plus tests):
- `has_dep_let`, `can_skip` (approxDepth ≤ 5, matching leanr's approxDepth
  if one exists; otherwise the skip is a pure optimisation, so document an
  equivalent choice);
- `Result { expr, ty: Option<ExprId> }` and the `results` cache;
- `visit_fvar/mvar/const/app/app_args/forall/lambda_let/proj`;
- `finalize`;
- `main`;
- `pub fn let_to_have(&mut self, e)`.

`visit_proj` reuses `structure.rs`. The oracle's error throws (`invalid let
declaration`, app mismatch, function expected) cannot fire on a type-correct
elaborated term. Map them to `MetaError` (never a panic) and do not add them
to the corpus.

`main` runs under transparency `.all` and the infer-type config.
`config.rs` already exposes the config fields; add a
`with_infer_type_config` helper if one does not exist.

### 3. `leanr_elab/src/command/def.rs`

- Delete `reject_let`, along with its seam string and seam unit test.
  Replace it with `let_to_have_type` and `let_to_have_value` wrappers that
  carry the oracle's gates. The gates read `DefKind`, the `unsafe`
  modifier (still seamed at `view.rs`, so in practice always safe) and
  `is_prop(type)`, using the existing full-`isAlwaysZero` `is_prop` in
  def.rs.
- Order: `abstract_nested_proofs`, then the type pass, then the value pass,
  as in the oracle. Fix the comment at `:139`.
- The async theorem header path (`:250`) runs the type pass after
  `fix_level_params`.
- `cleanup.letToHave` is not modelled (`set_option` covers only the two
  autoImplicit options). Any other option keeps the existing
  `set_option … — later M4` seam, so the option is effectively always on.

## Data flow

elaborate → instantiate mvars → fix level params →
ensure-no-unassigned-mvars → `abstract_nested_proofs` (non-theorem) →
**`let_to_have(type)`** (non-example) → **`let_to_have(value)`** (gated) →
kernel `add_decl_in`.

On the theorem path, the async header also runs `let_to_have(type)` early.
The pass is idempotent, so running it twice on a type is harmless.

## Error handling

- A `MetaError` from the pass propagates as `ElabError::Meta`. On
  oracle-shaped input it cannot happen.
- No new `ElabError` variants.
- The tracking scope must restore state on `Err` as well as `Ok`, because
  overload stages and retries catch errors.

## Testing

**Corpus:** add the 29 rows probed in `target/designD/rows.txt` (minus
`lth/instance`) as one fileQueries block. Re-probe them at plan time. The
current floor is whatever main has after A, C and B land.

| Rows | Oracle | Pins (mutation) |
|---|---|---|
| defVal, defNested, defLam, unusedLet, letInArg, letProofVal, defLetTypeOnly, abbrev | value `have` | never transform |
| defDep | `have` (the ascription leaves no ref) | "mentioned ⇒ dependent" |
| defNestedDep, nonPropDep, lamBinderDep | value keeps `let` | always nondep / never check |
| depAfterNondep, nonPropDepIdx | mixed | `letFVars` ordering |
| defHave | `have` stays | — |
| defType, defTypeArrow, thmType, opaqueType | type `have` | skip the type pass |
| thmVal, thmValDep | value `let` | transform theorem values |
| propDef, defDepRfl | `let` (Prop-typed) | drop the `isProp` gate |
| opaque | value `let` | transform opaque values |
| axiomType | type `let` (already passes) | transform axiom types |
| example, exampleType | no constants, no error | example gate |

**Unit tests (`leanr_meta`)**, for what no row can reach:
1. **Warm cache.** Run a defeq or whnf that unfolds `x` BEFORE
   `with_tracking_zeta_delta`. Inside the scope, the same query must still
   record `x`. This kills the mutation "no fresh cache scope".
2. **Restore on exit.** After the scope, the flag is off, the set is back
   to its saved contents, and the outer caches are intact. Check both on Ok
   and on Err.
3. **A `have` is never followed**, so it is never recorded.
4. **`visitDepExpr` through a delayed-assigned mvar** marks the let.
5. **One test per audited path from Component 1** whose ruling is
   "records".

**Mutations to run and record:** everything in the table; the fresh cache
scope; the restore; `Context.check` always true and always false; `finalize`
reading the flag inverted; the type pass on axioms; both header-pass sites
(the duplicate type pass may be equivalent, and that has to be shown).

## Seams after this slice

- `cleanup.letToHave` as an option (`set_option` seam).
- `zetaDeltaSet` / `isImplementationDetail` in whnf (no elab producer).
- The `instance` command is unported (`lth/instance`).
- `unsafe` stays seamed at `view.rs` (worktree E).

## Risks

- **A cache path that skips the record gives a silent wrong `have`.**
  Mitigated by the fresh-scope unit test plus the audit.
- **A let-unfold path outside whnf.** Mitigated by the audit table.
- **`_proof_N` interaction is unprobed:** Elab0 cannot build a nontrivial
  proof inside a let. At plan time, try a proof value inside a `let` in a
  def, so that `abstractNestedProofs` lifts it first. If no row is
  buildable, record it as a seam.
- **Performance:** the pass re-infers types under a fresh cache. That is
  acceptable at corpus scale; note it for M4 Mathlib slices.

## Plan amendments

Plan-time findings (docs/superpowers/plans/2026-10-07-let-to-have.md, lines 30-57) that override this spec:

1. `abstractNestedProofs` returned `Unsupported` on every `letE`; Task 3 ports the oracle's `letE` arm (`lambdaLetTelescope`, per-binder visit, `mkLambdaFVars (usedLetOnly := false)`).
2. After abstraction, check mode reaches `visitConst` on a still-pending `d._proof_N`: the pending-constant seam. `auxProofLet*` rows (oracle H, H, L) became seam unit tests, not corpus rows. `auxProofLetDep` also kills the "letToHave before abstraction" mutation.
3. Zeta-delta records are backtrackable (`SavedState.restore`, `Meta/Basic.lean:596`) but survive `withNewMCtxDepth` (`:1974-1980`).
4. The fresh-cache scope is equivalent in leanr (every cached entry is fvar-free; top-level `is_def_eq` clears the defeq caches). It is ported for fidelity.
5. The async theorem header pass is unobservable (`check_async_signature` returns only level params); it is not ported.
6. Audit result: no fixes beyond the whnf easy-cases FVar record. The oracle records in exactly three places: `WHNF.lean:408` (whnf easy-cases `.fvar`), `LetToHave.lean:174` (inside `visitDepExpr`, `:164-181`), and `LetToHave.lean:188` (`checkMVar`'s invalid-delayed-assignment arm, which marks every enclosing `letFVars`; ported at `let_to_have.rs` "An invalid delayed assignment").
7. Corpus is 42 `lth/*` rows (3 pending seams and `auxProofNoLet` excluded; `lth/instance` dropped).

Execution amendments:

- The plan's `mk_lambda_let_fvars` omitted the oracle's head-beta of cdecl binder types (`MetavarContext.lean:1319`); fixed in 25950d1.
- Review found the let-binder visit order was types-then-values; the oracle interleaves per binder (`AbstractNestedProofs.lean:77-89`). It is now interleaved, which matters for `_proof_N` numbering (1cc6b49).
- `visitProj` is ported step by step (3403d2a).
- Telescope lets are pushed without `isClass?`. leanr keeps the outer local instances where the oracle clears them: a documented narrowing (3403d2a).
- T4h was first recorded as equivalent. It is NOT: a prefix-cache hit on a delayed `?m` makes the `visitDepExpr` args path load-bearing; a new test pins it (3403d2a).
- Corpus floor 490 -> 532 (bb1e98b, 886c643).
- Executed order: T2, T3, T4, then T1, T5, T6, because A, C and B had to merge first.

## Landed

Commits (branch d-let-to-have): ba40d09 (T2 zeta-delta tracking), 25950d1 + 1cc6b49 (T3 abstractNestedProofs letE arm), 3403d2a (T4 `let_to_have` port), bb1e98b + 886c643 (T1 42 `lth/*` rows, floor 490 -> 532), a0b796a (T5 wired into `def.rs`, replacing its three `reject_let` calls; `axiom.rs` is untouched, since oracle `elabAxiom` runs no `letToHave` and leanr's axiom path never called `reject_let`; all 42 rows green), then this close-out.

Mutations (run, reverted; details in each commit body):

| Task | Mutation | Outcome |
|---|---|---|
| T2 | a drop insert, b record before nondep filter, c snapshot without set, d drop mctx-depth carve-out, f unrestored flag | killed (`tracking_*`, `a_failed_def_eq_*`, `new_mctx_depth_*`) |
| T2 | e skip fresh cache | killed by cache assertion only; record behaviour equivalent (finding 4) |
| T3 | a mk_lambda rebuild, b drop unused let, d drop cdecl headBeta | killed |
| T3 | c skip let-value visit | survived at T3; killed in T5 by `lth/auxProofInLetValue` |
| T4 | a, b, c, e, f, g, h, i, j, k, l | killed (see 3403d2a) |
| T4 | d `check()` always true | killed only via the ill-typed cache probe; equivalent on well-typed input |
| T5 | a, b, c, d, e, f, h, i, j, k | killed (rows or unit tests; see a0b796a) |
| T5 | g type+value pass on example | equivalent (examples are only kernel-checked, never abstract) |

T5b's literal "drop Theorem from the kind gate" is equivalent (`pushMain` already rejects non-Prop theorem types). T5h is killed only by the oracle_decl seam test (d28 is the first to return Ok), no file row.

Final-review C1 (fixed, not seamed). Deleting `reject_let` exposed a silent wrong Ok: `def e6 : Nat := let x := 1; PProd.fst (PProd.mk x (rfl : Eq x (Nat.succ Nat.zero)))` admitted the let value `@OfNat.ofNat Nat 1 (OfNat.mk (Nat.succ Nat.zero))`, where the oracle has `instOfNatNat 1`. Root cause, in `leanr_meta` and not letToHave itself: the numeral's `OfNat ?α 1` instance is still pending when the body's `rfl` check zeta-unfolds `x`, which leaves `Nat.succ Nat.zero =?= ?inst.1`. The oracle (trace probed) refuses the class-singleton solution, because `isDefEqSingleton` returns false on a class (`ExprDefEq.lean:2127`, issue #2011). It then reaches `isDefEqOnFailure` → `unstuckMVar` (`:2022-2026`, `:1985-1991`), which runs `synthPending` on `?inst` and retries. leanr elided the `isClass` guard ("no class registry") and had `isDefEqOnFailure` as a silent-`false` seam, so the singleton arm assigned `?inst := OfNat.mk v`. Without a `let`, the instance is synthesized before the comparison, which is why only the let path diverged. Fix: the `isClass` guard in `lazy_delta.rs::is_def_eq_singleton` (via `ClassTable::is_class_name`), plus `defeq.rs::is_def_eq_on_failure`/`unstuck_mvar`, wired at the oracle's three call sites (`:2174` and `:2178` after a `checkpointDefEq`-wrapped `isDefEqApp`, and `:2232`). It includes the `isDefEqStuckEx` outer-depth throw. `tryUnificationHints` stays a named seam. Pinned by 8 `lth/num*` rows (the reviewer's 2 plus 6 variants; floor 532 -> 540) and 3 unit tests. Mutations: guard removed → 5 rows plus 2 unit tests fail; `is_def_eq_on_failure` stubbed → 5 rows plus 1 unit test fail; the `isDefEqApp` fallback alone removed → `app_congruence_failure_falls_back_to_on_failure` fails (oracle-probed: `true`, `?m := instMyAddN`).

Open seams:

- pending-constant overlay (d28/d29/d30 raise the seam; `abstract_proofs.rs` and `let_to_have.rs` are its two callers);
- `cleanup.letToHave` as an option (`set_option` seam);
- `zetaDeltaSet` / `isImplementationDetail` in whnf (no elab producer);
- the `instance` command is unported (`lth/instance`);
- `unsafe` stays seamed at `view.rs`;
- `etaStruct := .all` is not modelled in `with_infer_type_config`;
- `cleanupAnnotations` stripping is untested.
- found in the C1 wave, loud and not fixed: `let x := 0; … (rfl : Eq x Nat.zero)` is a `StuckCoercion` in leanr but Ok in the oracle. The failing subproblem is `Nat.zero =?= 0` (a literal), which the oracle settles and leanr does not. Likely the `isDefEqOffset` seam (`lazy_delta.rs`), so not specific to `let`;
- found in the C1 wave, loud: `let x := 1; … (rfl : Eq (Nat.succ Nat.zero) x)` (operands swapped) hits the pending-constant seam above (`e14._proof_1`);
- `tryUnificationHints` (`ExprDefEq.lean:2026`) is still a silent `false`, because no unification-hint table is decoded;
- `isDefEqApp` same-head order: leanr compares head levels before the args, while the oracle compares args before levels (`:2171`). The `fromClass` `withImplicitConfig` bump in `isDefEqProj` is also still elided.
