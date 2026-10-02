# Synth pi-goals: `forallTelescope` in typeclass synthesis

## Where this sits

The macro/binop% spec, `2026-10-01-macro-expansion-binop-design.md`
§ Landed › P3, lists an open follow-up called the "synth pi-goal gap".
`synth_instance` cannot handle a goal of the form `∀ xs, C ..`, so
`(inferInstance : BEq Bool)` and `BEq Nat` both fail. Both go through
`instBEqOfDecidableEq`, whose subgoal `DecidableEq α` unfolds to
`∀ a b, Decidable (a = b)`. To get around this, ElabOp's test-support
suffix declares a closed `instance : BEq Bool`. Because of that
instance, `op/beq-prop`, `op/bne-prop` and `op/beq-prop-bool` pin
`instBEqBool` instead of the Prelude route (that spec's R5).

The checkAssignment spec,
`2026-10-02-check-assignment-ctx-approx-design.md` § Landed › Eta
follow-up, records the other half: `try_resolve` should use
`mk_lambda_eta`. #63 added `mk_lambda_eta` for this caller.

**Scope (the user's choice, 2026-10-02):** core pi-goals. This covers
real telescopes at every oracle telescope site in `SynthInstance.lean`.
It excludes porting `removeUnusedArguments?`, which stays a named seam
(see § Seams). It also excludes moving synthesis onto real mctx depth.
**Approach (the user's choice):** A. A synth-local telescope helper in
leanr_meta, with each site ported one-to-one onto it. Unifying it with
leanr_elab's `open_forall_telescope_core` (approach B) is a follow-up.

Pinned oracle: `leanprover/lean4:v4.33.0-rc1`. Every
`SynthInstance.lean` / `Basic.lean` citation below was opened against
that toolchain's `src/lean` while writing this spec.

## What is wrong today

There are two `MetaError::Unsupported` seams in
`crates/leanr_meta/src/synth.rs`:

- `preprocess` rejects a goal whose `whnf` is a `Forall`. The oracle
  instead runs `forallTelescopeReducing`, `whnf`s the body and calls
  `mkForallFVars` (`SynthInstance.lean:737-773`).
- `try_resolve` rejects a forall-shaped subgoal. The oracle instead
  opens `forallTelescopeReducing mvarType` (`:353`), builds the
  subgoals over `xs`, and then calls
  `mkLambdaFVars xs instVal (etaReduce := true)` (`:374`).

The second seam's blast radius is larger than the oracle's. A single
forall-shaped subgoal anywhere in the search aborts the whole
`synth_instance` call through `?`, even when another candidate would
have answered.

Both seam comments justify themselves with "no Meta-layer fvar
telescope in this crate". That is no longer true. leanr_meta now has
`push_local_decl`, `lctx_checkpoint`/`lctx_restore`, `mk_forall`,
`mk_lambda_eta` and `mk_aux_mvar_at`.

The oracle has five telescope sites:

| site | oracle | telescope |
|---|---|---|
| `getInstances` | `:202-243` (telescope at `:205`) | reducing |
| `getSubgoals` | `:317-339` (mint at `:325`) | none; it is passed `xs` |
| `tryResolve` | `:346-419` (`:353`, `:374`) | reducing |
| `preprocess` | `:737-773` | reducing |
| `preprocessOutParam` | `:775-818` | non-reducing |

`removeUnusedArguments?` (`:512-531`) has a sixth, non-reducing
telescope. It is out of scope (§ Seams).

## Design

### The telescope helper

Add a private method on `MetaCtx` in `synth.rs`. Synthesis is its only
caller.

```rust
/// oracle: `forallTelescope` / `forallTelescopeReducing`
/// (`Basic.lean:1561`, `:1592`; worker `forallTelescopeReducingAuxAux`, `:1453`).
fn with_forall_telescope<R>(
    &mut self,
    ty: ExprId,
    reducing: bool,
    k: impl FnOnce(&mut Self, &[ExprId], ExprId) -> Result<R, MetaError>,
) -> Result<R, MetaError>
```

- **Walk.** While the current type is a syntactic `Forall`, push one
  local decl per binder with `push_local_decl`, using the binder's
  name, binder info and domain. Instantiate the body with the new fvar
  and continue. When the type is not a `Forall` and `reducing` is set,
  `whnf` it once. If the result is a `Forall`, continue the walk;
  otherwise stop. `whnf` is reached only on the non-forall arm, as in
  the oracle's `process`. `k` receives `(xs, body)`. The body has been
  instantiated, and it has been `whnf`'d only if reducing exposed
  another forall.
- **Scope.** The helper brackets the walk and `k` with
  `lctx_checkpoint`/`lctx_restore`, and it restores on every exit,
  including `Err`. This is the idiom leanr_elab's
  `forall_telescope_reducing` uses. No telescope fvar outlives `k`.
- **Local instances.** `push_local_decl` installs an instance-implicit
  binder as a local instance, which is what the oracle's telescope
  does. `lctx_restore` uninstalls it (`local_instances.truncate_to`).

### Per-site ports

Every site keeps its current code as the `xs = []` case. The
binder-free goals that exist today go through the same instructions
they did before, so their behavior cannot change.

1. **`preprocess`** (`:737-773`). Open
   `with_forall_telescope(ty, reducing = true)`. `whnf` the body, set
   `type := mk_forall(xs, body)`, and classify on `body`
   (`noMVars` is decided on the rebuilt `type`, as in the oracle at
   `:743`). On the `MVarsOutputParams` arm, the normalized cache-key
   type is also re-wrapped with `mk_forall(xs, …)` (`:772`).
2. **`preprocess_out_param`** (`:775-818`). Use the non-reducing
   telescope. The rewritten result is `mk_forall(xs, mkAppN c args)`
   (`:814`, `:818`). The early returns (`typeBody.isConst`, not a
   class, no out-params) return the original `type`, unchanged.
3. **`get_instances`** (`instances.rs`, oracle `:202-243`). Take a
   snapshot of the local-instance candidates **before** opening the
   reducing telescope (oracle `:203-204`: "We must retrieve
   `localInstances` before we use `forallTelescopeReducing`"). Then
   resolve the class and look up globals on the telescope body. As a
   result, an instance binder inside the goal
   (`∀ [inst : C α], C α`) is **not** a candidate.
   The existing divergence for a goal that is not a class stays as it
   is: leanr returns `None` where the oracle throws. It is documented
   and out of scope.
4. **`get_subgoals(outer_lctx, xs, inst)`** (`:317-339`). For each
   binder `d` of the instance type, mint
   `?m : mk_forall(xs, d)` with
   `mk_aux_mvar_at(outer_lctx, …, MVarKind::Natural, None)`. Push
   `mk_app_spine(?m, xs)` into both `subst` and `instVal`. The
   re-`whnf` loop when the type stops being a syntactic forall is
   unchanged. Minting at the outer context gives the oracle's two
   stated invariants (`:308-309`): every synthesis mvar shares one
   local context, and `?m xs` is a higher-order pattern.
   leanr's `MVarDecl` has no `localInsts` field. A decl's local
   instances are derived from its `lctx` snapshot, so passing the outer
   snapshot is the whole of the oracle's `(lctx, localInsts)` pair.
5. **`try_resolve`** (`:346-419`). Capture `outer := current_lctx()`,
   then open `with_forall_telescope(mvar_type, reducing = true)`.
   Inside it:
   - `get_subgoals(outer, xs, inst)`;
   - `is_def_eq(body, instTypeBody)`, returning `Ok(None)` on false;
   - `instVal := mk_lambda_eta(xs, instVal)` (`:374`);
   - assign directly when `instantiate_mvars(body)` has no expr mvar
     (`:412-415`), otherwise re-unify `mvar =?= instVal` (`:417`);
   - `checkpoint()`, which is the oracle's `getMCtx` at `:418`.
   The checkpoint is taken inside the telescope. The subgoal decls it
   holds have `outer` as their context, so nothing dangles after the
   telescope's lctx restore. `instVal` is closed with respect to `xs`
   after `mk_lambda_eta`.
6. **`synth_instance_main` and the drivers** do not change. The root
   mvar is `mk_aux_mvar(type)` with the closed `∀ xs, C ..` type that
   `preprocess` rebuilt, matching the oracle's `main` (`:675-680`).
   `assign_out_params` unifies against `inferType result`, which is
   pi-typed in the same way.

**Table keys.** Every keyed type is a closed `∀ xs, C ..`. A unit test
pins that `KeyNormalizer::norm_expr` rebuilds `Forall` nodes and their
bodies, which contain loose bvars, structurally. If that test fails,
the fix is part of this slice.

**Error posture.** A pi subgoal no candidate solves is an ordinary
`Ok(None)` for that branch. Real `MetaError`s (budget, depth,
malformed term) still propagate, as everywhere else in synthesis.

### Seams

- **Closed:** `preprocess`'s and `try_resolve`'s pi-goal
  `Unsupported`.
- **Kept, with a new rationale: `removeUnusedArguments?`
  (`:512-531`, called from `consume` at `:558`).** Its doc in `consume` says
  "unreachable, because `try_resolve` refuses forall subgoals". That
  stops being true. The new doc says it is reachable and
  answer-neutral. The oracle tables `N → C` under the argument-stripped
  key and transports the answer back with
  `fun f _ => f` (`:529`). leanr tables it under the arrow and resolves it
  through `try_resolve`'s telescope. Both produce `fun _ => inst`. The
  Synth0 row `piUnused/synth/0` pins this. If the oracle's term
  differs, the seam is a bug, and the slice stops to re-scope with the
  user before widening.

## Testing

### Synth oracle corpus (`Synth0.lean` → `synth-queries.jsonl`)

Synth0 is prelude-mode and grows deliberately. Its existing queries
are curated, so appending declarations does not move their records.
Append this family; the names are provisional and are fixed in the
plan:

```lean
class Dec (p : Prop) where dec : N
instance instDecN (a b : N) : Dec (Eq a b) := ⟨N.zero⟩
abbrev DecEqN (α : Type) := (a b : α) → Dec (Eq a b)
class BE (α : Type) where be : N
instance instBEOfDecEq [DecEqN α] : BE α := ⟨N.zero⟩
class PB (α : Type) where pb : N
instance (priority := 100)  instPBLow  : PB N := ⟨N.zero⟩
instance (priority := 5000) instPBHigh [(x : N) → CoeT N x NoBase] : PB N := ⟨N.zero⟩
```

Add queries to `dump_synth.lean`'s `synthQueries`. Each row must be
killed by its mutation, and **each mutation is actually run** (memory:
plan briefs ship non-discriminating tests):

| row | goal | mutation it kills |
|---|---|---|
| `piRoot/synth/0` | `∀ a b : N, Dec (Eq a b)` | `preprocess` without a telescope (seam restored → error) |
| `piReducible/synth/0` | `DecEqN N` | the walk does not `whnf` a non-forall head |
| `piEta/synth/0` | same goal as `piRoot`; asserts the term is `instDecN`, not `fun a b => instDecN a b` | `mk_lambda` instead of `mk_lambda_eta` |
| `piApplied/synth/0` | `∀ a : N, Dec (Eq a N.zero)`; expects `fun a => instDecN a N.zero` | `get_subgoals` mints `?m : d` and does not apply it to `xs` |
| `piNested/synth/0` | `BE N` | nested pi subgoal (`try_resolve` seam restored) |
| `piUnused/synth/0` | `N → Pri N` | the `removeUnusedArguments?` answer-neutrality claim (§ Seams) |
| `piInstBinder/synth/0` | `∀ [h : NoInst N], NoInst N` | `get_instances` reads local instances after the telescope |
| `piBranch/synth/0` | `PB N` | the high-priority candidate's unsolvable pi subgoal aborts the whole search instead of failing its branch |

`piRoot` and `piEta` may be one record if the canonical term already
discriminates. The plan decides.

### Elab op corpus (`ElabOp.lean` → `op-queries.jsonl`)

- Delete `instance : BEq Bool := ⟨fun _ b => b⟩` and its comment from
  `tests/fixtures/elab/elab_op_support.lean.in` (`:69-70`). Regenerate
  with `mise run fixtures:regen`.
- `op/beq-prop`, `op/bne-prop` and `op/beq-prop-bool` (and, as found at
  regen, `op/beq-uncomparable-prop`) re-record
  against Prelude's `instBEqOfDecidableEq`. The plan reads the exact
  term off the regenerated oracle record and does not predict it here.
  The diff of the regenerated corpus must touch only those three
  records plus the new rows below. Any other moved record is reported
  in § Landed with a reason, not silently re-blessed.
- Add these rows: `meta/synth-pi-beq-nat` `(inferInstance : BEq Nat)`,
  `meta/synth-pi-deceq-nat` `(inferInstance : DecidableEq Nat)`, and
  `meta/synth-pi-beq-bool` `(inferInstance : BEq Bool)`.
  `CORPUS_FLOOR` in `oracle_op.rs` rises to match.
- `oracle_op.rs::elab_op_has_the_test_support_suffix` keeps
  `(inferInstance : BEq Bool)`. Its comment changes from "the closed
  `BEq Bool` of the suffix" to "Prelude's `BEq Bool` via
  `instBEqOfDecidableEq`, a pi subgoal".

### Unit tests (`synth.rs`)

- Replace `preprocess_seams_a_pi_shaped_goal` with
  `preprocess_telescopes_a_pi_shaped_goal`: `N → Add N` gives
  `∀ _ : N, Add N` with kind `NoMVars`.
- `with_forall_telescope` restores `lctx` and `local_instances` on
  both `Ok` and `Err`.
- `normalize_goal_key` on a pi type (see § Table keys).

## Doc and spec ledger

- Rewrite the doc comments on `preprocess`, `preprocess_out_param`,
  `get_instances` (and `instances.rs`'s module doc paragraph "takes an
  ALREADY-telescoped class application"), `get_subgoals`,
  `try_resolve` and `consume`. Open every new cite against the pinned
  toolchain. Fix any stale line numbers the slice touches.
- Sweep `grep -rn "pi-shaped\|forallTelescope\|forall-shaped" crates/`
  and update or remove every remaining mention of the closed seams,
  including `MetaError::Unsupported`'s doc and `leanr_meta/src/lib.rs`.
- Macro/binop% spec § Landed › P3: strike through the "synth pi-goal
  gap" bullet with `CLOSED [synth pi-goals slice]`, and mark R5
  "reverted".
- checkAssignment spec § Landed › Eta follow-up: mark the
  `try_resolve … mk_lambda_eta` item CLOSED.

## Risks

- **Every synth mvar's context changes.** A subgoal mvar is now minted
  at an explicit `outer` snapshot instead of the ambient lctx. Outside
  a telescope the two are the same snapshot, so existing behavior
  holds. The existing synth corpus and elab corpora are the check.
- **`ctxApprox` inside a telescope.** `?m xs =?= t` now reaches
  `checkAssignment` with telescope fvars in scope. That path landed in
  #62/#63 and has corpus coverage for Miller patterns, but not under
  synthesis config (`ctxApprox := true`, `foApprox := true`).
  `piApplied` is the row that exercises it.
- **Search-size changes.** Goals that used to abort early now search.
  `near_budget` flags in the synth corpus guard against a row that
  quietly runs near the step budget.

## Out of scope

- Porting `removeUnusedArguments?` (kept as a seam; § Seams).
- Synthesis onto real mctx depth (`withNewMCtxDepth`) and the
  rollback stand-in.
- Approach B: one shared telescope in leanr_meta, with leanr_elab's
  `open_forall_telescope_core` calling it.
- The `get_instances` "goal is not a class" divergence.

## Plan shape

One plan and one PR, in four tasks:

1. `with_forall_telescope`, plus `preprocess`, `preprocess_out_param`
   and `get_instances`, with unit tests.
2. `get_subgoals(outer, xs, …)` and `try_resolve`, with unit tests.
3. The Synth0 family, the `dump_synth.lean` rows, regen, and the
   mutation runs.
4. The ElabOp suffix drop, regen, the three re-recorded rows, the new
   elab rows, `CORPUS_FLOOR`, and the doc/spec ledger.

## Landed

Commits on `synth-pi-goals`: 4595e44 (spec), e4ab2be (plan), 549c8c9 (T1:
forall telescope in `preprocess`/`preprocess_out_param`/`get_instances`),
74920d5 (T2: `try_resolve`/`get_subgoals` pi goals, `mk_lambda_eta`),
b6c3282 (T3: Synth0 oracle rows), and the T4 commit (ElabOp suffix drop,
elab rows, docs, this ledger).

**Corpus counts.** Synth: 30 -> 37 compared records (seven `pi*` rows;
`piEta` folded into `piRoot`). Op: 94 -> 97 (`CORPUS_FLOOR` = 97): three new
`meta/synth-pi-{beq-nat,deceq-nat,beq-bool}` rows. Four rows re-recorded
against `instBEqOfDecidableEq Bool instDecidableEqBool` in place of
`instBEqBool`: `op/beq-prop`, `op/bne-prop`, `op/beq-prop-bool`, and
`op/beq-uncomparable-prop`. The fourth was not predicted by the spec: its
source `(binop% PU n u) == True` is a Bool `==` that also went through the
dropped suffix `BEq Bool`, and its only term change is that same
substitution. No other op-queries id moved.

**Oracle verdicts as observed.** `piUnused`: `fun (_ : N) => instPriHigh`, so
the `removeUnusedArguments?` absence is answer-neutral. `piInstBinder`:
`ok=false` (the goal's own instance binders are not candidates). All seven
records `near_budget:false`.

**piBranch binder change.** T3 changed `instPBHigh`'s binder from
`[(a b : N) -> NoInst (Dec (Eq a b))]` to `[(x : N) -> CoeT N x NoBase]`: the
original binder had no candidates, so `try_resolve` never ran on it and the
row killed nothing. The oracle record is byte-identical. The snippet above
and the plan carry the new binder.

**Mutation table** (run on the committed fixtures).

| mutation | result |
|---|---|
| 1c `preprocess` non-reducing telescope | survives; EQUIVALENT (the rebuilt type is identical for `DecEqN N`) |
| 1c' `with_forall_telescope` ignores `reducing` | killed by `piNested` |
| 1b `get_instances` snapshots local instances inside the telescope | killed by `piInstBinder` |
| 2a `mk_lambda` for `mk_lambda_eta` | killed by `piRoot`, `piReducible`, `piNested` |
| 2b subgoal mvar not applied to `xs` | SURVIVES the oracle gate; killed only by the unit test `pi_goal_subgoals_are_applied_outer_mvars` |
| 2c `outer` captured inside the telescope | killed by `piRoot`, `piReducible`, `piApplied`, `piNested` |
| `try_resolve` `Unsupported` seam restored | killed by `piRoot`, `piReducible`, `piApplied`, `piNested`, `piUnused`, `piBranch` (synth), and in `oracle_op` by 7 rows: `meta/synth-pi-{beq-nat,deceq-nat,beq-bool}`, `op/beq-prop`, `op/bne-prop`, `op/beq-prop-bool`, `op/beq-uncomparable-prop` |
| `try_resolve` `Err` instead of `Ok(None)` on `is_def_eq` failure under non-empty `xs` | killed by `piBranch` (only with the strengthened binder) |

**Open follow-ups.**
- Approach B: a shared meta/elab telescope.
- Synthesis onto real depth.
- Port `removeUnusedArguments?` (currently answer-neutral, `piUnused`).
- The `get_instances` non-class divergence.
- An 8th oracle row with a solved, telescope-dependent instance subgoal
  (e.g. an instance `[forall x, C x]`), to make mutation 2b oracle-observable.
- Minor: `lctx_restore` drops the `lctx_snapshot` cache even when nothing was
  pushed, so each candidate re-clones (perf only).
- Minor: binder-free goals take one extra `step()` per `try_resolve` and per
  preprocess/`get_instances` telescope. This matches the oracle and no
  corpus record moved.
