# `numScopeArgs` and the constant-approximation gates — design

Status: approved in brainstorming 2026-10-03 (architectural path).
Follow-up of M4b-4a P2 (`2026-09-29-m4b4-dot-notation-design.md` § Landed ›
P2, "leanr has no `numScopeArgs` constant approximation"). The delayed-
assignment machinery it builds on landed in #62
(`2026-10-02-check-assignment-ctx-approx-design.md`).

Pinned oracle: `leanprover/lean4:v4.33.0-rc1`. Every citation below was
opened against that toolchain's `src/lean` while writing this spec.

## Goal

The oracle's `MetavarDecl.numScopeArgs` records how many of a metavariable's
arguments model a *potential dependency on a binder*, not a genuine function
argument. Two defeq gates read it to decide whether constant approximation
(`?m a₁ … aₙ =?= v` solved by `?m := fun _ … _ => v`) is allowed when
`cfg.constApprox` is off — the default (`ExprDefEq.lean:751-797`, note A7
above `mkAuxMVar`).

leanr has no such field. `assign.rs` collapses both gates to
`cfg.const_approx` alone, so constant approximation is dead on the default
profile and the elaborator rejects terms the oracle accepts. Re-probed on
main (`038fc82`) on 2026-10-03:

| term | leanr | oracle |
|---|---|---|
| `(fun x y => y) Nat.zero Nat.zero` | `StuckCoercion` | accepts |
| `(fun x y => x) Nat.zero Nat.zero` | `StuckCoercion` | accepts (to be probed) |
| `(fun (x : Nat) f => f) Nat.zero Nat.succ` | `StuckCoercion` | accepts |
| `(fun x f => f x.1) (Prod.mk Nat.zero Nat.zero) Nat.succ` | `FunctionExpected` | accepts |
| `(fun f x => Nat.succ x.1) Nat.succ (Prod.mk Nat.zero Nat.zero)` | `InvalidProjection{TypeUnknown}` | accepts |

(`(fun x => Prod.fst x) (Prod.mk ..)`, listed in the P2 § Landed with the
others, now succeeds and is out of scope.)

Port `numScopeArgs` (field, producers, both gates) and, because opening the
gate makes it live on the default profile, port `processConstApprox`'s
longest-prefix search 1:1.

Scope: `leanr_meta` only. `leanr_elab` picks the behaviour up through
`mkLambdaFVars` → `elimMVarDeps` and changes only in tests and the corpus.

## The oracle model

- **The field.** `MetavarDecl.numScopeArgs : Nat := 0`
  (`MetavarContext.lean:323`); `addExprMVarDecl … (numScopeArgs := 0)`
  (`:809-820`); `mkFreshExprMVarAt … (numScopeArgs := 0)`
  (`Meta/Basic.lean:851-859`).
- **Producer 1, `elimMVar`** (`MetavarContext.lean:1205-1210`):
  ```
  let result       := mkMVarApp mvarLCtx newMVar toRevert newMVarKind
  let numScopeArgs := mvarDecl.numScopeArgs + result.getAppNumArgs
  … addExprMVarDecl newMVarId … newMVarKind numScopeArgs
  ```
  `result.getAppNumArgs` is the number of fvars `mkMVarApp` actually applied.
  `mkMVarApp` (`:1090-1097`) skips non-fvar entries and, for a
  non-`syntheticOpaque` mvar, genuine let-bound fvars, so this can be
  **smaller than `toRevert.size`**. (leanr's `collect_forward_deps` returns
  fvars only, so the non-fvar arm is vacuous there; the let-skip is live.)
- **Producer 2, ctxApprox restriction** (`ExprDefEq.lean:936`, inside
  `checkMVar`'s restriction path): `mkAuxMVar lctx localInsts mvarType
  mvarDecl.numScopeArgs` — the restricted aux mvar inherits the original's
  count.
- **Every other mint is 0.** `mkAuxMVar`'s default; in particular
  `checkApp`'s handler (`:967-981`) and `isDefEqMVarSelf`'s aux mvar
  (`:1801`) pass none. (Exhaustive: `grep -rn numScopeArgs src/lean/Lean`
  lists only the sites above plus a tactic-only copy in
  `Elab/Tactic/Do/VCGen/SuggestInvariant.lean:318`.)
- **Gate 1, `isDefEqMVarSelf`** (`ExprDefEq.lean:1790-1804`):
  `if mvarDecl.numScopeArgs == args₁.size || cfg.constApprox then` mint an
  aux mvar of `inferType (mkAppN mvar args₁)` in `mvarDecl.lctx` and
  `assignConst mvar args₁.size auxMVar`; else `false`.
- **Gate 2, `processConstApprox`** (`ExprDefEq.lean:1271-1309`):
  ```
  if mvarDecl.numScopeArgs != numArgs && !cfg.constApprox then return false
  else if patternVarPrefix == 0 then defaultCase          -- assignConst mvar args.size v
  else
    argsPrefix := args[*...patternVarPrefix]
    type ← instantiateForall mvarDecl.type argsPrefix
    suffixSize := numArgs - argsPrefix.size
    forallBoundedTelescope type suffixSize fun xs _ => do
      if xs.size != suffixSize then defaultCase
      else
        let some v ← mkLambdaFVarsWithLetDeps xs v | defaultCase
        go argsPrefix v
  go argsPrefix v:
    cont := if argsPrefix.isEmpty then defaultCase
            else let some v ← mkLambdaFVarsWithLetDeps #[argsPrefix.back!] v | defaultCase
                 go argsPrefix.pop v
    match ← checkAssignment mvarId argsPrefix v with
    | none      => cont
    | some vNew =>
      let some vNew ← mkLambdaFVarsWithLetDeps argsPrefix vNew | cont
      if argsPrefix.any (mvarDecl.lctx.containsFVar ·) then
        (isTypeCorrect vNew <&&> checkTypesAndAssign mvar vNew) <||> cont
      else
        checkTypesAndAssign mvar vNew <||> cont
  ```
  `<||>` / `<&&>` are Bool combinators with **no state rollback**; the
  enclosing `isDefEq` checkpoint is the only one.
- **Callers of gate 2** (`ExprDefEq.lean:1319-1339`, `useFOApprox`):
  `processAssignmentFOApprox mvar args v <||> processConstApprox mvar args i v`,
  with `i` = the index of the first non-pattern argument, or `args.size`
  for the A6 / failed-`checkAssignment` exits.
- **`instantiateForall`** (`Meta/Basic.lean:2142-2153`): for each `p`,
  `whnf e`; `forallE _ _ b _` → `b.instantiate1 p`; otherwise
  `throwError "invalid instantiateForall, too many parameters"`.

## Design

### §1 Data model and propagation

- `MVarDecl` (`mvar_ctx.rs`) gains `pub num_scope_args: usize`. Every
  `MVarDecl { .. }` literal states it (≈18 sites, mechanical); no
  `Default`-based shortcut, so the compiler flags each one.
- `mk_aux_mvar_at(lctx, ty, kind, user_name, num_scope_args)` gains the
  parameter (oracle `mkFreshExprMVarAt`'s shape). `mk_aux_mvar(ty)` stays a
  wrapper passing 0. Every caller states its value:
  - `elim_mvar` (`mk_binding.rs`): mint **after** computing `result`, with
    `decl.num_scope_args + app_num_args(result)` — the arg count of
    `mk_mvar_app`'s output, NOT `to_revert.len()`. Today `elim_mvar` mints
    the mvar before `mk_mvar_app`; the count is known only afterwards, so
    either reorder (mint a placeholder id, then declare) or compute the
    applied-arg count with a `mk_mvar_app`-shaped counter first. The plan
    picks one; the invariant is "equals `getAppNumArgs` of the `result`
    actually returned".
  - ctxApprox restriction (`check_assignment.rs` ~360): pass the restricted
    mvar's `decl.num_scope_args`.
  - `ctx_approx_const_fun` (`check_assignment.rs` ~442), `isDefEqMVarSelf`'s
    `mk_aux_mvar_for`, synthesis and every elaborator mint: 0.
- Checkpoint/rollback and `with_new_mctx_depth` save/restore need no change:
  the field lives inside the decl.

### §2 The gates and the `processConstApprox` port (`assign.rs`)

- **Gate 1** (`is_def_eq_mvar_self`, ~246): `decl.num_scope_args ==
  args1.len() || self.cfg.const_approx`. Replace the comment that says the
  gate collapses to `const_approx`.
- **Gate 2**: rewrite `process_const_approx` 1:1 against `:1271-1309`
  (pseudo-code above). Notes:
  - The `go`/`cont` recursion is tail-recursive; write it as a loop over a
    shrinking prefix, carrying `v`. No stacker.
  - "in the mvar's decl lctx" is `decl.lctx.lctx().get(fid).is_some()`, the
    same test `process_assignment` already uses for `has_ctx_locals`.
  - The type-correct check is `is_type_correct` (`check.rs`), as the oracle
    calls `isTypeCorrect` here — not `process_assignment`'s
    `infer_type_succeeds`.
  - **No extra checkpoints.** Port the Bool combinators literally; a failed
    `check_types_and_assign` falls to `cont` without rollback, as in the
    oracle. The doc comment says so, so a reviewer does not "fix" it.
  - `mk_lambda_fvars_with_let_deps` returning `None` (its let-decl seam)
    routes exactly where the oracle's `| defaultCase` / `| cont` do.
- **New helper `instantiate_forall(e, ps)`** (oracle `Meta/Basic.lean:2142-2153`):
  whnf, match a pi, `instantiate1`. Not-a-pi is a `MetaError`, never a panic.
- **Delete** the seam doc on `process_const_approx` claiming that skipping
  the prefix search "can only make this crate accept STRICTLY FEWER
  constraints". It is false once the gate is live: prefix and
  `defaultCase` can both succeed with different assignments (§3 row).
- `use_fo_approx` and its callers already pass the oracle's prefix index;
  unchanged.

### §3 Testing

**Oracle-probed rows.** Each is probed on the pinned oracle in prelude mode
(`prelude` + `import Elab0`, `LEAN_PATH=tests/fixtures/elab`, run from
`/workspace`) before it is written.

- The five gate terms in § Goal, as corpus records (`elab-queries.jsonl`),
  expected to succeed.
- Restored: `p2/app-fn-after-lval` (`(fun x f => f x.1) (Prod.mk Nat.zero
  Nat.zero) Nat.succ`, dropped in P2) and the original `p2/lval-two-binders`
  source (swapped in P2 to dodge this gap).
- **Prefix-vs-default row** (candidate; probe decides):
  `fun (n : Nat) => (fun x y w => w) n Nat.zero (Eq.refl n)`. The body-type
  mvar of `w` is abstracted over `x y` (2 scope args); the application
  produces `?γ n Nat.zero =?= Eq n n` with pattern prefix 1. The prefix
  search assigns `?γ := fun x _ => Eq x x` (binder `(w : Eq x x)`);
  `defaultCase` would give `(w : Eq n n)`. The encoder distinguishes them.
  If the oracle's output differs from this prediction, record the oracle's
  output and re-derive which branch produced it; if no reachable row
  distinguishes the prefix search, the mutations below that need one
  become named seams.

**Unit tests** (`assign.rs`, `mk_binding.rs`, `check_assignment.rs`):
- `elim_mvar` sets `num_scope_args = old + applied`, including a let-skip
  case where `applied < to_revert.len()`, and a nested case (`old > 0`).
- ctxApprox restriction inherits the original's count.
- Each gate: equal count with `const_approx` off → fires; unequal count
  with `const_approx` off → `false`; unequal with `const_approx` on → fires.
- `instantiate_forall`: through a reducible alias (needs the whnf) and the
  too-many-params error.

**Mutations** (each must be killed by a named test or row; run them, do not
trust a brief's prediction):
1. `elim_mvar`: drop `decl.num_scope_args +`.
2. `elim_mvar`: use `to_revert.len()` instead of the applied count.
3. ctxApprox restriction: pass 0.
4. Gate 1: `==` → `true`; → `false`.
5. Gate 2: the count check → always pass; → always fail.
6. Prefix search: go straight to `defaultCase`.
7. Prefix search: skip `is_type_correct`.
8. Prefix search: shortest prefix first.
9. `instantiate_forall`: drop the whnf.

A survivor without a reachable row is recorded in § Landed as a named seam.

**Regressions.** The gate fires on the default profile, so existing smoke
expectations (`StuckCoercion`, `TypeMismatch`, `FunctionExpected`, …) may
move. Probe the oracle before calling any movement a regression (the #65
lesson): a test written while this gap existed can encode the gap. The
corpus floor rises. Gate is `mise run ci` (fmt + clippy included).

## Not in this slice

- The `elim.jsonl` / `structures.jsonl` regen drift left by #65 — its own
  PR.
- `mk_lambda_fvars_with_let_deps`'s let-decl seam — unchanged; its `None`
  routes as the oracle's failure arms do.
- `unstuckMVar` / `isDefEqOnFailure`, `removeUnusedArguments?`, the
  `allowLevelAssignments` seam.
- Any `leanr_elab` source change.

## Plan shape

One plan, one PR, roughly:
1. Field + `mk_aux_mvar_at` parameter + producers (§1), with unit tests and
   mutations 1-3.
2. Gate 1 + gate 2's count check + the five gate rows and the restored
   records (mutations 4-5); triage smoke-test movement against the oracle.
3. `instantiate_forall` + the prefix search + the prefix-vs-default row
   (mutations 6-9).
4. Doc sweep: remove the stale "no `numScopeArgs` analogue" comments
   (`assign.rs` ~94, ~246, ~537), verify every new citation by opening the
   line, § Landed.

## Landed

Commits (`git log --oneline 038fc82..HEAD`, before this docs commit):

```
c2b32dc leanr_meta: processConstApprox longest-prefix search + instantiateForall
d4e3de8 leanr_meta: numScopeArgs opens the constApprox gates (isDefEqMVarSelf, processConstApprox)
0030834 leanr_meta: MVarDecl.num_scope_args, set by elimMVar and the ctxApprox restriction
14d8cff docs: plan citation fix (:977)
28098c5 docs: numScopeArgs implementation plan
740d50a docs: numScopeArgs + processConstApprox prefix search — design spec
```

**Mutations** (each applied, run, reverted):

1. Drop `decl_scope_args +` in `elim_mvar`: killed by `elim_mvar_scope_args_accumulate_across_nested_abstractions`.
2. `applied` replaced by `to_revert.len()`: killed by `elim_mvar_does_not_count_a_skipped_let`.
3. ctxApprox restriction passes 0: killed by `check_mvar_restriction_inherits_num_scope_args`.
4a. Gate 1 (`is_def_eq_mvar_self`), never refuse: killed by unit test `num_scope_args_gates_is_def_eq_mvar_self_on_the_default_profile` only (n=2 case).
4b. Gate 1, refuse whenever `!const_approx`: killed by the same unit test only (n=1 case).
5a. Gate 2 (`process_const_approx`), never refuse: killed by unit test `num_scope_args_gates_process_const_approx_on_the_default_profile` only (n=2 case).
5b. Gate 2, refuse whenever `!const_approx`: killed by the same unit test (n=1) and by all 8 task-2 corpus rows.
6. Prefix branch always `defaultCase`: killed by all four `prefix_search_*` unit tests and by corpus row `nsa/let-prefix-search` (the only row that fails).
7. Drop the `is_type_correct` conjunct: killed by `prefix_search_type_checks_a_ctx_local_prefix` only.
8. `cont` goes straight to `defaultCase` (no shorter-prefix retry): killed by `prefix_search_retries_a_shorter_prefix_before_the_default_case` only. (The plan redefined mutation 8; spec §3's "shortest prefix first" mutation was not run, this retry-removal variant was.)
9. `instantiate_forall` without `whnf`: killed by `instantiate_forall_whnfs_to_find_the_binder`.

Mutations 4a, 4b and 5a are killed only by unit tests; no corpus row
covers gate 1 and the corpus is success-only. Mutations 7 and 8 are
killed only by unit tests written from reading the oracle source
(`ExprDefEq.lean:1303-1306` and `:1293-1298`); they were never
oracle-probed, and no elab row reaches them (`nsa/let-prefix-search`
succeeds at its first prefix, because `n` is outside `?w`'s scope (its lctx), so no shorter-prefix retry is reachable).

**Corpus.** 350 → 359: `nsa/two-binders-snd`, `nsa/two-binders-fst`,
`nsa/fn-after-annotated`, `nsa/lval-after-fn-binder`,
`nsa/fo-before-const`, `nsa/in-lctx-arg-default-case`,
`p2/app-fn-after-lval`, `p2/lval-two-binders-holes` (task 2, 350 → 358)
and `nsa/let-prefix-search` (task 3, 359). `elab-queries.jsonl` gained
9 lines and changed none.

**Smoke-test movement.** None. The only change under
`crates/leanr_elab/tests` is `oracle_elab.rs`'s `CORPUS_FLOOR` (350 → 359).
`synthetic_smoke.rs::stuck_coercion_is_reported_by_the_coe_reporter_arm`
and `binder_smoke.rs::a_have_bound_variable_is_opaque_to_defeq` still pass
unedited (oracle-rejected terms stay rejected).

**Spec corrections.** The § Testing candidate row
`fun (n : Nat) => (fun x y w => w) n Nat.zero (Eq.refl n)` does NOT reach
the prefix branch: `n` is in the mvar's own lctx, so `processAssignment`
stops at arg 0 (`ExprDefEq.lean:1329-1330`; the elaborator's
`quasiPatternApprox := false` is `Elab/Config.lean:62`) and the oracle
gives `(w : Eq n n)` (`defaultCase`). Recorded as
`nsa/in-lctx-arg-default-case`; the discriminating row is
`nsa/let-prefix-search` (oracle: `w : Eq x x`, prefix `[n]` abstracted).
`p2/lval-two-binders` was kept, and its both-holes form added as
`p2/lval-two-binders-holes`, rather than swapping the source back.
Citation fixes found in the sweep: `process_assignment`'s per-argument
cites (`:1320-1321`/`:1322-1323`/`:1327-1328` are on the pin
`:1327-1328`/`:1329-1330`/`:1333-1334`; `:1345` is `:1346`; `:1346-1352`
is `:1347-1354`; the function ends at `:1357`, not `:1359`), the
`isDefEqMVarSelf` call `:1799-1801` is `:1800-1803`, `mkMVarApp` is
`MetavarContext.lean:1090-1097` (not `:1093-1098`), the `elimMVar` kind
split is `:1213` (not `:1212`), `mkFreshExprMVarAt` is
`Meta/Basic.lean:850-860`, and `expandDelayedAssigned?` is `:1702-1725`.

**Open seams.**
- `expandDelayedAssigned?` (`ExprDefEq.lean:1702-1725`, call sites
  `:1885`/`:1887`) is not ported in `is_def_eq_mvar`; delayed assignments
  themselves exist since #62. Previous docs wrongly called it moot.
- Mutations 7 and 8 are pinned only by unit tests (above), not by an
  oracle-probed row.
- Seam R9 (`elim_mvar` uses `decl.kind` where the oracle's
  `mkMVarApp`/`addExprMVarDecl` use `newMVarKind`, `syntheticOpaque` for a
  non-assignable original) now also affects the count. For a
  non-assignable original the oracle's aux mvar counts lets and is
  unassignable; leanr's skips lets (count == applied args) and is
  natural/assignable, so it passes the `numScopeArgs == args.len()` gate on
  the default profile. Low severity (needs `mkLambdaFVars` under
  `withNewMCtxDepth` over an outer-depth mvar). Code site:
  `crates/leanr_meta/src/mk_binding.rs:641` (`let kind = decl.kind;`)
  feeding the count below it. Follow-up: port `newMVarKind`.
- The `elim.jsonl` / `structures.jsonl` regen drift from #65 remains.
