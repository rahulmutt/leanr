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
  `mkMVarApp` (`:1093-1098`) skips non-fvar entries and, for a
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
