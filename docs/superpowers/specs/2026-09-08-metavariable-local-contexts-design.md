# Metavariable local contexts — design spec

## Where this sits

M4b-3 P4 shipped its Meta tier in #37: `Lean/Meta/Coe.lean` is ported 1:1
into `leanr_meta::coe`, the `@[coe_decl]` extension decodes, the coercion
class chain is in both fixture tiers, and ten unit tests pin the
expansion over the `Synth0` environment. P4's elaborator tier — `mkCoe`,
`ensureHasType`, `ensureType`, the `.coe` ladder arm and the six `coe/*`
records — is written but cannot pass, and the reason is not in the
coercion code at all.

**Every metavariable leanr mints is declared with an EMPTY local
context.** The oracle mints under the ambient one. The consequence is
that a metavariable cannot be unified with a `fun`-bound variable, and a
postponed metavariable's payload cannot be resolved once its binder
scope closes. This slice fixes that, and P4's elaborator tier then
resumes unchanged (its plan's tasks 7–10 need no edit).

This is infrastructure, not a coercion detail: every later slice that
elaborates under a binder depends on it.

## The finding, measured

Three probes over the committed `Synth0.olean` fixture, run against the
P4 Meta tier at 28e9d43 (each temporary, each reverted):

| Probe | Result |
| --- | --- |
| `coerce_simple(N.zero, M)` — a constant | `Some` |
| `coerce_simple(x, M)` where `x : N` is a `fun`-bound local | `None` |
| `infer_type(x)` for that same local | `Ok` |
| `is_def_eq(?m, x)` for a fresh `?m : N` | `Ok(false)` |
| `is_def_eq(?m, N.zero)` for a fresh `?m : N` | `Ok(true)` |
| `coerce_to_function(g)` where `g : FnN` is a local | `Some` |
| `coerce_to_sort(s)` where `s : SortN` is a local | `Some` |

The local variable is well formed — `infer_type` answers. What fails is
the *assignment*: `assign.rs::check_assignment_scope_body`'s `FVar` arm
accepts a free variable only when it is one of the abstracted pattern
variables or is visible in the metavariable's own declared local
context. With an empty declared context, an ambient variable is
correctly rejected as out of scope. **The predicate is right; its input
is a lie.**

The last two rows are why the failure went unnoticed for so long, and
they scope the fix: `CoeFun` and `CoeSort` take only types as class
parameters, so their goals never mention a local variable and they work
today. `CoeT α a β` takes the coerced *value* as a parameter. It is the
first goal shape in the project whose class parameters can contain a
local variable, which is why P4 is where this surfaced.

## Why the current state exists

Both minting sites declare an empty context, and both say so:

- `leanr_meta::assign.rs::mk_aux_mvar` — "Always mints with an EMPTY
  lctx", used by `forall_meta_telescope_reducing` for every
  instance-candidate telescope.
- `leanr_elab::elab.rs::mk_fresh_expr_mvar_of_kind` — the same
  `LocalContext::default()`, used for implicit arguments, instance
  arguments, holes and (in P4) coercion metavariables.

The stated reason is that `leanr_kernel::LocalContext` has neither
`Clone` nor any enumeration API, so no caller can copy the ambient
context into a declaration. That is accurate, and it is the one thing
this slice changes in the kernel.

## What the oracle does

- `MetavarDecl.lctx : LocalContext` — "The local context containing the
  free variables that the mvar is permitted to depend upon"
  (`MetavarContext.lean:305-311`).
- `mkFreshExprMVarCore` mints at `(← getLCtx)` and `(← getLocalInstances)`
  (`Meta/Basic.lean:866-867`), through `mkFreshExprMVarAt`
  (`:855-859`) — the ambient context, always.
- `MVarId.withContext` installs a metavariable's own context before any
  work on it: `withMVarContextImp` is
  `withLocalContextImp mvarDecl.lctx mvarDecl.localInstances`
  (`Meta/Basic.lean:2043-2052`).
- The synthetic-metavariable driver runs every arm under it —
  `resumePostponed` is `withRef stx <| mvarId.withContext do …
  withSavedContext savedContext do` (`Elab/SyntheticMVars.lean:32-36`) —
  and the `.coe` arm carries its own (`:545`).
- The scope check reads the declared context:
  `if mvarDecl.lctx.contains fvarId then` in `CheckAssignmentQuick.check`
  (`Meta/ExprDefEq.lean:1060`), and `containsFVar` in the slow path
  (`:854`).

So the oracle's contexts are truthful at mint time and reinstalled at
use time. leanr has neither half.

## What this ships

1. `leanr_kernel::LocalContext` derives `Clone`.
2. A `LocalCtxSnapshot` in `leanr_meta` — the context plus the parallel
   name index, shared behind an `Arc` — and a one-per-scope-change cache
   so that minting N metavariables at one binder depth costs one copy.
3. `MVarDecl.lctx` becomes that snapshot; both minting sites take the
   ambient one.
4. `MetaCtx::with_mvar_context`, and the synthetic-metavariable ladder
   running each arm under it.
5. The three probes above become permanent tests.

**Stated non-shipping.** No `localInstances` (leanr has no local-instance
concept; instances come from the environment extension) — named seam. No
`MetavarDecl.depth` model, which stays where it is. No `isSubPrefixOf`:
the `MVar` arm of the scope check keeps its existing tier-1 seam. No
`ctxApprox` slow rewriting path. None of these block P4.

## Global constraints

- **Pinned oracle `leanprover/lean4:v4.33.0-rc1`.** Never bumped.
- **The kernel edit is exactly one derive.** `LocalDecl` already derives
  `Clone`; `LocalContext` is `Vec<LocalDecl>` plus a `HashMap`, so the
  derive is mechanical. It adds no logic, changes no function body and
  adds no dependency, so it moves no soundness surface — the sense in
  which `AGENTS.md` asks the kernel to stay minimal. Any further kernel
  change is out of scope for this slice.
- **Both corpora stay byte-identical**: 107 elaboration records, 24
  compared synthesis records. This is the gate that matters here, and it
  is a sharp one — see § Risk.
- **`mise run ci` gates fmt and clippy**, not only tests.
- **Every discriminator is measured**: each mechanism gets a test that
  goes red when the mechanism is mutated, and the mutation is applied
  and recorded.

## Architecture

### The snapshot

`MetaCtx` already keeps `lctx: LocalContext` beside `local_names`, "an
index parallel to `lctx`'s own decl list, one entry per decl", with a
lockstep invariant asserted at every `lctx_checkpoint`/`lctx_restore`.
That parallel index exists precisely because `LocalContext` cannot be
enumerated, and it is the reason a snapshot must carry both halves:

```rust
pub struct LocalCtxSnapshot {
    lctx: LocalContext,
    local_names: Vec<(Option<NameId>, ExprId)>,
}
```

(`local_names`'s element type is `MetaCtx`'s own, unchanged.) `MetaCtx`
caches `Option<Arc<LocalCtxSnapshot>>`, invalidated by
`push_local_decl`, `push_let_decl` and `lctx_restore`. `current_lctx()`
returns the cached `Arc`, building it on first use after a change. A
candidate telescope that mints three metavariables at one depth pays one
copy; a Mathlib-scale synthesis sweep pays one copy per binder scope
entered, not one per metavariable.

### Minting

`mk_aux_mvar` and `mk_fresh_expr_mvar_of_kind` both store
`ctx.current_lctx()` in the declaration. That is the whole behavioural
change on the minting side, and it is what makes the scope check
truthful.

### The scope check does not change

`check_assignment_scope_body`'s `FVar` arm already transcribes
`CheckAssignmentQuick.check`'s own test (`ExprDefEq.lean:1060`). It
starts receiving a real context and starts answering correctly. Leaving
the predicate alone is deliberate: the bug was never in the check, and
rewriting it would be the grafting mistake its own doc comment already
warns about.

### `with_mvar_context`

```rust
pub fn with_mvar_context<R>(&mut self, mvar_id: MVarId, f: impl FnOnce(&mut Self) -> R) -> R
```

Swaps the ambient snapshot for the metavariable's, runs, restores —
both halves together, so the lockstep invariant holds throughout.
Mirrors `withMVarContextImp` (`Meta/Basic.lean:2043-2045`) minus
`localInstances`.

The ladder then runs each pending arm under it, as
`resumePostponed` and the `.coe` arm both do
(`Elab/SyntheticMVars.lean:32-36`, `:545`). This is the half that fixes
the postponement failure: a `.coe` metavariable registered inside a
binder is resumed with that binder back in scope, so its stored payload
still types.

## Rejected alternatives

- **Store a depth instead of a context.** `restore` truncates and later
  pushes reuse indices with fresh variable ids, so a stale metavariable
  would compare against a different variable at the same index and
  wrongly accept it. Unsound exactly where postponement makes it
  reachable.
- **Store a watermark of the fresh-variable counter.** Sibling binders
  break it: a variable popped before the metavariable was minted still
  has a lower counter, so it would be accepted though it was never in
  scope.
- **Store only the set of visible variable ids, no kernel change.** This
  fixes the scope check without touching the kernel, but carries no
  types, so it cannot reinstall a context and does not fix
  postponement. Half a fix for the same disruption.
- **Clone per mint rather than per scope change.** Correct but pays
  O(depth) on the hottest path in the project (instance search).

## Plan decomposition

Five tasks, each with its own gate; no commit leaves either corpus red.

| Task | Content |
| --- | --- |
| 1 | `Clone` on `LocalContext`, with a test that a clone is independent of its source. |
| 2 | `LocalCtxSnapshot`, the cache and its invalidation, `MVarDecl.lctx`, `mk_aux_mvar` minting ambient. Test: `is_def_eq(?m, x)` succeeds for a local `x`; both corpora unchanged. |
| 3 | `with_mvar_context`, with a test that installing and restoring holds the lockstep invariant. |
| 4 | `mk_fresh_expr_mvar_of_kind` mints ambient; the ladder runs each arm under `with_mvar_context`. Test: a synthetic metavariable's payload still types after its binder scope closes; both corpora unchanged. |
| 5 | The probes become permanent tests: `coerce_simple` on a local answers `Some` and expands to the instance function. |

## Risk

Making the scope check truthful admits assignments it previously
rejected, so this slice can in principle move a committed record. It
should not: every one of the 107 elaboration records agrees with the
oracle today, and the oracle's contexts are truthful, so an agreeing
result cannot depend on leanr rejecting an assignment the oracle
accepts. **A record that moves therefore means it was agreeing by
accident** — investigate it, and never re-baseline.

## Verification

- `mise run ci` green.
- `mise run meta:fast` and the elaboration gate: 107 and 24, byte-identical.
- `is_def_eq(?m, local)` succeeds; `is_def_eq(?m, out-of-scope local)`
  still fails — the check must get *truthful*, not permissive.
- A postponed synthetic metavariable resumed after its binder closes
  resolves its payload.
- `coerce_simple` on a local variable expands to the instance function,
  with no `CoeT.coe` and no projection node in the result.

## Next step

P4's elaborator tier resumes at its existing plan's task 7. Its wiring
is preserved on `m4b3-p4-task7-wip` and needs no redesign — the four
records it could not pass are blocked by this slice alone, and the two
records after it were never blocked at all.
