# M4b-3 — the application elaborator, the synthetic-mvar fixpoint, coercions and literals — design spec

## Where this sits

M4b-1 shipped `leanr_elab`: the crate seam, the
`SyntaxKind → elaborator` dispatch table, the `TermElabM` state over
`leanr_meta`'s `MetaM` core, the differential oracle harness
(`oracle_elab.rs` + `elab-queries.jsonl`), and the leaf elaborators.
M4b-2 shipped the binder forms across three plans (#28 `forall`/
`arrow`/`depArrow`, #29 `fun`, #30 `let`/`have`) and — per its own
§ Amendment — deliberately shipped **no** scheduler: no closed term in
M4b-2's grammar creates a synthetic mvar, so a fixpoint step would have
been a pure no-op on every corpus entry, and the whole ladder was
deferred to the slice that first produces one from source.

That slice is this one. M4b-3 is where the deferrals accumulated by
M4b-1 and M4b-2 come due, because they are all downstream of one
construct: **application**.

| Slice | Content |
|---|---|
| M4b-1 (shipped, #27) | crate skeleton, dispatch, oracle harness, leaf elaborators |
| M4b-2 (shipped, #28/#29/#30) | binder elaborators `forall`/`arrow`/`depArrow`/`fun`/`let`/`have` — no scheduler |
| **M4b-3 (this spec)** | `elabApp` + the `synthesizeSyntheticMVars` fixpoint + coercion insertion + num/char/scientific literals + implicit-binder and argument breadth |
| M4b-4 | `elabAsElim`, dot notation (`proj`/`dotIdent`/`pipeProj`), `binop%`, anonymous constructor `⟨⟩` |
| later M4 | macro expansion in dispatch, `by` tactic blocks, `show`, `suffices`, structure instances, match/equation compiler, `do` |

Pinned oracle: `leanprover/lean4:v4.33.0-rc1` (`lean-toolchain`). Every
citation below is against that toolchain's
`src/lean/Lean/Elab/App.lean`, `src/lean/Lean/Elab/SyntheticMVars.lean`,
`src/lean/Lean/Elab/BuiltinTerm.lean`,
`src/lean/Lean/Elab/Term/TermElabM.lean`, and
`src/lean/Lean/Meta/Coe.lean`. The pin is not bumped in this slice.

## What M4b-3 ships — and the stated non-shipping

Like all of M4a and M4b so far, **M4b-3 does not ship independently
useful functionality**, and this is recorded rather than papered over.
There is still no command layer, so nothing elaborates a `def`. What
M4b-3 delivers is the term elaborator's fidelity core: after it, the
elaborator handles the construct that every real Lean term is built
from, with implicit and instance arguments inserted, coercions applied,
numerals defaulted, and postponed work resumed — each differentially
verified against the oracle. The M4b-1 spec named `elabApp` and the
fixpoint as *the* fidelity risk of all of M4b; this is the slice that
pays it down.

## Two structural findings that shape the slice

**1. `elabIdent` is `elabAppAux`.** `App.lean:2246` registers the `ident`
term elaborator as `elabAtom`, which is `elabAppAux stx #[] #[]`
(`App.lean:2245`) — a bare identifier is a **zero-argument application**
in the oracle, so implicit arguments are inserted for it (`List.nil`
against expected `List Nat` elaborates to `@List.nil Nat`). M4b-1's
standalone leaf `ident` elaborator is therefore a simplification whose
corpus was biased toward monomorphic constants (the M4b-1 spec says so).
M4b-3 **retires** that path rather than bypassing it: its
constant-resolution and universe-instantiation logic moves into
`elabAppFn`'s ident case, where the oracle puts it.

**2. `char` is not an instance application.** The M4b-1 spec deferred
`num` *and* `char` to M4b-3 on the stated grounds that both "elaborate
through an application requiring instance synthesis and default
instances". That is true of `num` and false of `char`:
`BuiltinTerm.lean:248-251` is `mkApp (Char.ofNat) (mkRawNatLit ...)` —
no instance, no expected-type consultation at all. Recorded here as a
spec correction; `char` is a two-line arm, not a synthesis client.

## Global constraints

- **Kernel is byte-untouched.** `leanr_kernel` continues to depend on no
  workspace crate, and no existing kernel function is modified.
  `instantiateBetaRevRange` (needed by `State.getFType`) is built from
  the existing `leanr_kernel::subst::instantiate_rev` at the
  `leanr_meta` layer, not added to the kernel.
- **`leanr_olean` gains two additive env-extension decoders**, not a
  behavior change: `classExtension` (P2) and the `coe_decl` tag
  attribute (P4). Precedent: M4a plan 4 PR-A, which decoded the
  instance / default-instance / projection-fn extensions the same way.
  Both are untrusted-input parsers and must never panic on arbitrary
  bytes (`docs/THREAT_MODEL.md`); no existing decode path changes.
- **`leanr_meta/src` constraint — widened once, deliberately.** M4b-1
  and M4b-2 allowed only purely additive, TCB-neutral, behavior-neutral
  public *accessors* on `leanr_meta`. Plans P1–P3 stay inside that rule
  (see § Accessor ledger). **P4 widens it**: coercion is Meta-level
  machinery in the oracle (`Lean/Meta/Coe.lean`), and P4 adds it as new
  modules `leanr_meta/src/coe.rs` and `leanr_meta/src/transform.rs`.
  These are new files: no existing `leanr_meta` path changes behavior,
  no kernel change, and the 1:1 file correspondence with the oracle is
  what keeps fidelity auditing cheap. Any *non-additive* or
  behavior-changing `leanr_meta` change remains flagged and out of
  scope.
- **Named-seam discipline.** Every unregistered kind and every guarded
  shape returns `ElabError::UnsupportedSyntax` naming the slice that
  owns it — never a panic, never a wrong `ExprId`, never a silent
  divergence. Where the oracle would do something we do not implement,
  we detect the *shape it would have taken* and error; a fall-through
  that quietly produces a different term is the failure mode this
  discipline exists to prevent (§ Seams).
- **Oracle discipline.** Correctness is byte-for-byte agreement with the
  pinned oracle's canonical `Expr` via `oracle_elab.rs`. No new nightly
  workflow; no Mathlib-scale elaboration sweep in this slice (§
  Verification).

## Architecture

### The entry-point pipeline

M4b-2's entry point was `elab_term_ensuring_type → instantiate_mvars`
with no scheduler. M4b-3 lands the shape the M4b-2 spec named as
eventual:

```
elab_term(elem, expected)              // dispatch → leaf / binder / app
  → synthesize_synthetic_mvars(.no)    // the fixpoint ladder
  → instantiate_mvars(e)               // final substitution
```

`.no` is the oracle's `PostponeBehavior.no`, i.e.
`synthesizeSyntheticMVarsNoPostponing` (`SyntheticMVars.lean:649`) —
the strictest variant, which forces default instances, then reports
stuck synthetic mvars, then drains postponed universe constraints.
`tests/fixtures/elab/dump_elab.lean` changes to match, once, in P2.

A bare `_` is a **natural**, not synthetic, mvar, so
`reportStuckSyntheticMVars` does not touch it and the committed
`hole/bare` → `{"k":"mvar","i":0}` record is expected to survive
unchanged. That is an argument, not evidence: P2's final task
regenerates every fixture and gates on `git diff --exit-code` over the
JSONL, landing the empty diff as proof that adding the fixpoint is a
no-op on all pre-existing records.

### Plan decomposition

Five plans, each a single PR with its own hermetic oracle tier
extending `oracle_elab.rs` + `elab-queries.jsonl`.

| Plan | Content | First oracle-verifiable thing |
|---|---|---|
| **P1** application foundation | `expandApp`, `Arg`/`NamedArg`, the `ElabAppArgs` state machine (explicit / implicit / strictImplicit arms, `addNewArg`, `fType` normalization), `propagateExpectedType`, `etaArgs`, `finalize` (no coercion), overload single-candidate guard, implicit-lambda guard; rewire `ident` / `@` / `.{u}` through `elabAtom` | polymorphic applications without instance args; eta cases via named args |
| **P2** instance args + the fixpoint | `instMVars`, `synthesizeAppInstMVars`, `.typeClass` registration, the full escalation ladder, `mayPostpone` / `withoutPostponing`, `mvarErrorInfos`, `reportStuckSyntheticMVars`, `classExtension` outParam decode + the `resultTypeOutParam?` support, the entry-point pipeline change; M4b-2's `fun` postponement seam goes live | typeclass applications; postponed-then-resumed terms |
| **P3** literals + defaults | `num` (`OfNat`), `char` (`Char.ofNat`), `scientific` (`OfScientific`), `synthesizeUsingDefault` / `synthesizeSomeUsingDefaultPrio` | `42`, `(42 : Int)`, `'a'`, `1.5` |
| **P4** coercions | `coe_decl` tag-extension decode, `expandCoe`, `coerceSimple?` / `coerceToFunction?` / `coerceToSort?` in new `leanr_meta/src/coe.rs`, `mkCoe` + `.coe` mvar case + `ensure_has_type` rewire, monad-lift shape guard | `(n : Int)` where `n : Nat`; a `CoeFun` application |
| **P5** binder + argument breadth | implicit / strictImplicit / instImplicit binders for `fun`/`let`/`have`, `fun`'s `optType`, `optParam` defaults, the `autoParam` arm, `..` ellipsis, real implicit-lambda insertion replacing P1's guard | `fun {α} => …`; signatures with `optParam`; `f ..` |

**Ordering rationale.** P1 before P2 because the state machine is what
first *creates* the synthetic mvars the fixpoint drains — the M4b-2
amendment's condition ("each ladder field gets a source producer and
differential coverage in the slice that builds it") holds only in that
order. P3 after P2 because `num`'s default-instance fallback *is* a
fixpoint rung. P4 after P2 because a stuck coercion registers a `.coe`
synthetic mvar. P5 last because it is breadth over a verified core, so
it can absorb schedule pressure without leaving a divergent path on
main.

### P1 — the application machinery

Module layout under `leanr_elab/src/app/`: `expand.rs` (`expandApp` →
`(f, namedArgs, args, ellipsis)`, the `Arg`/`NamedArg` types),
`state.rs` (`Context` + `State`), `args.rs` (parameter-kind arms and the
main loop), `propagate.rs`, `finalize.rs`, `overload.rs`. No file over
~400 lines; M4b-2's 718-line `binder.rs` is the crate's current maximum
and is not a target to beat.

The oracle's `abbrev M := ReaderT Context (StateRefT State TermElabM)`
(`App.lean:229`) becomes one struct rather than a transformer stack:

```rust
struct AppElab<'a, 'e> {
    ctx: Context,                    // immutable after construction
    st: State,                       // mutable
    elab: &'a mut TermElabM<'e>,
}
```

Each `private def foo : M α` becomes a method on `AppElab`. `Context`
carries `ellipsis`, `explicit`, `result_is_out_param_support`,
`num_implicit_params` (`App.lean:132-175`); `State` carries `f`,
`f_type`, `f_args`, `args`, `named_args`, `expected_type`, `eta_args`,
`to_set_error_ctx`, `inst_mvars`, `propagate_expected`,
`result_type_out_param`, `found_named_args` (`App.lean:178-227`).

**Every field exists from P1**, including the ones a given plan does not
yet drive. A missing *arm* is a named seam; a missing *field* is a
silent fidelity hole, because the oracle's control flow branches on
these fields in places far from where they are set.

`State::param_idx` is `f_args.len()`; `State::get_f_type` is
`instantiate_beta_rev_range(f_type, 0, f_args)` (`App.lean:232-237`).

**Dispatch rewiring.** `Lean.Parser.Term.app`, `<ident>`,
`Lean.Parser.Term.explicit`, and `Lean.Parser.Term.explicitUniv` route
to `elab_app`/`elab_atom`. M4b-1's `builtin/ident.rs` leaf elaborator is
deleted. Its committed oracle records must stay byte-identical across
the rewiring — a task-level gate, not a hope.

`Lean.Parser.Term.proj`, `pipeProj`, `dotIdent`, `namedPattern` and
`choice` are *not* rewired: in the oracle they reach `elabAppFn`'s LVal
machinery (`resolveLValAux` / `addLValArg`), which is the dot-notation
subsystem the roadmap assigns to M4b-4. They remain named seams.

**Overload resolution** is a shape guard. `elabAppFn` returns a
candidate vector; P1 asserts `len == 1` and otherwise errors
`UnsupportedSyntax("overloaded application requires namespace/alias
resolution")`. `getSuccesses` / `mergeFailures` / "Ambiguous term"
(`App.lean:2190-2217`) are unreachable while `resolve_global` resolves
only exact names, so they are not built speculatively.

**`propagateExpectedType`** (`App.lean:449-609`) and **`etaArgs`**
(`App.lean:206`, consumed at `App.lean:621-624`) are both in P1, not
deferred: each silently changes the emitted `Expr` for ordinary
applications. Without propagation, `(f x : T)` unifies in the wrong
order and produces different mvar assignments; without `etaArgs`, an
under-applied function with named args emits an application where the
oracle emits a lambda. Both are oracle-visible on trivial corpus terms,
so deferring either means shipping known-divergent output.

### P2 — the synthetic-mvar ladder and fixpoint

New module `leanr_elab/src/synthetic.rs`.

**Ladder state.** `TermElabM` grows `pending_mvars: Vec<MVarId>`,
`synthetic_mvars: HashMap<MVarId, SyntheticMVarDecl>`,
`mvar_error_infos`, and the reader flag `may_postpone`.
`SyntheticMVarKind` gets all four oracle variants —
`TypeClass`, `Coe`, `Postponed`, `Tactic`
(`TermElabM.lean:65-99`) — from the start, even though P2 produces only
`TypeClass` and `Postponed` (P4 produces `Coe`; P5 registers `Tactic`).

**`synthesizeSyntheticMVarsStep`** (`SyntheticMVars.lean:573-602`) is
transliterated exactly, because its ordering is fidelity-critical and
easy to get subtly wrong. `pending_mvars` is a list whose **head is the
most recent**. The step clears it, processes the snapshot with
`filterRevM` — i.e. **in creation order**, not list order — and
re-merges as **`new_pending ++ still_unsolved`**, so mvars created
*during* the step land before the leftovers. Progress is
`count_before != still_unsolved.len()`, not "any succeeded". A version
that reverses the merge order still terminates and still looks green on
simple corpus entries, then diverges on nested applications, so P2
gates it with a term that creates a pending mvar during a resume.

**The escalation ladder** (`SyntheticMVars.lean:611-648`): five rungs,
tried in this exact order, looping back to rung 1 on any success.

1. `step(postpone_on_error: false, run_tactics: false)`
2. *(rungs 2-5 only when `postpone != .yes`)*
   `without_postponing step(postpone_on_error: true, run_tactics: false)`
3. `synthesize_using_default`
4. `without_postponing step(postpone_on_error: false, run_tactics: false)`
5. `step(postpone_on_error: false, run_tactics: true)`

then `report_stuck_synthetic_mvars` when `postpone == .no`, then
`process_postponed_universe_constraints`. `PostponeBehavior` is the
oracle's three-valued `yes` / `no` / `partial`.

**Per-mvar dispatch** (`SyntheticMVars.lean:540-571`):

- `TypeClass` → `synthesizePendingInstMVar`. leanr's
  `MetaCtx::synth_instance` already returns
  `Err(MetaError::IsDefEqStuck)` for a stuck search rather than
  collapsing it to failure, which is exactly the oracle's
  `trySynthInstance` `.undef`. The elab layer maps
  `Err(IsDefEqStuck)` → "not ready yet" and `Ok(None)` → a real
  synthesis failure. Preserving that distinction is the whole reason
  postponement works.
- `Postponed` → `resumePostponed` (`SyntheticMVars.lean:32-71`),
  re-running `elab_term` under the saved context. This is where M4b-2
  plan 2's `fun` postponement seam becomes live code.
- `Coe` → P4.
- `Tactic` → the seam. Rung 5 (`run_tactics: true`) reaches it and
  errors `UnsupportedSyntax("autoParam tactic execution requires the
  `by` elaborator")`. A silent `false` here would make the ladder report
  "stuck" for a reason the user cannot see.

**`SavedContext`** is the local context plus `may_postpone` plus the
level/mvar checkpoint. `universeConstraintsCheckpoint` — which wraps all
of `elabApp` (`App.lean:2239`) — maps onto leanr_meta's existing
postponed level-constraint queue (`metactx.rs:104`) and
`process_postponed` (`level.rs:708`), exposed additively.

**The outParam support** (`Context.resultIsOutParamSupport`,
`State.resultTypeOutParam?`, `App.lean:141-175` and `610-700`) lands
here too, because it calls `synthesizeSyntheticMVarsUsingDefault`, which
P2 builds anyway. When an application's result type is the `outParam` of
a *local* instance, `finalize` eagerly applies default instances; this
changes the emitted term for `getElem`-shaped code. Detecting it needs
class outParam positions, so P2 adds a **`classExtension` decode**
(`ClassEntry` = name + outParam positions) to `leanr_olean` — the same
shape as M4a plan 4 PR-A's instance decode, and small. The alternative
of leaving `result_is_out_param_support = false` was rejected: it is a
silent divergence rather than a named seam, and a conservative
over-approximation would reject most ordinary typeclass applications and
gut P2's own corpus.

### P3 — literals and default instances

Three dispatch arms (`BuiltinTerm.lean:210-252`):

- **`num`** — `mkFreshTypeMVarFor(expected)` (fresh type mvar, then
  `discard <| isDefEq expected typeMVar`; a *failed* unification is
  deliberately ignored, `BuiltinTerm.lean:205-208`), `getDecLevel`, an
  instance mvar for `OfNat.{u} ?α (rawNatLit v)` registered as
  `.typeClass`, emitting `@OfNat.ofNat.{u} ?α (rawNatLit v) ?inst`, then
  `registerMVarErrorImplicitArgInfo`. The two `getDecLevel` failure
  branches — expected type is a `Prop`, expected type is
  universe-polymorphic — are distinct oracle errors and stay distinct.
- **`char`** — `@Char.ofNat (rawNatLit c)`. No instance, no expected
  type (§ Two structural findings).
- **`scientific`** — the `num` shape against `OfScientific`, emitting
  `@OfScientific.ofScientific.{u} ?α ?inst (rawNatLit m) sign
  (rawNatLit e)`. Included rather than seamed because leanr's parser
  already registers `Prim::ScientificLit` in term position
  (`leanr_syntax/src/builtin/term.rs:216`), so the kind is reachable
  from source. This is a small stated addition to the roadmap's
  "num/char literals" wording.
`rawNatLit` (`BuiltinTerm.lean:231-235`) is **excluded**: leanr's parser
registers no such kind, so no source term can reach it. `mkRawNatLit`
itself — the `Expr` constructor the three arms above all use — is of
course in scope.

**`synthesizeUsingDefault`** (`SyntheticMVars.lean:113-230`) is the rung
that makes `42 : Nat` work, and its ordering is as delicate as the
ladder's. Two things are transliterated verbatim: default instances are
tried **priority-set by descending priority**, and within a priority
`synthesizeSomeUsingDefaultPrio` walks `pendingMVars.reverse` —
**reverse creation order**, with the oracle's own comment explaining why
(otherwise `toString 0` fails with an `OfNat String ?_` error). On
success the queue is rebuilt as `pendingMVars.reverse ++
pendingMVarsNew`. Applying a default instance then recursively
synthesizes the instance-implicit binders it introduced
(`synthesizePending` → `synthesizeUsingInstances` →
`synthesizeSomeUsingDefault?`) — a nested fixpoint, not a single pass.
`withAssignableSyntheticOpaque` is required (a default instance must be
able to assign a `syntheticOpaque` outParam mvar) and lands as an
additive `MetaCtx` config toggle.

### P4 — coercions

New `leanr_meta/src/coe.rs`, mirroring `Lean/Meta/Coe.lean`:

- **`expand_coe`** (`Coe.lean:44-70`) — a `transform` traversal under
  `withReducibleAndInstances`, unfolding `@[coe_decl]`-tagged constants
  via `unfoldDefinition?` then `headBeta`, recording applied `Coe.coe`
  instance names, and recursing through projection functions
  (`recProjTarget`). The generic traversal lands as
  `leanr_meta/src/transform.rs`.
- **`coerce_simple?`** (`Coe.lean:78-97`) — synthesize
  `CoeT.{u,v} α e β`, build `CoeT.coe …`, `expand_coe`, then **verify**
  the result's inferred type is defeq to the expected type; a mismatch
  is a hard error, not a silent pass.
- **`coerce_to_function?`** (`CoeFun`) and **`coerce_to_sort?`**
  (`CoeSort`). `CoeFun` is not optional-adjacent: `elabApp` itself needs
  it when the function's type does not reduce to a `forall`.
- **`coerce?`** preserving the dispatch order of
  `coerceCollectingNames?` (`Coe.lean:259-265`): **monad-lift →
  CoeFun-when-expected-is-forall → CoeT**.

Three supporting pieces:

1. **`coe_decl` decode** in `leanr_olean` — a `TagAttribute`
   extension (a name set), smaller than M4a plan 4's instance decode.
   Without it `expand_coe` is a no-op and every coercion emits
   `CoeT.coe` applications where the oracle emits the unfolded
   function: a guaranteed, silent, corpus-wide divergence. It is a P4
   prerequisite task, not a follow-up.
2. **`mkCoe` and the `.coe` mvar** in `leanr_elab`
   (`TermElabM.lean:1294-1332`, `SyntheticMVars.lean:544-561`). On
   `.undef` — a stuck `CoeT` synthesis — create a `syntheticOpaque`
   mvar and register `.coe`. The fixpoint's `Coe` case first re-tries
   `isDefEq` under `withDefault` (mvar assignments and defaulting may
   have made the types equal), then `coerce?`, with an `occursCheck`
   before each assign. `ensure_has_type` / `elab_term_ensuring_type`
   stop erroring on a defeq mismatch and route through `mkCoe` — a
   behavior change to shipped M4b-1 code, so the existing
   `TypeMismatch` records are re-verified, not assumed.
3. **The monad-lift shape guard.** `coerceMonadLift?`
   (`Coe.lean:201-248`) is not implemented, but it is tried *first* in
   the oracle, so silently skipping it would let a term the oracle
   coerces via `liftCoeM` fall through to `CoeT` and emit a different
   term. The guard detects that shape — expected type an application of
   a monad-ish head, source coercible under `MonadLiftT` — and errors
   `UnsupportedSyntax("monad-lift coercion requires the do-notation
   slice")`.

### P5 — binder and argument breadth

- **Binder info breadth**: `fun`'s implicit / strictImplicit /
  instImplicit `funBinder` forms and its `optType`; `let`/`have`'s
  bracketed binders. Reuses M4b-2's binder machinery with the remaining
  `BinderInfo` variants.
- **`optParam`**: when the parameter type is `optParam α d` and no
  positional argument remains, `d` is instantiated and added as the
  argument — not a fresh mvar.
- **`autoParam`**: strip the wrapper; an explicitly-supplied argument
  elaborates normally (fully oracle-verifiable); an omitted one creates
  the `.tactic` synthetic mvar exactly as `App.lean:846` does, with
  execution left to P2's seam. Full autoParam would pull in the `by`
  elaborator and the tactic framework, which the roadmap assigns to a
  later M4 slice.
- **`..` ellipsis**: disables eta-expansion; missing arguments become
  `_`.
- **Implicit-lambda insertion**: not app-local. It lives in
  `elabTermAux` via `useImplicitLambda` (`TermElabM.lean:1743`,
  `1823-1880`), affects every term elaborated against an
  implicit-`forall` expected type, and `@` exists partly to disable it
  (`App.lean:2268-2270`). That path becomes reachable in **P1**, the
  moment ascription starts supplying expected types, so **P1 ships the
  guard** (detect the `useImplicitLambda` condition → `UnsupportedSyntax
  ("implicit lambda insertion — M4b-3 P5")`) and **P5 replaces the guard
  with the implementation**. Guard-in-P1, feature-in-P5 is the only
  ordering in which no plan ships a silent divergence.

## Accessor ledger (`leanr_meta`)

Additive, TCB-neutral, behavior-neutral public accessors, by plan:

| Plan | Additions |
|---|---|
| P1 | `instantiate_beta_rev_range` — and only this one. `Expr` destructuring (`fTypeIsForall`, `bindingDomain!`, `getAppFn`) uses the already-public `Store::expr_node` (`leanr_kernel/src/bank/terms.rs:615`) via `mctx.store()` + `view.store`, and `whnfForall` composes from the public `MetaCtx::whnf`, so neither needs an accessor. `instantiate_beta_rev_range` does: its beta step needs `whnf.rs`'s `beta_rev`/`head_beta`, which are `pub(crate)`. |
| P2 | `process_postponed` + the postponed-queue checkpoint, `default_instances` (currently `pub(crate)`, `instances.rs:520`), `with_assignable_synthetic_opaque` config toggle |
| P3 | `get_dec_level`, `mk_raw_nat_lit` |
| P4 | `unfold_definition`, `get_level`, `whnf_r`, `mk_arrow`, and the **new modules** `coe.rs` + `transform.rs` (§ Global constraints — the one deliberate widening) |
| P5 | none expected |

## Error handling

`ElabError` grows one variant per real oracle failure mode: stuck
synthetic mvar, synthesis failure with its extra message,
numeral-is-not-data (both `getDecLevel` branches), coercion failure,
ill-formed syntax. Every seam is a distinct `UnsupportedSyntax` message
naming the owning slice.

`MetaError` propagates rather than collapsing. In particular
`IsDefEqStuck` means *postpone*, never *fail*; and the deterministic
`StepBudgetExhausted` / `DepthBudgetExhausted` budgets surface as
elaboration errors rather than hangs. No path panics.
Untrusted-input discipline is unchanged: the only new decoders are P2's
`classExtension` and P4's `coe_decl` name set, both following the
existing env-extension decode pattern, which must never panic on
arbitrary bytes (`docs/THREAT_MODEL.md`).

## Verification

Three tiers, no new nightly workflow.

1. **The hermetic differential gate** remains the only correctness
   oracle: `oracle_elab.rs` replays `elab-queries.jsonl` against
   committed `.olean` fixtures and compares byte-for-byte on the
   canonical `Expr`. Each plan extends the corpus.
   **Expected types come from source ascription.** The dumper keeps its
   one-term-per-record contract; `(f x : T)` induces an expected type
   through `typeAscription`, which M4b-1 already ships. This matters
   because `propagateExpectedType`, coercion insertion and numeral
   defaulting are all *unreachable* under the dumper's current pinned
   `expectedType? := none`, and inducing them from real syntax tests the
   path leanr will actually see rather than an entry point no source
   term reaches until the declaration layer lands.
2. **Ordering unit tests.** Three orderings are fidelity-critical but
   invisible on simple corpus terms: the step's
   `new_pending ++ still_unsolved` merge, `filterRevM`'s creation-order
   processing, and `synthesizeSomeUsingDefaultPrio`'s reverse-creation-
   order walk. Each gets a direct unit test constructing the queue
   state, in the `binder_smoke.rs` style. The corpus cannot be relied
   on to catch these.
3. **Seam audit per plan**, in M4b-1's Task-7 style: enumerate every
   unregistered kind and every guarded shape and assert each returns a
   named `UnsupportedSyntax` rather than a wrong `ExprId`.

`mise run ci` — which gates `cargo fmt --check` and clippy, not only
tests — runs before every commit and push.

## Seams (shape-guarded, not fall-through)

Each of these detects the shape the oracle would have handled and
errors, rather than proceeding to emit a different term:

| Seam | Owner |
|---|---|
| overloaded application (candidate count > 1) | the slice that grows `resolve_global` |
| implicit-lambda insertion (P1 only; P5 implements) | M4b-3 P5 |
| `.tactic` synthetic mvar execution | later M4 (`by`) |
| monad-lift coercion shape | the do-notation slice |
| `proj` / `pipeProj` / `dotIdent` / `namedPattern` / `choice` | M4b-4 |

## Out of scope (each names the slice that owns it)

- `matchAlts` / pattern matching, `elabAsElim`, dot notation and the
  LVal machinery (`proj` / `pipeProj` / `dotIdent` / `namedPattern` /
  `choice`), `binop%`, anonymous constructor `⟨⟩` — **M4b-4**
- overload resolution (`getSuccesses` / `mergeFailures` / "Ambiguous
  term") and namespace-prefix / alias / `export` / `_root_` resolution —
  the slice that grows `resolve_global`
- macro expansion in dispatch, `by` tactic blocks and `.tactic` mvar
  execution, `show` (both arms), `suffices`, `let rec` /
  `let_recs_to_lift` producer, `letI` / `haveI` / `let_fun` /
  `let_delayed` / `let_tmp` — **later M4**
- monad-lift coercion (`coerceMonadLift?`, `Lean.Internal.coeM` /
  `liftCoeM`, the `autoLift` option) — the **do-notation** slice
- `letPatDecl` / `letEqnsDecl`, `letConfig` items, and `rawNatLit` — not
  ported by leanr's parser, so no slice owns them until it does
- a Mathlib-scale elaboration discovery sweep — needs the
  declaration/command layer, so no nightly workflow changes here
- `lean-toolchain` pin bump — milestone boundaries only

## Next step

Invoke the writing-plans skill to produce the M4b-3 **plan 1**
implementation plan (application foundation). Plans 2-5 get their own
implementation plans as each predecessor lands, mirroring M4b-2's
rhythm.
