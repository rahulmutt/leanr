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

## Amendment (2026-07-27, post-plan-1): P2 splits into P2a and P2b

Reality-checking this spec's original § P2 against the shipped plan-1
code produced three scoping decisions, recorded here and folded into the
sections below (which are now § P2a and § P2b).

**1. P2 splits.** As written, § P2 is a single PR carrying the ladder
state, `synthesizeSyntheticMVarsStep` and the five-rung escalation,
instance arguments, `mayPostpone` threading, stuck reporting, the
entry-point pipeline change, *and* the `classExtension` outParam decode
— comparable in weight to P1's nine tasks, across `leanr_elab`,
`leanr_meta`, `leanr_olean` and the fixture pipeline at once. M4b-2 met
the same pressure by splitting into three plans. It splits here into
**P2a** (ladder + instance arguments) and **P2b**
(`classExtension` + `resultTypeOutParam?`).

The original ordering rationale — "leaving `result_is_out_param_support
= false` is a silent divergence rather than a named seam" — no longer
binds: P1 shipped it as a *named*, shape-guarded seam
(`app/args.rs:499`, `app/finalize.rs:51`, both
`UnsupportedSyntax(".. requires classExtension decode — M4b-3 P2")`),
which is exactly the discipline this spec's § Seams sanctions. P2b
retargets those messages; nothing silent sits on main in between.

**2. Stuck reporting is control-flow faithful, prose deferred.**
`reportStuckSyntheticMVar` (`SyntheticMVars.lean:292-320`) **throws**
rather than only logging, so leanr raising an error is faithful in
control flow. P2a ports the structure — the `pendingMVars` drain, the
priority sort at `:322-362` that decides *which* stuck mvar is
reported, the per-kind dispatch, and a structured `ElabError` carrying
the mvar kind and its type — and defers `explainStuckTypeclassProblem`'s
note/hint prose and the `MessageData` rendering to whichever slice grows
a diagnostics layer. The oracle gate compares only the canonical `Expr`
on successful elaborations, so the prose is not differentially
verifiable; the sort is ported anyway because it is small and picks the
reported mvar deterministically. `mvarErrorInfos` lands as the table
plus its registration sites, with prose deferred the same way.

**3. `withSynthesize` is P2a's, and `synthesizeUsingDefault` is a
guarded seam.** § P2 did not name `withSynthesize`
(`SyntheticMVars.lean:662-693`), but `builtin/ascription.rs:39-42`
records that `elabTypeAscription`'s two arms are degenerate in leanr
precisely because it does not exist. That seam goes live the moment the
ladder lands, and it is on the hot path: ascription is how the corpus
induces expected types. With the ladder present and ascription
unrewired, instance mvars created inside the ascribed *type* would drain
at the top-level fixpoint instead of before the body is elaborated,
which can reorder assignments and change the emitted term. So P2a builds
`withSynthesize`/`withSynthesizeLight` and rewires both ascription arms.

`withSynthesizeImp` calls `synthesizeUsingDefaultLoop` when
`postpone == .yes`, and ladder rung 3 is `synthesizeUsingDefault` — both
owned by P3. P2a supplies `synthesize_using_default` as a
**shape-guarded seam**: it errors if any pending `TypeClass` mvar's
class has default instances registered (via the `default_instances`
accessor already on P2a's ledger), and is a no-progress no-op otherwise.
P3 replaces the body; P3's scope is unchanged.

## Amendment 2 (2026-07-28, post-P2a): P3 precedes P2b

Reality-checking § P2b against the merged P2a code (#32, `43c1df1`)
found that P2b cannot verify its own headline behavior next. The plan
order changes to **P3 before P2b**; the sections below are updated in
place, and this amendment records why and what else moved with it.

**1. P2b's feature is unreachable in the fixture, by construction.**
Three facts compound:

- The oracle gates the whole feature on coercions being available:
  `resultIsOutParamSupport := (← getEnv).contains ``Lean.Internal.coeM
  && resultIsOutParamSupport && !explicit` (`App.lean:1355`).
  `app/mod.rs:398` computes it faithfully, and prelude-mode `Elab0.lean`
  declares no `Lean.Internal.coeM`, so the flag is false for every
  application in the corpus.
- The trigger needs a class carrying `outParam`s
  (`hasLocalInstanceWithOutParams`, `App.lean:700-706`). `Elab0.lean`'s
  four classes carry none.

Both of those are fixture edits, and would have been fine on their own.
The third is not:

- `finalize`'s branch (`App.lean:637-648`) runs `synthesizeAppInstMVars`
  and then, *only* if the outParam mvar is still unassigned and the
  result type *is* that mvar, `synthesizeSyntheticMVarsUsingDefault`.
  That second call is P2a's shape-guarded seam (`synthetic.rs:595`).
  And the way an outParam mvar stays unassigned is the oracle's own
  motivating example, `getElem xs 0` — where the `0` is what remains
  undetermined until the `OfNat` default instance fires. `num` is P3's.

So P2b-before-P3 can ship only the degenerate arm: every corpus term
writable today has the outParam solved by ordinary instance synthesis,
takes the `else`, and returns `e`. The interesting call is unreachable
not for want of corpus imagination but because no numeral elaborates
yet. § Plan decomposition's original rationale — "P2b after P2a because
the outParam branch's own body calls `synthesizeAppInstMVars` and
`synthesizeSyntheticMVarsUsingDefault`, both of which P2a builds" — was
half wrong: P2a built the first and seamed the second.

P3 has no reciprocal dependency on P2b (its corpus is `42`, `'a'`,
`(1.5 : Tag)`), so the swap is free. P2b then lands with a live, non-degenerate
corpus. The P2b seams stay on main one PR longer, which § Amendment
item 1 already establishes is sound: they are named, shape-guarded
seams, not silent divergences.

**2. P3 is one plan, not split.** `num` is the only construct in
leanr's grammar that creates a `TypeClass` mvar whose class carries
default instances, so it is the sole source producer for ladder rung 3.
Shipping the rung without its producer — or `num` while still seaming at
rung 3 — is exactly what the M4b-2 amendment's condition forbids. They
ship together, in eight tasks (§ P3).

**3. The two deferred P2a follow-ups land in P3.** P2a's final
whole-branch review raised both; both were deferred with the stated
intent of folding them into the next plan, and P3 is it.

- **`synthetic.rs` splits first** (804 lines at merge) into
  `synthetic/state.rs` (decl types, registration, `mvar_error_infos`,
  `may_postpone`), `synthetic/ladder.rs` (the step, the five rungs,
  `withSynthesize`, `resumePostponed`) and `synthetic/report.rs` (stuck
  reporting and its priority sort) — **before** P3 adds the
  `synthesizeUsingDefault*` family as `synthetic/default_inst.rs`, not
  after. A pure move, gated on committed records staying byte-identical.
- **A second instance per fixture class** (`Wrap`, `Pair`, `Dflt`), as
  P3's *second* task. Today each has exactly one candidate, so
  `tc/useWrapAscribed` and `tc/pairBoth` may reach the oracle's answer
  by a different route than the oracle takes — leanr resolving eagerly
  from the sole candidate where the oracle keeps the goal stuck and lets
  the argument fix the type parameter. A second instance separates "got
  the right answer" from "got it for the right reason". If it turns a
  green record red, the fix is in P2a's `synthesizeInstMVarCore` and
  lands in the same PR; placing the task second means that surfaces
  before any literal work is committed. `NoInst` keeps zero instances
  (`synthetic_smoke.rs` asserts its no-instance arm), and none of the
  three gains a *default* instance — `Elab0.lean:158-163` records why
  that would break the stuck-path tests.

## Amendment 3 (2026-07-29, post-P3): P2b splits into P2b-i and P2b-ii

Reality-checking § P2b against the merged P3 code (#33, `d478d71`)
found that P2b as scoped cannot be built inside `leanr_elab` and
`leanr_olean` alone: the mechanism its `finalize` branch depends on does
not exist anywhere in leanr, and it lives one layer down, in
`leanr_meta`'s synthesis engine. P2b therefore splits — **P2b-i**
(outParam support inside synthesis) then **P2b-ii** (the elaborator
branch) — on the same reasoning that split § P2, and the sections below
are updated in place.

**1. P3's own follow-up already made this a requirement.** § Follow-ups
item 3 records it as a hard requirement on P2b's plan rather than a
deferral: `try_synth_instance`'s stuck pre-test
(`crates/leanr_elab/src/synthetic/ladder.rs:97-123`) answers `Undef` on
goals the oracle answers `.some` — the standard binop shape
`HAdd Nat Nat ?γ` — and closing it means porting `preprocessOutParam`
(`SynthInstance.lean:775-817`) and `assignOutParams` (`:825-845`).
Neither exists in leanr: `crates/leanr_meta/src/synth.rs:1651-1659`
names both a seam, together with `preprocess` itself, and assigns them
to "M4b". This is that slice.

**2. The port is not avoidable by choosing a gentler fixture class.**
`synthInstanceCore?` routes the `.noMVars` arm through
`preprocessOutParam` too (`:983-1002`, the `OrderDual` note), so the
first fixture class carrying an `outParam` sends *every* goal against it
— ground goals included — through machinery leanr does not have. There
is no outParam class that is safe to introduce without the port.

**3. Where the mechanism lives decides which crate the plan touches.**
The whole of it sits at synthesis's *entry* boundary, not inside the
tabled search: nested subgoals go through `newSubgoal` / `getInstances`
and never see `preprocess`. In the oracle that boundary is
`synthInstanceCore?` (`:960-1010`); in leanr it is
`MetaCtx::synth_instance_main` (`crates/leanr_meta/src/synth.rs:1599`).
Preprocessing the goal in `leanr_elab` instead was rejected: it would
put Meta-level machinery in the elaborator, leave `whnf.rs`'s
`synth_pending` and `leanr_meta`'s own differential tier wrong, and keep
the Mathlib synthesis nightly dark on outParam classes — which is most
of Mathlib (`tests/fixtures/meta/synth-passlist.txt` is currently empty).

**4. `leanr_meta/src` widens a second time, and this one is not
additive.** § Global constraints allowed P1–P3 purely additive
accessors and widened once for P4's *new* modules. P2b-i changes
behavior in an *existing* file, `synth.rs`, which no prior widening
covers. It is recorded here rather than taken silently, and it is
bounded: one function's control flow (`synth_instance_main`) plus new
private helpers, no kernel change, no other `leanr_meta` path altered,
and gated on `leanr_meta`'s and `leanr_elab`'s committed corpora staying
byte-identical.

The structural change is *where the snapshot sits*. The oracle's
`withConfig` wraps everything (`:963-964`) while `withNewMCtxDepth`
wraps only `main` (`:978`); leanr today wraps the whole function in one
`checkpoint`/`rollback` pair, which is its stand-in for the depth block
(`synth.rs:1600,1667`). That pair narrows to the search alone:

```
set cfg                                 // withConfig (:963-964), unchanged
  preprocess(ty) -> {type, kind}        // :737-773 — inside cfg, OUTSIDE the snapshot
  checkpoint
    main(preprocessOutParam(type))      // :983-1002, all three kinds
  rollback                              // leanr's withNewMCtxDepth stand-in
  applyAbstractResult(type, abst)       // :877-925 — open, then assignOutParams
restore cfg
```

`assignOutParams` running *after* the rollback is the entire feature: it
is what lets its `isDefEq type resultType` assign the caller's `?γ` at
the outer depth, which is how `?γ := Nat` becomes a *result* of
synthesis. It requires moving `open_abstract_mvars_result` out of
`synth_instance_body` (`synth.rs:1688`) into a new
`apply_abstract_result`.

**5. Three corrections to § P2b as written.**

- **`ClassEntry` has three fields, not two.** `Class.lean:14-31` in the
  pin: `name`, `outParams`, and `outLevelParams` (positions of universe
  parameters appearing only in output-parameter types). All three
  decode; `outLevelParams` has a consumer in `preprocessOutParam`'s
  `preprocessLevels` (`:786-795`) but *not* in `preprocess`'s
  `cacheKeyType`, because leanr has no top-level `synthInstance` cache
  at all — that half is a named seam.
- **outParam-aware discr-tree keys and `computeSynthOrder` are free.**
  The oracle serializes both into the `.olean` at instance registration
  and leanr reads them rather than recomputing (`instances.rs:46-60`),
  so `Instances.lean:159`'s `getOutParamPositions?` use needs no port.
- **`applyAbstractResult?`'s tail is not portable.**
  `checkMayHaveSideEffects` + `check result` (`:876-923`, the issue-#796
  universe-constraint propagation) needs `Lean.Meta.check`, which
  `leanr_meta` does not have and cannot get from `leanr_check` (that
  crate sits above it). Named seam on `apply_abstract_result`.

**6. P2b-i's headline behavior is invisible to the synth record shape,
so the shape changes first.** This is § Amendment 2's finding one layer
down. For `Op N N ?γ` the committed record carries `goal`, `mvars`,
`ok`, `val` — and leanr today answers `ok:true`, `val:instOpN`, leaving
`?γ` unassigned, while the oracle answers identically *and* assigns
`?γ := N`. Same record, different state. So `dump_synth.lean` and
`oracle_synth.rs` gain a post-synthesis **assignment** field
(`"assigns":[{"i":<N>,"e":<E>}]`, encoded in the same `EncSt` as
`goal`/`val`, absence meaning unassigned) before any of the port is
differentially verifiable. It is also what makes the placement in item 4
mutation-detectable: run `assignOutParams` before the rollback instead
of after and the assignment is discarded, so `assigns` comes back empty
and the record goes red.

**7. P2b-i changes every synthesis goal, not only outParam ones.**
`preprocess` normalizes unconditionally — `forallTelescopeReducing`,
`whnf` on the body, `mkForallFVars` (`:740-742`) — and leanr skips that
step entirely today, handing `synth_instance_body` the goal with only
`instantiate_mvars` applied. So the port's regression gate is wider than
its new records: the 15 committed synth records and the 101 committed
elab records (which reach synthesis through P2a's instance arguments and
P3's default instances) must stay byte-identical. One that moves means
the port is wrong, not that the baseline was stale.

**8. P3's carried follow-ups 1 and 2 land in P2b-ii.** § Follow-ups
records that one fixture addition closes both — a universe-polymorphic
`@[default_instance]` carrying an `instImplicit` binder, at a fourth
priority — and prices it at re-deriving `synthetic_smoke.rs`'s
rung-counting assertions plus an `Elab0.olean` rebuild and a corpus
regen. P2b-ii pays the rebuild and the regen anyway (item 9), so the
marginal cost is the smoke assertions alone. Item 3 of that section
splits with the plan: the `preprocessOutParam` / `assignOutParams` port
is P2b-i's, and teaching `ladder.rs`'s pre-test to exempt
output-parameter positions is P2b-ii's, because the pre-test is
`leanr_elab` code that becomes reachable exactly when `Elab0.lean` gains
its first outParam class.

**9. One ordering trap inside P2b-ii, recorded now.**
`app/args.rs:497-505`'s guard fires on `result_is_out_param_support`
alone, with no shape test. Declaring `Lean.Internal.coeM` in
`Elab0.lean` flips that flag true for every non-`@` application, so the
real `isNextOutParamOfLocalInstanceAndResult` (`App.lean:698-728`, with
`isResultType` / `hasLocalInstanceWithOutParams` /
`isOutParamOfLocalInstance` / `isOutParamOf`) must land in the same
commit as the fixture declaration. Split across two commits, the corpus
is uniformly red in between.

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
  behavior change: `classExtension` (P2b-i; `ClassEntry` is
  name + `outParams` + `outLevelParams`, § Amendment 3 item 5) and the
  `coe_decl` tag attribute (P4). Precedent: M4a plan 4 PR-A, which decoded the
  instance / default-instance / projection-fn extensions the same way.
  Both are untrusted-input parsers and must never panic on arbitrary
  bytes (`docs/THREAT_MODEL.md`); no existing decode path changes.
- **`leanr_meta/src` constraint — widened twice, deliberately.** M4b-1
  and M4b-2 allowed only purely additive, TCB-neutral, behavior-neutral
  public *accessors* on `leanr_meta`. Plans P1–P3 stay inside that rule
  (see § Accessor ledger). **P2b-i widens it first, and its widening is
  the one that is not additive**: the outParam mechanism lives at
  synthesis's entry boundary, so it changes the control flow of an
  existing function, `MetaCtx::synth_instance_main`
  (`crates/leanr_meta/src/synth.rs:1599`), and adds a `ClassTable` to
  `MetaCtx::new`. Bounded and recorded in § Amendment 3 item 4: no
  kernel change, no other `leanr_meta` path altered, and gated on both
  crates' committed corpora staying byte-identical. **P4 widens it
  again**: coercion is Meta-level
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
`tests/fixtures/elab/dump_elab.lean` changes to match, once, in P2a.

A bare `_` is a **natural**, not synthetic, mvar, so
`reportStuckSyntheticMVars` does not touch it and the committed
`hole/bare` → `{"k":"mvar","i":0}` record is expected to survive
unchanged. That is an argument, not evidence: P2a's final task
regenerates every fixture and gates on `git diff --exit-code` over the
JSONL, landing the empty diff as proof that adding the fixpoint is a
no-op on all pre-existing records. If a pre-existing record *does*
change, that is a finding to run down — not a fixture to update.

### Plan decomposition

Seven plans (P2 split per § Amendment; P3 before P2b per § Amendment 2;
P2b split per § Amendment 3), each a single PR with its own hermetic
oracle tier. That tier is `oracle_elab.rs` + `elab-queries.jsonl` for
every plan except **P2b-i**, which touches no `leanr_elab` code and is
verified one layer down, at `oracle_synth.rs` + `synth-queries.jsonl`
(§ Verification). The table is in **execution order**.

| Plan | Content | First oracle-verifiable thing |
|---|---|---|
| **P1** application foundation | `expandApp`, `Arg`/`NamedArg`, the `ElabAppArgs` state machine (explicit / implicit / strictImplicit arms, `addNewArg`, `fType` normalization), `propagateExpectedType`, `etaArgs`, `finalize` (no coercion), overload single-candidate guard, implicit-lambda guard; rewire `ident` / `@` / `.{u}` through `elabAtom` | polymorphic applications without instance args; eta cases via named args |
| **P2a** instance args + the fixpoint | `instMVars`, `trySynthesizeAppInstMVars` / `synthesizeAppInstMVars`, `synthesizeInstMVarCore`, `.typeClass` registration, the escalation ladder, `mayPostpone` / `withoutPostponing`, `withSynthesize` + the ascription rewire, `mvarErrorInfos`, `reportStuckSyntheticMVars`, the entry-point pipeline change; M4b-2's `fun` postponement seam goes live | typeclass applications; postponed-then-resumed terms |
| **P3** literals + defaults | the `synthetic.rs` split and the fixture second-instances (§ Amendment 2 item 3), `Term.mkInstMVar`, `num` (`OfNat`), `char` (`Char.ofNat`), `scientific` (`OfScientific`), `synthesizeUsingDefault` / `synthesizeSomeUsingDefaultPrio` | `42`, `(42 : Tag)`, `'a'`, `(1.5 : Tag)`, and a numeral inside an application |
| **P2b-i** outParam synthesis | `classExtension` decode (`ClassEntry` = name + `outParams` + `outLevelParams`), `ClassTable` in `MetaCtx`, `preprocess` / `preprocessOutParam` / `assignOutParams` in `synth.rs` with the snapshot narrowed to the search, the synth record's new `assigns` field | `Op N N ?γ` — the outParam assigned as a *result* of synthesis, at the meta tier |
| **P2b-ii** the outParam branch | `Context.resultIsOutParamSupport` producer, `isNextOutParamOfLocalInstanceAndResult`, `State.resultTypeOutParam?`, the `finalize` outParam branch, `ladder.rs`'s stuck pre-test exemption, P3's carried follow-ups 1–2 | `getElem`-shaped applications whose result type is a local instance's outParam |
| **P4** coercions | `coe_decl` tag-extension decode, `expandCoe`, `coerceSimple?` / `coerceToFunction?` / `coerceToSort?` in new `leanr_meta/src/coe.rs`, `mkCoe` + `.coe` mvar case + `ensure_has_type` rewire, monad-lift shape guard | `(n : Int)` where `n : Nat`; a `CoeFun` application |
| **P5** binder + argument breadth | implicit / strictImplicit / instImplicit binders for `fun`/`let`/`have`, `fun`'s `optType`, `optParam` defaults, the `autoParam` arm, `..` ellipsis, real implicit-lambda insertion replacing P1's guard | `fun {α} => …`; signatures with `optParam`; `f ..` |

**Ordering rationale.** P1 before P2a because the state machine is what
first *creates* the synthetic mvars the fixpoint drains — the M4b-2
amendment's condition ("each ladder field gets a source producer and
differential coverage in the slice that builds it") holds only in that
order. P3 after P2a because `num`'s default-instance fallback *is* a
fixpoint rung — and it is the slice that replaces P2a's guarded
`synthesize_using_default` seam. P2b after **P3**, not merely after P2a:
the outParam branch's body calls `synthesizeAppInstMVars` *and*
`synthesizeSyntheticMVarsUsingDefault` (`App.lean:639-647`), and only
the first of those is P2a's — the second is the seam P3 retires, and
the branch's own trigger needs a numeral (§ Amendment 2 item 1). P2b-i
before P2b-ii because P2b-ii's first fixture outParam class routes every
goal against it — ground goals included — through `preprocessOutParam`,
which P2b-i is what builds (§ Amendment 3 items 2 and 3); the reverse
order would put a known-divergent synthesis path under a live corpus.
P4 after P2a because a stuck coercion registers a `.coe` synthetic mvar.
P5 last because it is breadth over a verified core, so it can absorb
schedule pressure without leaving a divergent path on main.

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

### P2a — the synthetic-mvar ladder, the fixpoint, and instance arguments

New module `leanr_elab/src/synthetic.rs`.

**Ladder state.** `TermElabM` grows `pending_mvars: Vec<MVarId>`,
`synthetic_mvars: HashMap<MVarId, SyntheticMVarDecl>`,
`mvar_error_infos`, and the reader flag `may_postpone`.
`SyntheticMVarKind` gets all four oracle variants —
`TypeClass`, `Coe`, `Postponed`, `Tactic`
(`TermElabM.lean:65-99`) — from the start, even though P2a produces only
`TypeClass` and `Postponed` (P4 produces `Coe`; P5 registers `Tactic`).
The fields live directly on `TermElabM`, mirroring the oracle's
`Term.State` one-to-one, with their `impl` block in `synthetic.rs` so
`elab.rs` does not grow. A nested sub-struct was rejected: every step
that touches both the table and `&mut self` would need a
`mem::take`/restore dance for no structural gain.

**`synthesizeSyntheticMVarsStep`** (`SyntheticMVars.lean:573-602`) is
transliterated exactly, because its ordering is fidelity-critical and
easy to get subtly wrong. `pending_mvars` is a list whose **head is the
most recent**. The step clears it, processes the snapshot with
`filterRevM` — i.e. **in creation order**, not list order — and
re-merges as **`new_pending ++ still_unsolved`**, so mvars created
*during* the step land before the leftovers. Progress is
`count_before != still_unsolved.len()`, not "any succeeded". A version
that reverses the merge order still terminates and still looks green on
simple corpus entries, then diverges on nested applications, so P2a
gates it with a term that creates a pending mvar during a resume.

**The escalation ladder** (`SyntheticMVars.lean:611-648`): five rungs,
tried in this exact order, looping back to rung 1 on any success.

1. `step(postpone_on_error: false, run_tactics: false)`
2. *(rungs 2-5 only when `postpone != .yes`)*
   `without_postponing step(postpone_on_error: true, run_tactics: false)`
3. `synthesize_using_default` — **P3's, a shape-guarded seam in P2a**
   (§ Amendment, item 3): errors if any pending `TypeClass` mvar's class has
   default instances registered, otherwise reports no progress
4. `without_postponing step(postpone_on_error: false, run_tactics: false)`
5. `step(postpone_on_error: false, run_tactics: true)`

then `report_stuck_synthetic_mvars` when `postpone == .no`, then
`process_postponed_universe_constraints`. `PostponeBehavior` is the
oracle's three-valued `yes` / `no` / `partial`.

**Stuck reporting.** `reportStuckSyntheticMVars`
(`SyntheticMVars.lean:322-362`) drains `pending_mvars`, sorts by the
oracle's priority order (non-typeclass problems first; among typeclass
problems, those whose syntactic range does not contain another's), and
calls `reportStuckSyntheticMVar` (`:292-320`), which **throws**. P2a
ports that structure and the sort; the note/hint prose is deferred
(§ Amendment, item 2).

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

**Instance arguments.** `processInstImplicitArg` (`App.lean:903-923`)
replaces P1's seam, **both halves**: under `explicit` (`@`) it consumes
a `_` hole via `nextArgHole?` and *still* synthesizes for it, falling
back to `processExplicitArg` otherwise; the non-`explicit` half discards
the minted mvar and recurses into `main`. `mkInstMVar` mints
`mkFreshExprMVar ty MetavarKind.synthetic`, pushes onto
`State::inst_mvars` (`App.lean:415`), and `addNewArg`s it.

`synthesizeInstMVarCore` (`TermElabM.lean:1232-1275`) ports whole,
including the `containsPendingMVar` re-try branch and the two
assignment-mismatch throws: its `true` / `false` / throw trichotomy is
what the scheme rests on. Three call sites, each replacing one of P1's
guards:

- `trySynthesizeAppInstMVars` (`App.lean:355-362`) — filters, keeps the
  unsolved, runs **before** expected-type propagation
  (`app/propagate.rs:88`)
- `synthesizeAppInstMVars` (`App.lean:368-370` → `:75-79`) — registers
  each unsolved mvar as `.typeClass none` plus a
  `registerMVarErrorImplicitArgInfo`, then clears; the `finalize` tail
  (`app/finalize.rs:85`)
- the `resultTypeOutParam?` branch (`App.lean:639-647`) — **stays a
  named seam**, retargeted to P2b-ii (`app/finalize.rs:51`)

**`withSynthesize` and the ascription rewire** (§ Amendment, item 3).
`withSynthesize` / `withSynthesizeLight` (`SyntheticMVars.lean:662-693`)
save `pending_mvars`, clear, run the body, synthesize, and restore by
appending — the oracle's `finally`, so the restore is drop-safe in
leanr. `elabTypeAscription` (`BuiltinNotation.lean:410-434`) then takes
its real shape: `withSynthesize(.yes) <| elabType type`, then
`elabTerm e type`, then `ensureHasType`; the second arm is
`withSynthesize(.no) <| elabTerm e none`. `builtin/ascription.rs`'s
module doc, which records the degenerate arms as deliberate, is updated
in the same PR.

**The entry point** becomes the pipeline in § The entry-point pipeline —
`elab_term → synthesize_synthetic_mvars(.no) → instantiate_mvars` — and
`tests/fixtures/elab/dump_elab.lean` changes to match, once, here.

**Corpus.** `tests/fixtures/elab/Elab0.lean` grows a prelude-mode class
and instance scaffold modelled on `tests/fixtures/meta/Synth0.lean:86-136`:
a single-parameter class with a concrete instance, a parameterized
instance for the postponement case, and a class with no instance for the
stuck path. Only the shapes P2a's records discriminate — not a copy of
Synth0.

### P2b — outParam support (P2b-i, then P2b-ii)

*Executes after § P3, per § Amendment 2, and splits in two per
§ Amendment 3. It keeps its position in this document so the two halves
of the P2 split read together.*

#### P2b-i — outParam support inside synthesis

Everything the `finalize` branch below depends on, one layer down.
`preprocess` / `preprocessOutParam` / `assignOutParams`
(`SynthInstance.lean:737-845`) are today a named seam in
`crates/leanr_meta/src/synth.rs:1651-1659`; P2b-i ports them into
`MetaCtx::synth_instance_main`, narrowing that function's
`checkpoint`/`rollback` pair to the search alone so `assignOutParams`
runs after it and can assign the caller's mvar. Detecting the shape
needs class outParam positions, so P2b-i also adds the
**`classExtension` decode** (`ClassEntry` = name + `outParams` +
`outLevelParams`) to `leanr_olean` — the same shape as M4a plan 4
PR-A's instance decode, and small — and a `ClassTable` built once in
`MetaCtx::new` beside `InstanceTable::build`. It is an untrusted-input
parser: it must never panic on arbitrary bytes
(`docs/THREAT_MODEL.md`), and no existing decode path changes.

`applyAbstractResult?`'s `checkMayHaveSideEffects` + `check` tail and
`preprocess`'s `cacheKeyType` are named seams, not ports — the first
needs a `Meta.check` this crate cannot have, the second a synthesis
cache it does not have (§ Amendment 3 item 5). The full rationale,
the structural diagram and the corrections to this section as
originally written are in § Amendment 3; verification is in
§ Verification tier 4.

#### P2b-ii — the elaborator branch

`Context.resultIsOutParamSupport` and `State.resultTypeOutParam?`
(`App.lean:141-175`, `610-700`) — the fields exist from P1; P2b-ii
supplies
their producers and the `finalize` branch. When an application's result
type is the `outParam` of a *local* instance, `finalize` calls
`synthesizeAppInstMVars` and then, if the parameter is still unassigned
and the result type *is* that mvar, `synthesizeSyntheticMVarsUsingDefault`
— eagerly applying default instances and changing the emitted term for
`getElem`-shaped code. The first callee is P2a's and the second is P3's,
which is why P2b-ii follows both.

Two things about the corpus follow from that, and are what make P2b-ii
worth running only here. The env gate
(`env.contains ``Lean.Internal.coeM`, `App.lean:1355`) is false
throughout `Elab0.lean` today, so P2b-ii's fixture task declares
`Lean.Internal.coeM` and a `getElem`-shaped class carrying an
`outParam`; and the branch's *interesting* arm needs the outParam mvar
to survive `synthesizeAppInstMVars` unassigned, which in the oracle's
own worked example is the numeral in `getElem xs 0`. P3 is what makes
that term elaborate at all (§ Amendment 2 item 1).

That declaration is also P2b-ii's one ordering trap:
`app/args.rs:497-505`'s guard fires on `result_is_out_param_support`
alone, so `isNextOutParamOfLocalInstanceAndResult` (`App.lean:698-728`)
must land in the same commit as the fixture change or the whole corpus
is red in between (§ Amendment 3 item 9). P2b-ii also carries
`ladder.rs`'s pre-test exemption and P3's carried follow-ups 1–2
(§ Amendment 3 item 8).

A conservative over-approximation (treat every application as outParam
support) was rejected: it would reject most ordinary typeclass
applications and gut P2a's own corpus. Leaving
`result_is_out_param_support = false` permanently was likewise rejected —
but as a *temporary* state across the three PR boundaries it now spans
(P2a, P3, then P2b-i) it is sound, because P1 already shipped it as a
named, shape-guarded seam rather than a silent divergence
(§ Amendment, item 1).

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

**Module structure.** `synthetic.rs` splits first (§ Amendment 2 item
3); the new family lands as `synthetic/default_inst.rs`. The three
literal arms go in the existing `builtin/lit.rs` (202 lines today, ~450
after), which splits into `lit/{str,num,char,scientific}.rs` only if it
passes that.

**`Term.mkInstMVar` does not exist in leanr yet, and must not be
confused with the one that does.** `app/args.rs:618` implements
`ElabAppArgs`'s own same-named `where`-binding (`App.lean:919-923`),
which *defers* synthesis: mint a synthetic mvar, push it on `instMVars`,
`addNewArg`, done. `Term.mkInstMVar` (`TermElabM.lean:1925`) is a
different function — it calls `synthesizeInstMVarCore` eagerly and
registers `.typeClass` only `unless` that succeeds. `num` and
`scientific` need the latter. Both its halves already sit on
`TermElabM`, so it is a short new function in `synthetic/state.rs`; the
two stay distinct rather than one being refactored into the other.

**Fixture growth in `Elab0.lean`.** Copied verbatim from `Init`, because
their shape is what the emitted `Expr` references: `Bool`,
`class OfNat (α : Type u) (_ : Nat)`,
`@[default_instance 100] instance instOfNatNat`, `class OfScientific`.
Opaque carriers for `char` — `axiom Char : Type` plus
`axiom Char.ofNat : Nat → Char` — following this file's own
`axiom String` precedent: `elabCharLit` emits
`Char.ofNat (rawNatLit c)` without ever reading `Char`'s shape or the
expected type, while the real definition is `dite` over
`BitVec.ofNatLT`/`UInt32`, unreachable in a prelude-mode fixture. The
emitted `Expr` is byte-identical either way.

The ascribed-numeral record uses a fixture-local second numeric type
(`Tag`, with its own `OfNat Tag n` instance at a third priority) rather
than `Int`, which prelude-mode cannot reach. That is a stated departure
from this section's original `(42 : Int)` example. It buys something:
`instOfNatNat`'s prio 100, `Tag`'s, and the existing `instDfltNat`'s
bare `@[default_instance]` (prio 1000) give three distinct priorities in
one environment, which is what makes the descending-priority walk
differentially observable instead of vacuous.

One risk is measured rather than assumed in the fixture task: the
emitted term carries `Expr.lit (.natVal 42)` typed as the fixture's own
`Nat`. Lean's kernel special-cases literals by the *name* `Nat` with
`Nat.zero`/`Nat.succ` constructors, which `Elab0.lean`'s inductive
matches — but this is the first literal the elab fixture mints.

**Accessor ledger.** Larger than this spec's original three entries; see
§ Accessor ledger's P3 row. `isClass?` needs no accessor:
`synthesizeUsingDefaultPrio`'s two early-outs fuse, since a head
constant with a non-empty default-instance list is necessarily a class,
and P2a's `pending_class_name` already computes exactly that. Faithful
by fusion, not a seam.

**Verification.** Tier 1 corpus: `42`, `(42 : Nat)`, `(42 : Tag)`,
`'a'`, `(1.5 : Tag)`, plus a numeral *inside* an application and one
against an instance goal — the application cases are what actually
drive the ladder, since a bare `42` with no expected type is the
degenerate path.

**A bare `1.5` is not a corpus record and cannot become one** (measured
in P3 task 7; this spec said `1.5` unascribed until the P3 fix wave).
`OfScientific` has no `@[default_instance]` in `Elab0.lean`, so an
unascribed scientific literal leaves `OfScientific ?α` stuck, the
fixpoint reports it, and `dump_elab.lean` DROPS a query whose
elaboration throws — the record would simply be absent, with only a
stderr line. Every `sci/*` query is therefore ascribed to `Tag`, which
grounds `?α` inside `mkFreshTypeMVarFor` so `Term.mkInstMVar`'s eager
synthesis closes the goal. This is not symmetric with `num`: `42` is a
corpus record precisely *because* `instOfNatNat` is a default instance,
which is what makes the bare numeral the rung-3 case.
Tier 2: the reverse-creation-order walk (already assigned to P3 by
§ Verification) and the descending-priority set order, which the
three-priority fixture makes non-vacuous. Tier 3: `rawNatLit` stays
unregistered, and P2a's `synthesize_using_default` seam is *gone*
rather than retargeted.

**Tasks (eight).** 1. split `synthetic.rs`; 2. second instances, regen,
and any `synthesizeInstMVarCore` divergence it surfaces; 3. the fixture
scaffold and `Elab0.olean` rebuild; 4. the `leanr_meta` accessors and
the `synth.rs` generalization; 5. `Term.mkInstMVar` plus
`synthetic/default_inst.rs` and the two ordering tests, retiring P2a's
seam; 6. `num` and both `getDecLevel` failure branches; 7. `char` and
`scientific`; 8. seam audit, corpus extension, `mise run ci`.

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

Additive, TCB-neutral, behavior-neutral public accessors, by plan.
Rows are in this document's order, not execution order (P3 runs before
P2b, § Amendment 2, and P2b is split in two, § Amendment 3). P3's row is the one entry that is not purely
additive; it says so.

| Plan | Additions |
|---|---|
| P1 | `instantiate_beta_rev_range` — and only this one. `Expr` destructuring (`fTypeIsForall`, `bindingDomain!`, `getAppFn`) uses the already-public `Store::expr_node` (`leanr_kernel/src/bank/terms.rs:615`) via `mctx.store()` + `view.store`, and `whnfForall` composes from the public `MetaCtx::whnf`, so neither needs an accessor. `instantiate_beta_rev_range` does: its beta step needs `whnf.rs`'s `beta_rev`/`head_beta`, which are `pub(crate)`. |
| P2a | `process_postponed_levels` + `postponed_len`, `default_instances_of` (forwarding the `pub(crate)` `instances.rs:520` — needed by rung 3's guarded seam), `check_occurs` (`metactx.rs:837` — a `pub` forwarder to the existing `pub(crate)` `occurs_check`, `assign.rs:1117`, needed to port `resumePostponed`'s occurs-check assignment guard) |
| P2b-i | **Does not belong in this ledger, and that is the point.** P2b-i is not an accessor addition: it changes `MetaCtx::synth_instance_main`'s control flow, adds private `preprocess` / `preprocess_out_param` / `assign_out_params` / `apply_abstract_result` helpers to `synth.rs`, and adds a `ClassTable` argument to `MetaCtx::new` (a signature change across 25 call sites; P4 adds a further extension, so the six entry slices should become one `EnvExtensions` struct in the same task rather than paying that churn twice). The widening is recorded in § Global constraints and § Amendment 3 item 4. The only genuinely additive part is the `pub` reader pair `get_out_param_positions` / `get_out_level_param_positions` (oracle: `Class.lean:76-88`), which P2b-ii consumes. |
| P2b-ii | none expected — it reads P2b-i's class accessors and otherwise stays in `leanr_elab` |
| P3 | Audited against the merged P2a code; larger than this spec's original three. **Additive forwarders:** `get_dec_level` (composes the private `get_level`, `infer.rs:754`, `level_normalize`, and `dec_level_top`, `level.rs`); `is_prop` (widening the `pub(crate)` `lazy_delta.rs:171` to `pub` — needed by `num`'s Prop failure branch; no name clash exists, so no forwarder was added); `checkpoint`/`rollback` (widening the `pub(crate)` `metactx.rs:944`/`:954` to `pub`, plus a `pub` `MetaSnapshot` re-export — needed for `commitWhen`, `Lean/Util/MonadBacktrack.lean:50-60`; both line numbers corrected in the P3 fix wave — `:952` was blank, and `:56` truncated the citation before the `catch ex => restoreState s; throw ex` arm that is the whole reason `rollback` is needed on the error path); `with_assignable_synthetic_opaque` (needed by this plan only for `synthesizeUsingDefaultInstance`, `SyntheticMVars.lean:164` — the spec's earlier attribution to `synthesizeUsingDefaultPrio` was off by one function, and "only" is scope-local: the pin turns the flag on in eleven places, enumerated in `config.rs`'s field doc; both corrected against the pinned v4.33.0-rc1 source in M4b-3 P3 task 4 — moved here from P2a, whose ladder never reaches it; `config.rs`'s module doc named `assign_synthetic_opaque` as a deferred field; task 4 added it, cutting that list from three to two). **The `Config` field's READ SITES are part of this row's contract, not an implementation detail** (added in the P3 fix wave: a config field with no consumer is dead, and a later slice reading only "added the field and the scope" would not know where the flag is consulted). `Config::assign_synthetic_opaque` (`crates/leanr_meta/src/config.rs:95-163`, whose field doc enumerates all three sites and is the authority this row mirrors) is open-coded at three `syntheticOpaque` checks, two of them **gated by the flag**: `assign.rs:157-166` (`unassigned_mvar_id`, transcribing `isAssignable`, `ExprDefEq.lean:1731-1733`) and `lazy_delta.rs:498-501` (`is_def_eq_singleton`'s `isAssignable sFn`, `ExprDefEq.lean:2156` → the same `:1731-1733`; gated in P3 task 4 fix round 1, because it is reachable from inside an `isDefEq` and an ungated copy would refuse an assignment the oracle permits). The third, `discr_path.rs`'s discrimination-key builder (`DiscrTree/Main.lean:308`), is **deliberately NOT gated** — and the reason is not "the oracle never runs it inside the scope", which is false (the flag does survive into synthesis; `synthInstanceCore?`'s `withConfig`, `SynthInstance.lean:963-964`, overrides six fields but not this one). What moots the gate there is `withNewMCtxDepth` (`SynthInstance.lean:978`): every mvar from outside the search is at a different depth, so `isReadOnlyOrSyntheticOpaque`'s FIRST arm (`Basic.lean:981-982`) returns `true` before the kind is examined. Depth is this crate's standing tier-1 seam, so wiring the flag in there without modelling depth would flip `Star`/`Other` keys the oracle keeps at `Other`. `whnf.rs`'s `synth_pending` guard is not on the list at all: `synthPendingImp` (`SynthInstance.lean:1033-1036`) matches `mvarDecl.kind` directly and never reads the config. `mk_raw_nat_lit` is NOT needed (M4b-3 P3 task 4): `Store::expr_lit_nat` (`leanr_kernel/src/bank/terms.rs:535`) and `MetaCtx::store_mut` are both already public, which is exactly how `builtin/lit.rs`'s `elab_str` reaches `expr_lit_str`. **New:** `default_instance_priorities` — the *global* descending distinct priority set (`getDefaultInstancesPriorities`); the existing `default_instances_of` is per-class and cannot produce it. **Not additive, and the one item that isn't:** `mk_const_with_fresh_mvar_levels` and `forall_meta_telescope_reducing` (returning binder infos, which `synthesizeUsingDefaultInstance` needs to pick out the `instImplicit` binders as new pending goals). Both loops existed — `refresh_instance_levels` and the telescope inside `get_subgoals` — but private, specialized to `&Instance`, and discarding binder infos. (Line references dropped: M4b-3 P3 task 4 renamed the first and moved the second, so the numbers this row carried before the commit no longer resolve. The generalized forms are `MetaCtx::mk_const_with_fresh_mvar_levels` and `MetaCtx::forall_meta_telescope_reducing`, both in `synth.rs`.) P3 **generalizes them out of `synth.rs` and has `get_subgoals` call the generalized form**, rather than duplicating a fidelity-critical telescope loop in `leanr_elab`. Behavior-neutral, gated by `synth.rs`'s existing tests plus the `leanr_meta` oracle corpus staying byte-identical. |
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
Untrusted-input discipline is unchanged: the only new decoders are
P2b-i's `classExtension` and P4's `coe_decl` name set, both following the
existing env-extension decode pattern, which must never panic on
arbitrary bytes (`docs/THREAT_MODEL.md`).

## Verification

Four tiers, no new nightly workflow.

1. **The hermetic differential gate** remains the only correctness
   oracle: `oracle_elab.rs` replays `elab-queries.jsonl` against
   committed `.olean` fixtures and compares byte-for-byte on the
   canonical `Expr`. Each plan extends the corpus — except P2b-i, whose
   gate is tier 4.
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
   order walk — the first two in P2a, the third in P3. Each gets a
   direct unit test constructing the queue state, in the
   `binder_smoke.rs` style. The corpus cannot be relied on to catch
   these.
3. **Seam audit per plan**, in M4b-1's Task-7 style: enumerate every
   unregistered kind and every guarded shape and assert each returns a
   named `UnsupportedSyntax` rather than a wrong `ExprId`.
4. **The meta-tier synthesis gate, for P2b-i only.** P2b-i touches no
   `leanr_elab` code, so it is verified where the code lives:
   `crates/leanr_meta/tests/oracle_synth.rs` over
   `tests/fixtures/meta/Synth0.lean`. Three parts, and the first is a
   precondition for the other two (§ Amendment 3 item 6): the record
   shape gains `assigns`, the post-synthesis state of every declared
   goal mvar. Then `Synth0.lean` gains outParam classes chosen so that
   each mechanism dies without one — an `HAdd`-shaped
   `class Op (a b : Type u) (c : outParam (Type u))` whose goal
   `Op N N ?γ` pins `?γ := N` (the shape `ladder.rs:105-115` cites as a
   live divergence); a goal whose outParam is already concrete and
   *wrong*, so `assignOutParams`' `isDefEq` fails and the result is
   rejected — without which a constant-`true` `assign_out_params` keeps
   the suite green; a ground goal against the same class, for the
   `.noMVars` arm the oracle also routes through `preprocessOutParam`;
   a class whose universe appears only in its outParam, giving
   `preprocessLevels` a producer; and the `getElem`-shaped class P2b-ii
   will need, proved out here first. Third, the regression gate is
   wider than the new records: `preprocess` normalizes *every* goal, so
   the 15 committed synth records and the 101 committed elab records
   must stay byte-identical (§ Amendment 3 item 7). The Mathlib
   synthesis nightly is expected to move `synth-passlist.txt` off zero
   as a consequence; that is an outcome reported by the nightly, not a
   gate in the PR, and no workflow changes.

`mise run ci` — which gates `cargo fmt --check` and clippy, not only
tests — runs before every commit and push.

## Seams (shape-guarded, not fall-through)

Each of these detects the shape the oracle would have handled and
errors, rather than proceeding to emit a different term:

| Seam | Owner |
|---|---|
| overloaded application (candidate count > 1) | the slice that grows `resolve_global` |
| implicit-lambda insertion (P1 only; P5 implements) | M4b-3 P5 |
| local-instance outParam result type (P1 named it "P2"; retargeted) | M4b-3 P2b-ii |
| `try_synth_instance`'s stuck pre-test over output-parameter positions (P3 § Follow-ups item 3) | M4b-3 P2b-ii, over P2b-i's port |
| `synthesize_using_default` with default instances in play (P2a) | M4b-3 P3 |
| `applyAbstractResult?`'s `checkMayHaveSideEffects` + `check` (P2b-i) | the slice that grows a `Meta.check` |
| `preprocess`'s `cacheKeyType` / `outLevelParams` wildcarding (P2b-i) | the slice that builds the synthesis cache |
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

## Follow-ups carried out of P3 (for the next plan author)

Recorded in the P3 whole-branch-review fix wave. These are *known* gaps
in shipped P3 code, not deferrals of unwritten constructs — § Out of
scope is for the latter. Each names the slice or plan that should carry
a task for it.

*Owners assigned by § Amendment 3 item 8: items 1 and 2 are P2b-ii's
(it pays the olean rebuild and corpus regen anyway); item 3 splits
across P2b-i and P2b-ii; item 4 is unchanged.*

**1. The nested `synthesizePending` fixpoint is untested (owner:
P2b-ii, which adds the fixture below).** `synthesize_using_default_instance`
collects a candidate's `instImplicit` binders as new pending goals and
recurses (`crates/leanr_elab/src/synthetic/default_inst.rs:245-254`,
oracle `SyntheticMVars.lean:167-171`). Mutating that loop to collect
*nothing*, and separately stubbing `synthesize_pending` to
`return Ok(true)`, each pass the ENTIRE suite — corpus, smoke tests and
seam audit — because no `@[default_instance]` in `Elab0.lean` has an
instance-implicit binder (`instDfltNat` has no binders;
`instOfNatNat`/`instOfNatTag` take one *explicit* `(n : Nat)`).

**2. The candidate universe refresh is untested (same owner: P2b-ii).**
`mk_default_instance_candidate`
(`crates/leanr_elab/src/synthetic/default_inst.rs:274-304`) builds the
candidate with fresh level mvars. Mutating it to build at an EMPTY level
list — reintroducing precisely the plan defect caught during P3
implementation — also passes the whole suite, because no fixture default
instance is universe-polymorphic (`Dflt`'s parameter is `Type`, and both
`OfNat` instances land on `Nat`/`Tag`, so each instance constant has an
empty universe-parameter list).

**One fixture addition closes both 1 and 2**: a universe-polymorphic
default instance that also carries an `instImplicit` binder, registered
at a FOURTH priority. Cost to be paid with it: adding a priority
re-derives `default_instance_walk_visits_pending_mvars_in_reverse_creation_order`
(`crates/leanr_elab/tests/synthetic_smoke.rs`), whose `prios.len() == 3`,
`prios[0] > 100 && prios[1] == 100` and `order.len() == 4` assertions all
count rungs — plus an `Elab0.olean` rebuild and a `fixtures:regen-elab`
run, so the corpus must be re-checked record-by-record.

**3. `try_synth_instance`'s `outParam` residue is P2b's, as a hard
requirement (owner: split — the port is P2b-i's, the pre-test is
P2b-ii's, § Amendment 3 item 8).** Documented at
`crates/leanr_elab/src/synthetic/ladder.rs:97-123`: the standard binop
shape `HAdd Nat Nat ?γ` is `.some` in the oracle — `preprocessOutParam`
(`SynthInstance.lean:775-817`) replaces the caller's mvars in output-
parameter positions with ones minted inside `withNewMCtxDepth`
(`:978`), and `assignOutParams` (`:825-845`) assigns the caller's mvar
back after the depth block closes — while leanr's stuck pre-test answers
`Undef` and the ladder eventually raises `StuckSyntheticMVar` on a goal
the oracle answers. It is unreachable today only because no fixture
class carries an `outParam`; the moment one does, this is a live
divergence, not a missing feature. **P2b-i's plan must carry the port
(`preprocessOutParam`/`assignOutParams`, not the mctx-depth model) and
P2b-ii's must carry the pre-test exemption that consumes it**, rather
than relying on a reader finding the comment.

**4. `with_assignable_synthetic_opaque` has no drop guard (owner:
`leanr_meta`, whenever an external caller can panic).**
`crates/leanr_meta/src/metactx.rs` restores `Config::assignSyntheticOpaque`
by plain save/run/restore. P3 task 4 widened the function from
`pub(crate)` to `pub`, so an external caller that panics inside the
scope and catches the unwind would leave the flag `true` on that
`MetaCtx`. No in-tree path reaches it (the sole production caller is
`leanr_elab`'s `synthesize_using_default_instance`, which is
`Result`-based and catches nothing), so the P3 fix wave recorded the
risk in the function's doc rather than adding the guard — a drop guard
is a behaviour change to `leanr_meta`, which that wave was scoped out of.

## Next step

Plan 1 (application foundation) shipped in #31; P2a — the
synthetic-mvar ladder, the fixpoint, and instance arguments — shipped in
#32; P3 — literals and default instances — shipped in #33. The next
implementation plan is **P2b-i** — outParam support inside synthesis
(§ P2b-i, and § Amendment 3 for why P2b splits, what P2b-i widens in
`leanr_meta`, and why the synth record shape changes before anything
else in that plan). P2b-ii, P4 and P5 get their own implementation
plans as each predecessor lands, mirroring M4b-2's rhythm.
