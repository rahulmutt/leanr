# `MkBinding.elimMVarDeps` — design spec

## Where this sits

M4b-3 P4 shipped its elaborator tier in #41. Its whole-branch review
recommended that `MkBinding.elimMVarDeps` get its own spec and
implementation plan, landing **before P5**, rather than being folded
into P5. This is that spec.

`MetaCtx::mk_binding` (`crates/leanr_meta/src/metactx.rs:737`) is a plain
`abstract_fvars` loop. The oracle's `mkBinding` is not: before it
abstracts, it runs `elimMVarDeps` over the body and over every binder
type. The consequence is a wrong `ExprId` with no error — a postponed
synthetic metavariable registered under a binder and resumed after that
binder has closed leaves an unabstracted `fvar` where the oracle emits a
`bvar 0`.

This is infrastructure, not a coercion detail. § Amendment 6 item 5 of
the M4b-3 spec justified giving the metavariable-local-contexts work its
own slice as "infrastructure every later slice that elaborates under a
binder needs"; that sentence describes `elimMVarDeps` word for word. P5
is binder and argument breadth, so it multiplies the producers of this
bug; debugging it inside a breadth slice is the failure mode Amendment 6
was written to avoid.

## The gap, measured

The gap is already documented and pinned executably, so this section
records what exists rather than new probes:

- `metactx.rs:710` carries a `# UNMODELLED: MkBinding.elimMVarDeps`
  heading on `mk_binding` itself, with the full diagnosis.
- `crates/leanr_elab/tests/seam_audit.rs:727`,
  `postponed_coe_under_a_binder_leaves_an_unabstracted_fvar_pending_elim_mvar_deps`,
  holds the pinned oracle answer for
  `fun (n : Nat) => pairW n Nat.zero` and asserts leanr differs from it
  by **exactly one token**:

  ```text
  leanr : fun (n : Nat) => pairW Nat (Wrapper.mk Nat <fvar n>) Nat.zero
  oracle: fun (n : Nat) => pairW Nat (Wrapper.mk Nat  bvar 0  ) Nat.zero
  ```

  Its first assertion is an `assert_ne!`, so it fails the day the gap
  closes. Its doc comment already carries the retirement instructions.
- `crates/leanr_elab/tests/oracle_elab.rs:169-192` asserts class-wide
  that no corpus answer contains an `fvar` node at all, and names this
  gap as the cause when one appears. Every corpus query is a closed
  term, so that detector is exact.
- The same postpone-then-resume path with **no** binder
  (`pairW Nat.zero Nat.zero`, the record `coe/postponedThenResumed`)
  agrees with the oracle byte-for-byte. The corpus therefore has **zero**
  differential coverage of a postponed synthetic metavariable under a
  binder.

Not coercion-specific: a `.coe` metavariable, a `.postponed` one, and a
`.typeClass` one resolving against a local instance all qualify.

## What the oracle does

`MetavarContext.lean` (toolchain `leanprover/lean4:v4.33.0-rc1`),
namespace `MkBinding`, `:938-1349`.

`mkBinding` never abstracts directly. It abstracts through

```lean
abstractRange (xs) (i) (e) := do
  let e ← elimMVarDeps xs e
  pure (e.abstractRange i xs)          -- :1277-1279
```

called once on the body as `abstractRange xs xs.size e` and once per
binder type as `abstractRange xs i type` (`:1313-1345`). Note that
`elimMVarDeps` always receives the **full** `xs`, even when only the
first `i` are abstracted.

`elimMVarDeps xs e` returns `e` untouched when `e` has no expr
metavariable, and otherwise runs `elim` under a fresh cache
(`:1252-1257`). For an unassigned metavariable `?m` occurring applied to
`args`, `elimMVar` (`:1176-1229`):

1. `toRevert := getInScope mvarLCtx xs` — the members of `xs` that are
   actually in `?m`'s own declared context (`:1070-1077`). Empty means
   nothing to do.
2. `toRevert ← collectForwardDeps mvarLCtx toRevert` (`:1037-1062`) —
   close under forward dependencies: any later declaration in `?m`'s
   context whose type or value depends on something already in
   `toRevert` joins it.
3. `newMVarLCtx := reduceLocalContext mvarLCtx toRevert` (`:1065-1067`)
   — literally `toRevert.foldr (fun x lctx => lctx.erase x.fvarId!)`.
4. Mint a fresh auxiliary metavariable at `newMVarLCtx` with type
   `mkAuxMVarType mvarLCtx toRevert kind mvarDecl.type` (`:1123-1168`),
   which abstracts `?m`'s type over `toRevert` and wraps it in
   `forall`s.
5. Replace the occurrence with `mkMVarApp mvarLCtx newMVar toRevert kind`
   (`:1090-1097`) applied to the visited `args`.
6. Connect the two, by kind:
   - **not** `syntheticOpaque` → assign the original outright,
     `?m := ?new ys`.
   - `syntheticOpaque` → delayed-assign the **new** one back to the
     original, `?new (ys ++ nestedFVars) := ?m`, where `nestedFVars`
     comes from any delayed assignment `?m` already had.

`collectForwardDeps` rests on `DependsOn` (`:660-725`) via
`findLocalDeclDependsOn` (`:744`) / `localDeclDependsOn` (`:767`),
whose "may depend" case is what makes it more than a syntactic fvar
scan: a declaration depends on `x` if it mentions a metavariable whose
**local context** contains `x`.

The delayed channel is consumed in two places that matter here:
`instantiateExprMVars` (C++, `instantiateExprMVarsImp`, `:577-583`) and
`whnfDelayedAssigned?` (`Meta/WHNF.lean:587-606`).

`mkCoe` mints its postponed metavariable as
`mkFreshExprMVar expectedType MetavarKind.syntheticOpaque`
(`Elab/Term/TermElabM.lean:1310`), so leanr's failing case is the
**delayed** branch.

## What this ships

A faithful port of the `elimMVarDeps` core into `leanr_meta`, plus the
delayed-assignment channel it requires, wired into `MetaCtx::mk_binding`
so every existing caller gets it. `MetaCtx::mk_forall` / `mk_lambda`
keep their signatures; `leanr_elab/src` is untouched.

What it does **not** ship, each with the reason:

| Not shipped | Why |
| --- | --- |
| `mkAuxMVarType`'s ldecl arms | leanr's `LocalDecl` has no `nondep` field (see § Let-declarations) |
| `revert` | no caller without a tactic framework |
| `preserveOrder`, `etaReduce`, `usedOnly`, `mvarIdsToAbstract`, `quotContext` | no producer in leanr |
| `numScopeArgs` | no `MVarDecl` field, no `check_assignment` consumer (`assign.rs:226-227`) |
| the occurs check's delayed channel, `isDefEq`'s delayed arms | `assign.rs:1124` already declares these; measured, not assumed (§ Verification) |
| `newLocalInsts` filtering | **not a new seam** — leanr has no `LocalInstance` concept at all, an elision already declared at `instances.rs:96` |

## Global constraints

- The **kernel/olean TCB** stays sound and minimal. This slice takes one
  kernel edit, additive and TCB-neutral (§ Crate-boundary ledger).
- Non-additive `leanr_meta` changes are **flagged** with the alternative
  rejected and the neutrality gate to be run, per the M4b accessor
  precedent (M4b-3 § Amendment 5 item 12, and the P3 `synth.rs`
  generalization precedent).
- **Every discriminator is measured** (AGENTS.md). A task brief that
  names a mutation its test is supposed to kill is a hypothesis: the
  implementer applies the mutation, watches the test go red, and reverts.
  Where it survives, the test is strengthened before the task closes.
- CI gates on `cargo fmt --check` and clippy via `mise run ci`; the test
  gates do not cover them.

## Architecture

### The entry point

`MetaCtx::mk_binding` keeps its existing peel-one-fvar-at-a-time
abstraction loop — that loop is transcribed from `infer.rs`'s
oracle-verified `rebuild_forall` and the whole corpus depends on it — and
gains `elim_mvar_deps` calls at exactly the oracle's two insertion
points:

- once on `body`, with the **full** `fvars`, before the loop;
- once per binder type, with the **full** `fvars`, before
  `abstract_fvars(ty, &fvars[..i])`.

This is `abstractRange`'s semantics with a minimal diff. The
peel-loop-vs-`abstractRange` equivalence is argued, not proven, by
construction; the byte-identical corpus is what proves it (§ Risk).

The `# UNMODELLED` heading at `metactx.rs:710` is deleted.

### The core

`elim_mvar_deps(xs, e)` returns `e` unchanged when `e` carries no expr
metavariable, so every `mk_binding` call over an mvar-free body is a
strict no-op. That is a *fast path*, not the neutrality argument: for a
body that does carry a metavariable the behavior genuinely changes, and
§ Risk item 1 is about exactly that population. Otherwise it runs `elim`
with a fresh cache. `elim_app` on a metavariable head: assigned to a lambda →
beta-reduce and re-`elim`; assigned otherwise → recurse on the value;
unassigned → `elim_mvar`. `elim_mvar` follows the six steps above.

The `withFreshCache` cache is a threaded `&mut` parameter, not new
`MetaCtx` state: it is scoped to one `elim_mvar_deps` call and to each
`mk_aux_mvar_type` call, and adding a field would make its lifetime a
matter of discipline rather than of type. Every recursion arm calls
`self.step()?`, per the crate's existing fuel discipline.

### The two branches, both reachable

The `syntheticOpaque` branch is leanr's `.coe` metavariable
(`leanr_elab/src/coe.rs:80` mints `MVarKind::SyntheticOpaque`, matching
`TermElabM.lean:1310`). The plain-assign branch is a `TypeClass`
metavariable, which leanr mints `MVarKind::Synthetic`
(`app/args.rs:834`, `synthetic/state.rs:204`).

The plain branch is **not** rare, and this is the slice's central risk.
Any `fun` whose body still holds an unassigned instance metavariable
when `mk_lambda` runs will now have that metavariable assigned to
`?new n`. The oracle absorbs this in `synthesizeInstMVarCore`'s
`instMVar.isAssigned` arm (`TermElabM.lean:1240-1268`): it synthesizes
`val` from the type, then runs `isDefEq oldVal val` with
`oldVal = ?new ys`, a Miller pattern. leanr already has that arm
(`synthetic/ladder.rs:207-234`, including the `contains_pending_mvar`
retry), which is why `leanr_elab/src` needs no change — but those
records currently come out right *by accident* (a synthesized instance
is a closed term, so the missing abstraction is invisible), and after
this slice they route through a path that has never fired.

### Let-declarations: a refusal, not an arm

`mk_binding`'s **telescope** is already cdecl-only; it refuses an ldecl
entry outright (`metactx.rs:769-772`). But `mk_aux_mvar_type` and
`mk_mvar_app` walk the **metavariable's own** local context, which can
contain let-declarations: `leanr_elab/src/builtin/binder.rs:734` pushes
one for every `let` and `have`.

`mkAuxMVarType` branches on `LocalDecl.ldecl (nondep := …)`
(`:1131-1160`), and **leanr's `LocalDecl` has no `nondep` field**
(`leanr_kernel/src/local_ctx.rs:37-43`) — `mk_let_binding` takes it as a
caller argument (`metactx.rs:835`), so the information does not exist on
the declaration at all.

So: a hard `MetaError` when `to_revert` contains an ldecl, shape-guarded
and named, mirroring `mk_binding`'s existing
`"let-decl fvar in a cdecl telescope"` refusal. Any ldecl arm written
today would be guessing `nondep`, and a named refusal beats a wrong
`ExprId`. The corpus must demonstrate no record reaches the guard.

Under that guard `mk_mvar_app`'s two kind branches coincide, and both are
transcribed anyway so the file reads against the oracle.

`mk_aux_mvar_type`'s metavariable arm (`:1157-1163`, `xs` carrying
"may dependencies") **is** transcribed: it is five lines and
`collect_forward_deps` is its producer.

### The delayed channel

`MetavarContext` gains
`DelayedMVarAssignment { fvars: Vec<ExprId>, mvar_id_pending: MVarId }`
and a `d_assignment` map, with `assign_delayed` / `delayed_assignment` /
`is_delayed_assigned`, plus `get_delayed_mvar_root` (`:436-440`).

Two consumers:

- `assign.rs::instantiate_mvars_body` (`:1202`) gains the delayed arm:
  a metavariable head with a delayed assignment whose pending
  metavariable is assigned becomes `mk_lambda fvars val` beta-applied to
  the args.
- `whnf.rs::whnf_delayed_assigned` (`:481`), today a hardcoded `Ok(None)`
  with a SEAM comment, becomes the real `whnfDelayedAssigned?`
  (`Meta/WHNF.lean:587-606`) — including its two `None` guards
  (insufficient arguments; the pending value still carrying
  metavariables). Its SEAM comment retires.

### Module layout

A new file `crates/leanr_meta/src/mk_binding.rs`, one
`impl<'e> MetaCtx<'e>` block — the house pattern (17 such blocks across
`assign.rs`, `whnf.rs`, `coe.rs`, `synth.rs`, …). `self` stays
`MetaCtx`, so `self.node` / `self.scratch` / `self.mctx` / `self.step()`
/ `self.guarded` need no re-plumbing.

| leanr | oracle |
| --- | --- |
| `depends_on`, `local_decl_depends_on` | `DependsOn` `:660-725`, `findLocalDeclDependsOn` `:744`, `localDeclDependsOn` `:767` |
| `get_in_scope`, `collect_forward_deps`, `reduce_local_context`, `mk_mvar_app` | `:1037-1097` |
| `mk_aux_mvar_type` | `:1123-1168` (cdecl + mvar arms; ldecl refuses) |
| `elim`, `visit`, `elim_app`, `elim_mvar` | `:1101-1249` |
| `elim_mvar_deps`, `abstract_range` | `:1252-1279` |

`depends_on` lives here rather than in its own module because
`collect_forward_deps` is its only caller; a second caller moves it out.

## Crate-boundary ledger

| File | Change | Status |
| --- | --- | --- |
| `leanr_kernel/src/local_ctx.rs` | `pub fn erase(&mut self, fvar_id: NameId)` — oracle `LocalContext.erase`, maintaining `index` exactly as `restore` (`:200`) already does | **additive, TCB-neutral**: the kernel checker gains no caller; no existing function body changes |
| `leanr_meta/src/mk_binding.rs` | new file | additive |
| `leanr_meta/src/mvar_ctx.rs` | `DelayedMVarAssignment`, `d_assignment`, `assign_delayed` / `delayed_assignment` / `is_delayed_assigned` | additive |
| `leanr_meta/src/local_snapshot.rs` | ordered enumeration for `collect_forward_deps`; a reduced-snapshot constructor filtering `local_names` in lockstep with the erased `lctx` | additive, `pub(crate)` |
| `leanr_meta/src/assign.rs` | `get_delayed_mvar_root` (additive); the delayed arm in `instantiate_mvars_body` (`:1202`); `mk_aux_mvar` (`:689`) generalized into `mk_aux_mvar_at(lctx, ty, kind)` with the existing entry point becoming `mk_aux_mvar_at(current_lctx(), ty, Natural)` | **flagged, behavior-neutral** |
| `leanr_meta/src/whnf.rs` | the `whnf_delayed_assigned` stub (`:481`) becomes real | **flagged, behavior-neutral** |
| `leanr_meta/src/metactx.rs` | two `elim_mvar_deps` insertions in `mk_binding`; `# UNMODELLED` heading deleted | **flagged, behavior-neutral** |
| `leanr_elab/src` | none | — |

**Why each flagged row is behavior-neutral, and how it is proven.**
Two of the three are neutral by unreachability: no delayed assignment
exists anywhere in leanr today, so `instantiate_mvars`' and `whnf`'s new
delayed arms cannot fire until this slice's own records create one, and
`mk_aux_mvar_at`'s existing entry point keeps its exact prior arguments.

The `metactx.rs` row is different and must not be overclaimed. An
mvar-free body takes `elim_mvar_deps`' fast path unchanged, but a body
carrying an unassigned metavariable whose declared context holds a
telescope fvar takes a path that has never run — the population task 1
measures, and § Risk item 1's subject.

For that row the proof is the **outcome**, not the reachability
argument: the corpus records are the oracle's own answers, so leanr
being right before and right after means the whole existing test suite
plus the elab (107 records), synth (24) and defeq/whnf/infer corpora
stay **byte-identical**, with the new records the only additions. A
record that moves is either a real regression or a place leanr was
accidentally right for the wrong reason; either way the gate catches it
rather than the next slice doing so.

The `mk_aux_mvar_at` generalization is a *refactor, not an addition* —
the same shape as P3's `forall_meta_telescope_reducing` generalization
out of `synth.rs`, which was flagged and approved on exactly this
rationale. Rejected alternative: a second aux-minting function
duplicating the declare-and-intern sequence.

## Rejected alternatives

- **Keep the kernel byte-untouched.** `reduceLocalContext` is repeated
  `lctx.erase`, and `LocalContext` has no `erase`; `mk_local_decl`
  (`:110`) mints a *fresh* fvar id, so a filtered context cannot be
  rebuilt from the public surface. The alternatives are an unfaithful
  reduction, or a shadow context type inside `leanr_meta` that
  `check_assignment_scope_body` would have to learn about — more
  invasive in `leanr_meta` than the one-function kernel addition it
  avoids.
- **Keep the unreduced lctx on the new auxiliary metavariable.** It
  re-admits the very fvar the slice exists to abstract:
  `check_assignment_scope_body` would accept an assignment mentioning
  it, and the leak returns by another route.
- **Skip the delayed channel; take the plain-assign branch for
  `syntheticOpaque` too.** Not viable, not merely unfaithful: the ladder
  later assigns `?m` itself on resume, and
  `MetavarContext::assign` refuses reassignment — a wrong answer becomes
  a hard error.
- **Put `elimMVarDeps` at the `mk_lambda` call sites in `leanr_elab`.**
  It is `mkBinding`'s contract in the oracle; `leanr_elab` has no
  metavariable-minting rights at the `MetaCtx` level; and
  `infer.rs::rebuild_forall` would silently keep the gap.
- **A standalone `MkBinding` struct mirroring the oracle's `M` monad.**
  Would need to borrow the store, mctx, lctx, snapshot cache and the
  step/guard budget out of `MetaCtx`; breaks the pattern every other
  module in the crate follows.
- **Inline into `metactx.rs`.** That file is already 1753 lines and is
  the crate's accessor surface; a 400-line fidelity transcription does
  not belong in it.

## Risk

Ranked, most likely to bite first:

1. **The plain-branch blast radius.** Existing records that hold an
   unassigned instance metavariable at `mk_lambda` time will newly route
   through `?m := ?new ys` and the ladder's `is_assigned`
   reconciliation. This directly threatens the byte-identical gate.
   Mitigation: **task 1 is a measurement, not code** (§ Verification).
2. **Pattern unification of `?new ys`.** The reconciliation needs
   `is_def_eq(?new n, val)` to solve a Miller pattern — an auxiliary
   metavariable applied to fvars. If leanr's `process_assignment` cannot,
   that is an inherited gap this slice surfaces.
3. **`depends_on`'s may-depend case** consults a metavariable's local
   context mid-traversal, a shape none of leanr's existing traversals
   need.
4. **The peel-loop / `abstractRange` equivalence** in `mk_binding`
   (§ The entry point) — argued by construction, proven only by the
   byte-identical corpus.

## Verification

**Task 1 is a blast-radius probe, and gates everything after it.**
Instrument `mk_binding` (throwaway, reverted) to report across all
existing corpora every call whose body carries an unassigned
metavariable with a telescope fvar in its declared local context. That
yields the true list of affected existing records *before* a line of the
port is written, rather than as a red corpus at task 10.

**The differential corpus.** Five records in
`tests/fixtures/elab/dump_elab.lean`, regenerated with
`mise run fixtures:regen`, each chosen to die if one specific ported
mechanism is removed:

| Record | Mechanism it must kill |
| --- | --- |
| `coe/postponedThenResumedUnderBinder` — `fun (n : Nat) => pairW n Nat.zero` | the delayed branch: `elim_mvar`'s `SyntheticOpaque` arm, `assign_delayed`, the `instantiate_mvars` delayed arm |
| a `Synthetic` instance metavariable still pending at `mk_lambda` | the plain-assign arm `?m := ?new ys` and the ladder's `is_assigned` reconciliation |
| nested `fun`s, the metavariable's context holding both binders, the inner telescope holding one | `get_in_scope`'s filter — a "revert everything in the metavariable's context" bug survives without it |
| a `coe/sortDomain`-shaped dependent pair (`(c : Carrier) (x : c)`) carrying a postponed metavariable | `collect_forward_deps`' closure |
| in-crate unit test on the auxiliary metavariable's declared context | `reduce_local_context` |

Rows 3 and 4 may need new declarations in `tests/fixtures/elab/Elab0.lean`.
**None of the five source strings has been run.** Per § Global
constraints, each row's stated kill is a hypothesis the implementer
verifies by mutation, strengthening or replacing the record where the
mutation survives.

**Discriminator gaps this slice closes.** Nothing in the tree currently
kills `MVarKind::SyntheticOpaque` — the mutation to `Natural` survives
(noted at `synthetic/default_inst.rs:215-219`). Record 1 is the natural
place to close it, since the two kinds take different `elim_mvar`
branches.

**Seam retirement.** `seam_audit.rs:727`'s `assert_ne!` flips to
`assert_eq!` and its named follow-ups are carried out: the gap notes in
`metactx.rs::mk_binding`, in `dump_elab.lean`'s `coeQueries` block, in
`oracle_elab.rs:135-192`, and in `seam_audit.rs`'s own module doc
(`:30`). `whnf.rs:476`'s SEAM comment retires with the stub.

**Measured, not assumed.** The seams in § What this ships — `numScopeArgs`,
the occurs check's delayed channel, `isDefEq`'s delayed arms — are
*claimed* unreached. The plan verifies each by instrumenting the entry
point and running the full corpora, not by asserting it in a brief.

**Gates.** `mise run ci` (which includes `cargo fmt --check` and clippy),
`mise run test`, `mise run meta:fast`, and `mise run parse:mathlib:fast`.
No full-corpus Mathlib sweep: this slice touches no parser.

## Plan decomposition

Twelve TDD tasks, comparable to P4's ten:

1. **Blast-radius probe** (measurement; gates the rest).
2. `LocalContext::erase` + the reduced-snapshot constructor.
3. `depends_on` / `local_decl_depends_on`, including the may-depend case.
4. `get_in_scope`, `collect_forward_deps`, `reduce_local_context`,
   `mk_mvar_app`.
5. The delayed channel in `mvar_ctx.rs` + `get_delayed_mvar_root`.
6. The `instantiate_mvars` delayed arm + the real
   `whnf_delayed_assigned`.
7. `mk_aux_mvar_at` generalization (gate: existing suite byte-identical).
8. `mk_aux_mvar_type`, including the ldecl refusal.
9. `elim` / `visit` / `elim_app` / `elim_mvar`, `elim_mvar_deps`,
   `abstract_range`.
10. Wire into `mk_binding`; run the neutrality gate.
11. The five records + the `SyntheticOpaque` discriminator + the
    `seam_audit` retirement.
12. Doc retirement across `metactx.rs`, `whnf.rs`, `dump_elab.lean`,
    `oracle_elab.rs`, `seam_audit.rs`.

## Next step

The implementation plan, via the writing-plans skill. M4b-3 P5 follows
this slice, as § Amendment 6 item 6 already sequenced it.
