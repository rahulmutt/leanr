# Local instances (`LocalInstances`) — design

**Status:** design, approved 2026-09-09. Prerequisite slice ahead of
M4b-3 P5, recorded as Amendment 8 in
`docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md`.

**Oracle pin:** `leanprover/lean4:v4.33.0-rc1` (the `lean-toolchain`
version). Every citation below is against that source tree.

## What this slice is

The `LocalInstances` context the oracle maintains alongside every local
context (`LocalInstance`, `MetavarContext.lean:268-273` — a `className`
and an `fvar`, nothing else), its producers at every fvar-pushing scope,
and its one consumer: `getInstances` appending fvar-valued candidates at
query time (`SynthInstance.lean:202-240`).

It is meta-tier. It lands entirely in `leanr_meta` (plus the fixture and
replay harness), and adds no `leanr_elab` code.

## Why it is its own slice and not a task inside M4b-3 P5

P5 — binder and argument breadth — is what first gives leanr's
elaborator an instance-implicit binder, and therefore what first
*produces* a local instance. The obvious reading is that local instances
are P5's problem. Three measured facts put them below P5 instead, and
they are the whole argument for this slice existing:

1. **The producer is not the elaborator.** The oracle installs local
   instances at every fvar-pushing scope, not at the binder elaborator:
   `withLocalDeclImp` via `withNewFVar` (`Basic.lean:1785-1789`,
   `:1791`), `withLetDeclImp` through the same `withNewFVar`
   (`:1905-1911`), and `forallTelescopeReducingAux` via
   `withNewLocalInstancesImp` (`:1472`, `:1477`). leanr's counterparts
   are `MetaCtx::push_local_decl` (`metactx.rs:619`), `push_let_decl`
   (`:653`) and `assign.rs`'s `forall_bounded_telescope` (`:614`) — all
   inside `leanr_meta`. An elaborator-only implementation would be
   unfaithful at every meta-tier telescope.

2. **It amends the metavariable-local-contexts slice.**
   `MetavarDecl.localInstances` (`MetavarContext.lean:320`) sits beside
   `MetavarDecl.lctx` (`:309`). So leanr's mvar declaration, its
   `LocalCtxSnapshot`, and the `lctx_swap` pair (`metactx.rs:515`,
   `:542`) each grow a local-instances component, and
   `with_mvar_local_context` must reinstall instances along with the
   context. That is an amendment to structures PR #39/#40 built, not new
   construction beside them.

3. **It is not additive.** `get_instances`' result changes. Per the
   M4b accessor precedent, a non-additive `leanr_meta/src` change must
   be flagged with the alternative rejected and the neutrality gate that
   will be run. Both are in § Neutrality gate below.

## Data model

### The record

```rust
struct LocalInstance { class_name: NameId, fvar: ExprId }
```

Mirrors `MetavarContext.lean:268-273` field for field. The oracle's
`BEq`/`Hashable` instances key on `fvar` alone (`:275-279`); leanr needs
neither yet, and adding them without a consumer would be dead code.

### Where it lives

A `local_instances: Vec<LocalInstance>` on `MetaCtx`, following the
`local_names` precedent (`metactx.rs:80`) — with one difference that is
easy to get wrong.

`local_names` is in **lockstep** with `lctx.decls`: one entry per push,
so `lctx_restore(cp)` truncates it to the same index and a `debug_assert`
guards the invariant. `local_instances` is **sparse** — only class-typed
declarations produce an entry — so index-truncation does not apply.

Each entry therefore carries the `lctx` length at which it was pushed,
and `lctx_restore(cp)` pops while the last entry's recorded length is
`>= cp`. This keeps `lctx_checkpoint`'s return type unchanged, so no
call site churns.

**Rejected alternative: derive the set from `lctx` on demand.** It would
need `is_class` over the whole local context inside `get_instances`, and
`isClassExpensive?` runs `whnf`. `get_instances` documents a re-entrancy
invariant at `instances.rs:468-479`: the instance table is
`mem::take`n — empty — for the whole duration of `discr_get_match`, and
that comment explicitly warns that a change widening what the path
touches must re-check the invariant. A whnf there is exactly that
change, and nothing would catch it: the nested lookup would report "no
instances" rather than erroring. Eager-at-push keeps whnf off the query
path.

### Producers

Installation happens at three chokepoints, matching the oracle's three:

| leanr | oracle |
|---|---|
| `MetaCtx::push_local_decl` (`metactx.rs:619`) | `withLocalDeclImp` → `withNewFVar` (`Basic.lean:1791`, `:1785-1789`) |
| `MetaCtx::push_let_decl` (`metactx.rs:653`) | `withLetDeclImp` → `withNewFVar` (`Basic.lean:1905-1911`) |
| `assign.rs::forall_bounded_telescope` (`:614`) | `forallTelescopeReducingAux` → `withNewLocalInstancesImp` (`Basic.lean:1472`, `:1477`) |

### `is_class`

Port `isClassQuick?` (`Basic.lean:1358-1381`) — a pure structural walk
with no whnf — falling back to `isClassExpensive?` (`:1520-1522`:
`withReducible`, forall-telescope to the conclusion, then `isClassApp?`'s
head-constant test at `:1509-1518`) only on `isClassQuick?`'s three
`.undef` arms: `.letE`, `.proj`, and an application whose head is a
`.lam` or an mvar assigned to a non-constant.

Class membership is `ClassTable::out_params(name).is_some()`
(`instances.rs:580`). Every class gets a `classExtension` entry whether
or not it declares output parameters, so the existing table is already
the membership oracle and needs only a named predicate over it.

`isClass?` swallows exceptions (`Basic.lean:1542-1543`,
`try isClassImp? type catch _ => return none`). leanr models that as
error → `None`, never propagated — a divergence here would turn a
would-be non-class into a hard failure.

### Two oracle filters, one of them vacuous

- **Implementation-detail declarations are skipped.**
  `withNewLocalInstanceImp` (`Basic.lean:1383-1388`) reads the local
  declaration and returns unchanged when `localDecl.isImplementationDetail`.
  leanr's `LocalDecl` (`leanr_kernel/src/local_ctx.rs:37-43`) carries
  `id`, `binder_name`, `ty`, `binder_info`, `value` and no kind field,
  and nothing in leanr mints an implementation-detail declaration. The
  filter is therefore **vacuously satisfied**, and this slice adds no
  field to a kernel struct for a producer that does not exist — the same
  treatment `check_implicit_lambda` gives `hasNoImplicitLambdaAnnotation`
  (`elab.rs:388-393`). **Trigger for revisiting:** the slice that builds
  the tactic framework or the match compiler is the first to mint one.

- **Erasure and private-instance filtering do not apply to locals.**
  Those live in `getInstances`' `.const` arm (`SynthInstance.lean:216-228`);
  a local instance has no declaration name to erase. Faithful, not a
  seam.

## Consumption: `get_instances`

`getInstances` (`SynthInstance.lean:202-240`) does four things in an
order that is load-bearing:

1. read the local instances (`:204`);
2. telescope the goal and `isClass?` its conclusion for `className`
   (`:205-209`);
3. fetch the global candidates via `getUnify`, insertion-sort them
   ascending by priority, and filter erased/private (`:210-228`);
4. append every local whose `className` matches, with a `synthOrder`
   computed on the spot (`:230-238`).

### The className must be computed before the table is taken

leanr's `get_instances` (`instances.rs:467`) has no className today — it
queries the discrimination tree directly. Adding one means calling
`is_class`, whose `.undef` arms run whnf, which collides with the
`mem::take` re-entrancy invariant described above.

**The oracle's own ordering is the resolution**: `className` is computed
at step 2, before the global index is touched at step 3. Transcribing
the order faithfully also satisfies the invariant. Faithfulness and
safety agree here, which is worth stating so a later reader does not
"optimize" the computation down into the query.

### Ordering: locals are tried first

The oracle appends locals to the **end** of an ascending-by-priority
array, and `generate` consumes it **back-to-front**. Locals are
therefore tried *before* every global candidate.

leanr transcribes that composition as `sort_by_key(|i| i.priority)` then
`reverse()` (`instances.rs:486-492`, whose module doc argues the
composition is exact rather than approximate). So the local append must
happen **after the sort and before the reverse**, landing at the front
of leanr's vector.

This is the single most mutable line in the slice, and its test must
actually discriminate: a local and a global candidate both matching one
goal, asserting the local is chosen, with the push moved to
before-the-sort as the mutation that turns it red.

### `synthOrder` is computed per-local, at query time

Unlike globals, which carry a `synthOrder` precomputed by the instance
extension, a local's is computed on the spot (`SynthInstance.lean:231-238`):
telescope `inferType linst.fvar` and collect the indices whose binder
info is `.instImplicit`.

That telescope itself pushes fvars, so under this slice's chokepoints it
installs further local instances while computing one. This is the same
self-reference the oracle acknowledges at `Basic.lean:1402-1406`,
surfacing a second time. Named, not resolved.

Class matching is exact `NameId` equality (`linst.className == className`),
never defeq.

### One documented invariant this falsifies

`instances.rs:89-111` argues that `global_name: None` is reachable
**only** via adversarial or malformed `.olean` bytes, and that
`InstanceTable::build` drops such entries as incompleteness-only. A
local instance is a legitimate `global_name: None`: constructed directly
in `get_instances`, never passing through the table.

That module doc must be rewritten rather than left standing, and every
downstream read of `global_name` audited for an assumption it no longer
supports. This is its own task, not a documentation touch-up.

## Verification

### Tier

Meta-tier, where the code lives: `crates/leanr_meta/tests/oracle_synth.rs`
over `tests/fixtures/meta/Synth0.lean` and
`tests/fixtures/meta/synth-queries.jsonl`. Same reasoning M4b-3 P2b-i
used for being verified one layer down from the slice that consumes it.

### The record shape must grow first

The synth record is `goal` / `mvars` / `assigns` / `val` / `ok`
(`dump_synth.lean:23-32`). **There is no way to express a goal under a
non-empty local context.** With no local context there is no class-typed
fvar, and with no class-typed fvar there is no local instance to verify
at all.

The elaborator tier cannot cover for it either: the only elaborator
producer of a class-typed binder is P5's instance-implicit binder, which
comes *after* this slice. Left alone, the slice would ship on unit tests
only, below this repo's differential bar.

So the record grows an `fvars: [{i, t, bi}]` field, mirroring
`mvars: [{i, t}]`. The encoder already numbers fvars
(`dump_synth.lean:11`, `:105-106`) and query builders already run in
`MetaM` (`:180-182`), so this is a record-shape and replay change, not
an encoder redesign. M4b-3 P2b-i's `assigns` addition is the precedent,
and like `assigns` this is a **precondition task, first in the plan** —
every other record depends on it.

`bi` is carried because a local's `synthOrder` is read off the
instance-implicit binders of its own type; a round-trip that dropped
binder info could not reconstruct it.

### The gate is self-consistent

Replay pushes the declared local context through
`MetaCtx::push_local_decl` — the exact chokepoint this slice adds. The
fixture's local context *is* the producer, so no test-only path installs
instances a real run would not.

### Records, each killing a stated mutation

| Record | Mutation it must kill |
|---|---|
| `[inst : C α]` in scope, goal `C α`, no global candidate | locals never appended |
| a local and a global both matching one goal | the append moved before the sort (§ Ordering) |
| a class-typed **let** binder | `withLetDeclImp`'s install dropped |
| a non-class fvar in scope | a constant-true `is_class` |
| a local whose type has instance-implicit binders | an empty `synth_order` |
| an instance installed inside a telescope, goal after restore | the sparse-pop logic in `lctx_restore` |
| a `let`- or `proj`-headed type | `isClassExpensive?` never exercised, only `isClassQuick?` |

Every one of these is applied, watched go red, and reverted. A brief
that *names* a mutation is not a brief that has *run* it: on a recent
slice, four of five task briefs named mutations their tests did not
kill. This instruction goes into each implementer dispatch verbatim.

### Neutrality gate

Both committed corpora stay byte-identical apart from the new records:
117 elaboration records and 26 synthesis records.

**This is measured, not structural**, and the spec says so rather than
claiming more than it can. Because the producer sits at the meta-tier
telescopes, any *existing* synthesis that runs with a class-typed fvar
in scope can move. `dflt/polyInstImplicitUnderBinder` is the likeliest
candidate.

A record that moves **halts the slice for diagnosis** rather than being
absorbed into a regenerated baseline. If leanr was previously right by
accident there, that is the slice's first real finding.

### CI

`mise run ci` — which gates `cargo fmt --check` and clippy, not only
tests — before every commit and push. `mise run fixtures:regen` when
`Synth0.lean` grows declarations. No new nightly workflow; neither
Mathlib sweep nor the typeclass-synthesis nightly is touched.

## Seams

| Seam | Owner |
|---|---|
| `isClassExpensive?`'s whnf depends on the local-instance set being computed (`Basic.lean:1402-1406`) | inherited property, documented; no owner because there is no wrong shape |
| implementation-detail local declarations (vacuous — no producer, no kind field) | the slice that builds the tactic framework or the match compiler |
| `"type class instance expected"` when the goal's `isClass?` is none — leanr does not throw | **pre-existing**, explicitly unowned |
| `scoped instance` namespace-activation | unchanged, still unowned (`instances.rs:64-88`) |
| erasure / private-instance filtering | unchanged, still unowned (`instances.rs:123-163`) |

The `"type class instance expected"` divergence is left deliberately:
closing it here would put corpus movement from an unrelated fix inside
this slice's neutrality gate, and the gate is the whole approval
argument for a non-additive change.

`withNewMCtxDepth`'s depth machinery — this crate's standing tier-1
seam — does not reach local instances at all, since they are fvars and
not metavariables. Recorded as a non-interaction so a later reader does
not go looking for one.

## Non-goals

- No `leanr_elab/src` change. The producer wiring is P5's.
- No `isClass?` caching; the oracle has none at this layer.
- No Mathlib sweep, nightly, or workflow change.
- Not the two adjacent unowned seams `instances.rs` already defers
  (`scoped instance` activation; erasure / private-instance filtering).
  Local instances are a different mechanism. This slice closes one seam,
  not three.

## One prediction, written down in advance

Amendment 7 of the M4b-3 spec records that the elimMVarDeps slice's
`leanr_elab/src`-untouched constraint was falsified for exactly one
function, because wiring a meta-tier mechanism made a dormant elaborator
scoping bug live (`default_inst.rs` rung 3, `fun (n : Nat) => 0`).

**This slice is the same shape.** Installing local instances changes
what synthesis finds under a binder. So the narrow exception Amendment 7
established — *additive fixes to a seam a measured regression names*,
never a blanket lift — is stated as applying here from the start, rather
than being discovered at merge for the third consecutive slice.

## What M4b-3 P5 inherits

1. **Instance-implicit binders become live rather than decorative.**
   P5's producer wiring is a call at the binder site into
   `push_local_decl`, which is already the chokepoint — a small task,
   not a subsystem.
2. **The elimMVarDeps hazard compounds.** Local instances change what
   synthesis finds under a binder, so the `mvarId.withContext`
   scoping-audit task at P5's binder-family boundary now has two
   independent reasons to exist.
3. **`MetavarDecl.localInstances` must survive postponement.** A
   postponed synthetic metavariable resumed after its binder closed has
   to carry its local instances with it. That is precisely the shape
   that produced both prior prerequisite slices, and P5 multiplies its
   producers — so it is the first thing P5's own whole-branch review
   should probe.

## Estimated shape

~11 tasks, in the same range as the elimMVarDeps slice's 12:

1. the `fvars` record-shape precondition (`dump_synth.lean` + replay)
2. `LocalInstance`, the `MetaCtx` field, and sparse `lctx_restore`
3. `is_class` — `isClassQuick?` plus the `isClassExpensive?` fallback
4. install at `push_local_decl` / `push_let_decl`
5. install at `forall_bounded_telescope`
6. `MetavarDecl.localInstances`, `LocalCtxSnapshot`, `lctx_swap`,
   `with_mvar_local_context`
7. `get_instances` — className up front, the append, ordering,
   `synthOrder`
8. the `global_name: None` doc rewrite and downstream audit
9. `Synth0.lean` declarations and the fixture records
10. neutrality measurement across both corpora
11. seam audit and whole-branch review
