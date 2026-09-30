# M4b-4a — dot notation, the LVal machinery, and term-level postponement — design spec

## Where this sits

M4b-3 shipped the application elaborator, the synthetic-mvar fixpoint,
coercions and literals, and its close-out and follow-ups (#45, #46,
#47, #48) cleared every seam that did not belong to a later slice.
The roadmap row for M4b-4 (`2026-07-25-m4b3-application-elaborator-design.md`,
§ Where this sits) lists four constructs:

| Construct | State on `main` @ `e541220` | Disposition |
|---|---|---|
| dot notation (`proj` / `pipeProj` / `dotIdent`) | parsed, deliberately unrouted (`dispatch.rs`) | **this spec** |
| anonymous constructor `⟨⟩` | parsed (`leanr_syntax` `term.rs`, `anonymousCtor`) | M4b-4b, own spec |
| `elabAsElim` | recursor heads seamed in `app/head.rs` | M4b-4c, own spec |
| `binop%` | **not parsed**; `a + b` reaches it only through macro expansion | re-homed to the macro-expansion slice |

Two further items were later pinned to "M4b-4": the match slice's
`withLocalInstances` reading the stored `LocalDeclKind`, and
`useImplicitLambda`'s `.postpone` arm. Match needs the matcher/equation
compiler, which the roadmap places in **later M4**; it keeps its own
slice. The `.postpone` arm is closed here (§ P2), because the dot-notation
machinery is the first real producer of postponement.

M4b-4 is therefore decomposed into independent specs, each with its own
spec → plan → PR cycle. This is the first: **M4b-4a**.

Pinned oracle: `leanprover/lean4:v4.33.0-rc1`. Citations are against
that toolchain's `src/lean/Lean/Elab/App.lean`,
`src/lean/Lean/Elab/Term/TermElabM.lean` and `src/lean/Lean/Structure.lean`,
each opened while writing this spec. The pin is not bumped.

## Evidence

Run, not read: `lean` from the pinned toolchain on a scratch
`prelude`-mode file importing the committed `tests/fixtures/elab/Elab0.olean`
(`LEAN_PATH=tests/fixtures/elab`), `#check` per line.

| Term | Oracle | leanr today |
|---|---|---|
| `fun (p : Prod Nat Nat) => p.1` | `fun p => p.fst` | `UnsupportedSyntax` (proj unrouted) |
| `fun (p : Prod Nat Nat) => p.fst` | `fun p => p.fst` | `UnsupportedSyntax` |
| `fun (p : Prod Nat Nat) => p \|>.2` | `fun p => p.snd` | `UnsupportedSyntax` |
| `(Nat.zero).succ` | `Nat.zero.succ` | `UnsupportedSyntax` |
| `(fun x => x.1) (Prod.mk Nat.zero Nat.zero)` | accepted, `x.fst` | `UnsupportedSyntax` |
| `fun x => x.1` | **rejected**, "Type of x is not known" | `UnsupportedSyntax` |

The last two rows are the case for § P2: the oracle accepts the fifth
only because `x.1` is **postponed** until `x`'s type is unified with
`Prod Nat Nat`, and rejects the sixth only when the postponed term is
resumed with postponement disallowed. Without postponement both are
rejected.

## Scope

**In.** Everything `elabAppFn` (`App.lean:2060-2138`) does for the
field, fieldIdx, pipeProj, dotIdent, `@`-prefixed, `_` and generic
arms; the LVal resolution machinery (`App.lean:1435-1897`);
`resolveDottedIdentFn` (`App.lean:1985-2058`); the field split in
`resolveName`/`resolveName'` (`TermElabM.lean:2170-2208`); the
`structureExt` decode and the `Structure.lean` accessors these need; and
term-level postponement (`TermElabM.lean:1049`, `:1370-1388`,
`:1608-1661`, `:1843-1854`).

**Out.** See § Seams and § Out of scope; every excluded item names its
owner.

## Architecture: three layers

### `leanr_olean` — decode `structureExt`

A typed decode of `Lean.structureExt` entries, following the
`ClassEntry` / `ProjectionFnInfo` pattern in `module_data.rs`:

```text
StructureInfo       { struct_name, field_names: Vec<NameId>,
                      field_info: Vec<StructureFieldInfo>,
                      parent_info: Vec<StructureParentInfo> }
StructureFieldInfo  { field_name, proj_fn, subobject: Option<NameId>, binder_info }
StructureParentInfo { struct_name, subobject: bool, proj_fn }
```

Oracle shapes: `Structure.lean:25-67`. `field_info` is stored sorted by
`fieldName` (`Name.quickLt`) as the oracle does; `field_names` keeps
constructor order (`s.3` is `field_names[2]`). The deprecated
`autoParam?` is decoded (so the object layout is walked correctly) and
dropped. Per-module entry arrays are sorted by `StructureInfo.lt`
(`exportEntriesFn`, `Structure.lean:87-92`).

`structureResolutionExt` (`Structure.lean:421`) is a non-persisted
cache; nothing is decoded for it.

`.olean` bytes are untrusted (`docs/THREAT_MODEL.md`): the decoder
returns an error, never panics, on any malformed object.

### `leanr_meta` — additive structure accessors

TCB-neutral read accessors on `MetaCtx`, each the port of one oracle
function:

| leanr | oracle |
|---|---|
| `get_structure_info` | `getStructureInfo?` (`Structure.lean:126`) |
| `is_structure` | `isStructure` (`:270`) |
| `get_structure_fields` | `getStructureFields` (`:157`) |
| `get_field_info` | `getFieldInfo?` (`:161`) |
| `find_field` | `findField?` (`:197`), recursing through subobjects |
| `get_path_to_base_structure` | `getPathToBaseStructure?` (`:338`): subobject fields first, then other parents, with a visited set |
| `get_structure_resolution_order` | `getStructureResolutionOrder` (`:512`), the C3 merge in **relaxed** mode, memoized in `MetaCtx` as the oracle caches it |

`unfold_definition` and `whnf_core` already exist and are reused.

### `leanr_elab` — the LVal machinery

A new module `app/lval.rs` holding:

- `LVal` — `FieldName { r#ref, name, levels, suffix: Option<Name>, full_ref }`
  and `FieldIdx { r#ref, idx, levels }` (oracle `LVal`, `TermElabM.lean:662`).
- `LValResolution` — `ProjFn { base, struct_name, field, levels }`,
  `ProjIdx { struct_name, idx }`, `Const { base, struct_name, const_name, levels }`,
  `LocalRec { base, fvar }` (`App.lean:1435-1447`).
- One function per oracle function, same names, same order of effects:
  `consume_implicits` (`:1659`), `resolve_lval_aux` (`:1517`),
  `resolve_lval_loop` (`:1678`), `mk_base_projections` (`:1700`),
  `type_matches_base_name` (`:1712`), `find_method` (`:1453`),
  `add_lval_arg` (`:1735`), `elab_app_lvals` (`:1843-1897`).

`app/head.rs`'s `elab_app_fn` grows the remaining `elabAppFn` arms and
threads an `lvals` list through, as the oracle does. `resolve.rs` grows
the field split. `dispatch.rs` routes `Term.proj`, `Term.pipeProj` and
`Term.dotIdent` to `app::elab_atom` (the oracle aliases them to
`elabAtom`, `App.lean:2247-2248`, `:2273-2274`; `elabPipeProj`
desugars at `:2250-2258`).

### Fixture

`tests/fixtures/elab/Elab0.lean` grows:

- structures with `extends`: a subobject chain (`C extends B`, `B extends A`);
- a diamond whose second parent overlaps a field of the first, so it is
  a **non-subobject** parent and the C3 order is non-trivial;
- a one-constructor `inductive` (not `structure`), for `ProjIdx`;
- namespace methods (`Nat.foo`, `B.bar` inherited by `C`);
- a `Function.*` constant;
- a structure with a `CoeFun` instance, for `add_lval_arg`'s coercion path;
- a `def` alias of a structure type, for the `unfold_definition` retry.

Regenerated with `mise run fixtures:regen`. Every existing corpus record
must stay byte-identical (the additions are new declarations only).

## Sub-plans

Four sub-plans, one PR each. P2 and P3 are independent of each other
and both follow P1; P4 needs both.

### P1 — structures and projections

- `structureExt` decode; the meta accessors except
  `get_structure_resolution_order`.
- `LVal` / `LValResolution`; `consume_implicits`; `resolve_lval_loop`
  including `isMVarApp` → `synthesizeSyntheticMVarsUsingDefault`
  (`App.lean:1682-1683`) and the `.error`-only `unfold_definition` retry
  (`:1687-1694`).
- `resolve_lval_aux`: the `fieldIdx` arms (`ProjFn` for structures,
  `ProjIdx` for other one-constructor inductives, the index and
  explicit-universe errors) and the structure-field `fieldName` arm
  (`find_field` → `ProjFn`), plus the `forallE`/`mvar`/other error arms
  that do not need `Const`.
- `mk_base_projections`; the `ProjIdx` path via `mkProjAndCheck`
  (`App.lean:65`); the `ProjFn` path through `elabAppArgs` with the
  `(self := …)` named argument carrying `numImplicitParams`
  (`:1857-1872`) — which removes the `app/args.rs:371` seam.
- Head arms: `e.f`, `e.1`, `e.f.{u}`, `e.1.{u}` on an arbitrary `e`, and
  `elabAppFn`'s generic branch (`App.lean:2120-2138`: `elabTerm f none`
  then `elabAppLVals`), which also retires `head.rs`'s "general term in
  function position" seam.
- **Named seams left by P1:** `tryPostponeIfMVar` in
  `resolve_lval_loop` raises a named seam owned by P2 when
  `may_postpone` holds and the type is an mvar application (when it does
  not hold, the oracle's call is a no-op and P1 proceeds exactly as it
  does); the `Const` resolution and the `Function` namespace arm are
  seams owned by P3; `LocalRec` is owned by the `let rec` slice (§ Seams).

### P2 — term-level postponement

leanr has the **resume** side (`SyntheticMVarKind::Postponed`,
`synthetic/ladder.rs`'s `resume_postponed`) but no producer:
`may_postpone`'s only reader is P1's seam in `resolve_lval_loop`, whose
`false` branch nothing reaches yet, and nothing throws or catches a
postponement. P2 adds:

- a postpone outcome distinct from `ElabError` errors (the oracle's
  `Exception.internal postponeExceptionId`), so `.error`-only catch
  sites — the LVal retry, `resolveDottedIdentFn`, `observing` — pass it
  through untouched;
- `try_postpone`, `is_mvar_app` (whnfR head is an mvar),
  `try_postpone_if_mvar`, `try_postpone_if_none_or_mvar`
  (`TermElabM.lean:1370-1388`), all reading `may_postpone`;
- `without_postponing` (`:1049`), and the existing `with_synthesize`
  scopes setting `may_postpone` as the oracle's do;
- the catch in `elabUsingElabFnsAux` (`:1635-1651`): when
  `catchExPostpone`, **restore the saved state** (discarding synthetic
  mvars the failed attempt registered) and `postponeElabTermCore`
  (`:1449`), creating a `.postponed` synthetic mvar;
- the `.postpone` arm of `useImplicitLambda` in `elabTermAux`
  (`:1843-1854`), closing `elab.rs`'s named seam;
- `synthetic/report.rs`'s stuck-`Postponed` report, closing its seam.

P2 converts P1's LVal postponement seam into the real call, and gives
the resume path its first successful producer (the coverage gap the
P2a plan recorded).

### P3 — generalized field notation

- `get_structure_resolution_order` (C3, relaxed).
- `find_method` (`App.lean:1453-1478`): try `S.f`, then each namespace
  in the resolution order after `S`; an ambiguity is an error.
- The `Const` arm of `resolve_lval_aux` and the `Function` namespace
  arm for pi types (`:1580-1588`).
- `type_matches_base_name` (`:1712-1726`, `withReducibleAndInstances`).
- `add_lval_arg` (`:1735-1828`): the `forallMetaTelescope` walk under
  `withoutModifyingState`, positional insertion when the parameter is
  explicit (or `@`-explicit) and fits, the named-argument fallback, the
  `whnf` continuation, and the `coerceToFunction?` continuation that
  disables named insertion.
- `mk_base_projections` for `Const` when base ≠ struct; chained lvals
  (the non-final `elabAppArgs` calls with no expected type in
  `elabAppLValsAux`, e.g. `:1882`).

### P4 — identifier forms

- `resolveName`'s field split (`TermElabM.lean:2170-2192`): a local
  first (`resolveLocalName`: longest local prefix, remaining components
  as fields), then the longest global prefix whose remaining components
  become fields; universe levels attach to the last field.
- `elabAppFnResolutions` (`App.lean:1926-1950`) building
  `LVal::FieldName` with `suffix?` on the first field.
- `pipeProj` (`e |>.f args`).
- `dotIdent` via `resolveDottedIdentFn` (`:1985-2058`):
  `tryPostponeIfNoneOrMVar`, `withForallBody` over
  `whnfCoreUnfoldingAnnotations`, constant namespace → candidates or a
  local, the `unfold_definition` retry collecting earlier failures.
- The `@`-prefixed variants (`:2110-2117`), the `_` arm (`:2119`), the
  `namedPattern` error arm (`:2098-2100`).

## Errors

**Control flow is oracle-faithful; prose is not ported** — the M4b-3
precedent. Every oracle throw site becomes a typed `ElabError` variant
carrying enough structure for a test to identify the site:

| Variant | Oracle sites |
|---|---|
| `InvalidProjection { reason }` — `IndexZero`, `IndexOutOfRange { idx, num_fields }`, `NoFields`, `NotOneCtor`, `OnFunction`, `TypeUnknown`, `NotConstApp`, `ExplicitUnivsOnInductive` | `App.lean:1521-1551`, `:1589-1591`, `:1601-1603`, `:1614-1617` |
| `InvalidField { field, full_name, reason }` — `NotFound`, `TypeUnknown`, `NotConstApp` | `:1578`, `:1588`, `:1593-1600`, `:1609-1612` |
| `AmbiguousField { field, candidates }` | `findMethod?`, `:1466-1468` |
| `UnusableLValParameter` / `NoLValParameter` | `addLValArg`, `:1772`, `:1792-1794` |
| `InvalidDottedIdent { reason }` — `NotAtomic`, `NoExpectedType`, `Sort`, `NotConstApp`, `UnknownConstant` | `resolveDottedIdentFn` |
| `NamedPatternOutsidePattern`, `PlaceholderAsFunction` | `elabAppFn`, `:2099`, `:2119` |

The two `c ++ suffix` arms (`:1584-1586`, `:1606-1608`) — an
identifier like `Nat.zero.foo` whose split-off field fails — raise the
existing `UnknownIdent` with the rejoined name.

`resolveLValLoop` and `resolveDottedIdentFn` retry on `.error` only and
rethrow internal exceptions; leanr maps this to: postponement and
`ElabError::Meta` internal failures pass through, every other variant
triggers the retry. `resolveDottedIdentFn` logs its earlier failures
before rethrowing the last; leanr has no message log, so only the last
is returned (a named gap, § Seams).

**UI-only machinery not ported** (none of it changes the term produced
or whether it is accepted): `mkTupleHint`, `reverseFieldLookup`,
`@[suggest_for]` suggestions, `throwUnknownNameWithSuggestions`,
`addTermInfo` / `addProjTermInfo` / `addDotCompletionInfo` /
completion info, `checkDeprecated`, and the exporting-scope private
retry hint (`:1571-1577`).

`isInaccessiblePrivateName` (`:1860`, `:2024`) does change
acceptance. It is ported if leanr's environment models private names by
the time the task lands; otherwise it is a named seam.

## Seams after P4

| Seam | Owner |
|---|---|
| `LocalRec` (needs `auxDeclToFullName`, no leanr producer) | the `let rec` / `where` slice |
| `choice` fan-out, `observing` / `errToSorry` | the slice that grows `resolve_global` (overloading) |
| `findMethod?` / `dotIdent` candidate resolution uses exact names only (the oracle clears `currNamespace` but still honours `open`) | the `open` / alias slice |
| auto-bound implicit and the unknown-id variants of `elabAppFnId` | the declaration layer |
| `inPattern` | the match slice |
| `resolveDottedIdentFn`'s logged intermediate failures | the slice that adds a message log |
| `isInaccessiblePrivateName`, if not ported | the slice that models private names |

`tests/seam_audit.rs` and `dispatch.rs`'s deferral table are reconciled
at the end of every sub-plan, not only the last.

## Testing

**Oracle corpus (primary).** Each sub-plan appends `(id, src)` queries
to `dump_elab.lean` against the extended `Elab0` and regenerates
`elab-queries.jsonl`; `oracle_elab_gate` requires byte-identical terms.

- **P1:** `p.1`, `p.2`, `p.fst` on `Prod`; a direct field; an inherited
  field through the subobject chain and through the diamond's
  non-subobject parent; `.{u}` on a field; `ProjIdx` on the
  one-constructor inductive; a projection needing `consume_implicits`;
  the `unfold_definition` retry through the `def` alias; `(f) a`.
- **P2:** `(fun x => x.1) (Prod.mk a b)`; the implicit-lambda
  `.postpone` case; postponement under a nested `with_synthesize`; a
  chain `((f.x a).x b)` whose inner postponement is discarded on restore.
- **P3:** a namespace method (`(Nat.zero).foo`); a method inherited via
  the C3 order; `Function.*` on a pi-typed term; positional versus
  `(x := e)` insertion; a `CoeFun` head; chains such as `p.1.succ`.
- **P4:** local `x.f.g`; global `Nat.zero.succ`; `e |>.f a`; `.ctor`
  against an expected type, through a pi type, through an unfold; a
  postponed `.ctor` resolved on resume.

**Rejections.** The corpus is success-only, so each error variant gets a
smoke test (`app_smoke.rs` / `synthetic_smoke.rs`) asserting the variant
and its reason. Every "the oracle rejects this" claim is run on the
pinned binary during planning and the command cited in the test's
comment. No reject tier is added to the corpus harness.

**Lower layers.** `leanr_olean`: a decode test on `Elab0.olean`
(fields in constructor order, `field_info` sorted, subobject and
non-subobject parents), plus the new decoder under the existing
truncation / no-panic tests. `leanr_meta`: one test per accessor; the
C3 order and `getPathToBaseStructure?` results are compared against
values the **oracle dumps** for every fixture structure (a small
addition to `dump_elab.lean`), never hand-computed.

**Discipline.**

- Every new test is shown to discriminate: the task brief names the
  mutation, the implementer runs it and sees red, the reviewer re-runs it.
- Every oracle `file:line` citation in plans and comments is opened
  against the pinned toolchain.
- `mise run ci` (fmt, clippy, full suite) runs to completion, blocking,
  before every push.
- `parse:mathlib:fast` is unaffected (no parser change) and is not a
  gate for this slice.

## Out of scope

- `⟨⟩` (M4b-4b) and `elabAsElim` (M4b-4c) — their own specs.
- `binop%` — the macro-expansion slice (it is unparsed, and `a + b`
  reaches it only through macro expansion).
- Match / `withLocalInstances` reading `LocalDeclKind` — later M4's
  match slice.
- Overload resolution, `open` / alias / `export` / `_root_` — the
  `resolve_global` slice.
- Structure instances `{ x := … }` — later M4.
- The `lean-toolchain` pin.

## Next

Implementation plan for **P1** via the writing-plans skill; P2–P4 are
planned one at a time after their predecessor merges.

**P2 amendments (found while planning, measured)**

- **A third producer: `elabAppArgs`' `tryPostponeIfMVar fType`**
  (`App.lean:1366-1367`), which the list above omits. leanr skipped the
  call, a silent divergence with no seam: `(fun f => f Nat.zero) Nat.succ`
  elaborates in the oracle and raised `FunctionExpected` in leanr. It sits
  in the control flow P2 builds, so P2 owns it.
- **`synthetic/report.rs`'s `Postponed` arm is not a seam.** It is the
  oracle's `| _ => unreachable!` (`SyntheticMVars.lean:316`) and stays an
  internal-invariant error. The only route to it is `check_occurs`
  failing, which needs a synthetic `sorry`; leanr mints none.
- **"The existing `with_synthesize` scopes setting `may_postpone`" is
  wrong.** The oracle's `withSynthesize` never touches `mayPostpone`; only
  `withoutPostponing` does (`TermElabM.lean:1049-1050`), and the ladder's
  rungs 2 and 4 already use it. Nothing to change.
- **`is_mvar_app` becomes exact (`whnfR`).** P1 carried this forward. It
  needs `MetaCtx::whnf_r` widened from `pub(crate)` to `pub`, an additive
  change covered by the elab-to-meta accessor precedent.

**P3 amendments (found while planning, measured)**

1. **`AmbiguousField` is not added.** `findMethod?` throws it only when
   `resolveGlobalName` returns two or more candidates (`App.lean:1466-1468`).
   leanr resolves exact names only, so there is never more than one
   candidate; the variant would be dead code with no test. It belongs to the
   owner of the seam "`findMethod?` candidate resolution uses exact names
   only" (the `open`/alias slice), which adds it together with the
   resolution that can reach it.
2. **An extra `leanr_meta` accessor: `forall_meta_telescope`** (non-reducing,
   `Meta/Basic.lean:1752-1753`), outside the structure-accessor table.
   `addLValArg` needs it (`App.lean:1751`) and reads each mvar's `userName`
   (`:1756-1757`). leanr's only telescope,
   `forall_meta_telescope_reducing`, mints anonymous `Natural` mvars: it
   would reduce (wrong, `:1782` does the `whnf` itself) and lose the names.
   Minting goes through a generalized `mk_aux_mvar_at` that also takes a
   `user_name`. Additive, under the M4b elab-to-meta accessor precedent.
3. **A new error variant, `MaxRecDepth`**, for `addLValArg.go`'s
   `withIncRecDepth` (`App.lean:1749`; `Exception.lean:226`). Measured:
   `CoeFun Loop (fun _ => {u : Nat} -> Loop)` makes the oracle report
   "maximum recursion depth has been reached".
4. **`findMethod?` on a private structure name is a seam.** The oracle
   applies `privateToUserName` (`App.lean:1456`). leanr models no private
   names (P1's `isInaccessiblePrivateName` seam, same owner). The fixture
   has no private structure.
5. **The C3 merge carries a cycle guard.**
   `computeStructureResolutionOrder` recurses over `parentInfo` with no
   guard (`Structure.lean:462-470`). `structureExt` rows are untrusted, so a
   doctored parent cycle returns `None` rather than overflowing the stack,
   matching P1's `find_field` and `get_path_to_base_structure`.
6. **`MaxRecDepth` is not an oracle error for catch purposes.**
   `ElabError::is_oracle_error` excludes it: the oracle's `Core.tryCatch`
   (`CoreM.lean:792-799`) rethrows runtime exceptions
   (`Exception.isRuntime`, `:783-784`) before any catch arm. This
   supersedes the plan constraint "every new error variant is an oracle
   error".
7. **`addLValArg.go`'s two tail recursions are a loop in leanr**
   (`add_lval_arg_go`). The recursive form overflowed the debug-build Rust
   stack at depth ~385, before the 512 cap.

**P4 amendments (found while planning, measured)**

1. **`resolveDottedIdentFn`'s local-context candidate is not ported**
   (`App.lean:2034-2037`). It resolves `fullName = C ++ id`, which always has
   two or more components, and oracle locals are atomic
   (`ensureAtomicBinderName`, `Binders.lean:188-191`: "invalid binder name
   `x.a`, it must be atomic"). Only an auxiliary `let rec`/`where`
   declaration could match, and leanr's local context holds none. Owned by
   the `let rec`/`where` slice, on the P3 `AmbiguousField` precedent; its
   `throwInvalidExplicitUniversesForLocal` (`:2035-2036`) goes with it.
2. **New variant `InvalidExplicitUniversesForLocal`**
   (`TermElabM.lean:2160-2161`), raised by `resolveName`'s `processLocal`
   (`:2172-2179`). leanr silently dropped the levels on
   `fun (x : Nat) => x.{0}`; the oracle rejects it. A silent
   over-acceptance, closed by P4.
3. **New variant `NamedPatternOutsidePattern { as_function }`**, with the
   oracle's two throw sites: `x@Nat.zero` gets `elabNamedPatternErr`'s
   message (`BuiltinTerm.lean:443-444`; `elabNamedPattern := elabAtom`,
   `App.lean:2247`, is registered too but is not the one that answers), and
   `x@Nat.succ Nat.zero` gets `elabAppFn`'s "Expected a function, but found
   the named pattern" (`App.lean:2098-2100`).
4. **`LVal::FieldName.suffix` is the rejoined field text
   (`Option<String>`); `fullRef` is not added.** `suffix?` only feeds the
   unknown-constant error `c ++ suffix` (`App.lean:1584-1586`,
   `:1606-1608`), whose leanr form is `UnknownIdent(String)`; `fullRef` is
   only the error position.
5. **Reserved names are a named follow-up, not a seam.** The oracle's
   `realizeGlobalName` (`TermElabM.lean:2190`) realizes reserved names on
   demand: `pick.eq_1` elaborates to the equation lemma. leanr splits it
   into `pick` plus a field `eq_1` and reports `UnknownIdent("pick.eq_1")`.
   Reject-only. Owner: the slice that grows `resolve_global_name`.
6. **`whnfCoreUnfoldingAnnotations` is ported but nothing observable
   depends on it.** An annotated expected type it would unfold
   (`optParam Nat Nat.zero`) fails as a namespace (`optParam.zero`) and
   reaches the same constant through the `unfoldDefinition?` retry. Only the
   oracle's logged intermediate errors differ, and leanr has no log.
7. **`resolveLocalName`'s longest-prefix order is not observable.** With
   single-component local names only one prefix can match. The loop is
   ported as the oracle writes it.
8. **The escape convention is `intern_dotted`'s** (decision, not oracle
   behaviour): split on every `.` and keep `«»` verbatim. Binder names are
   interned whole as one component, so unescaping only the identifier side
   would break `fun («x» : Nat) => «x»`, which works today. Consequence:
   the oracle accepts `fun («x» : Nat) => x.succ`, `Nat.«zero».succ` and
   `fun (s : S2) => s.«toS1».a`, and leanr rejects them (reject-only,
   recorded under § Landed › P4).

## Landed

### P1 — structures and projections (PR #49)

- `structureExt` decoded (`leanr_olean`: `StructureInfo`, keyed by the
  private `_private.Lean.Structure.0.Lean.structureExt`); `leanr_meta`
  structure accessors, checked against `tests/fixtures/elab/structures.jsonl`
  (oracle-dumped by `dump_structs.lean`).
- `app/lval.rs`: `consumeImplicits`, `resolveLValLoop` (default-instance
  unblock, unfold retry that never retries a seam), `resolveLValAux`'s
  fieldIdx / structure-field / forall / mvar / other arms,
  `mkProjAndCheck`, `mkBaseProjections`, `elabAppLValsAux` for
  `projIdx` / `projFn`; `numImplicitParams`; `elabAppFn`'s proj,
  explicitUniv, hole and generic arms; `@` on projections.
- `@` on projections follows the oracle's rows exactly (`App.lean:2110-2116`,
  `:2262-2268`): `@(e).1`, `@(e).f` and `@(e).f.{us}` are accepted, and
  `@(e).1.{us}` has no row — `UnsupportedSyntax` citing `App.lean:2118`
  in a function position (the oracle's "unexpected syntax"), the
  `` `(@$t) `` arm in a term position (`lval_smoke.rs`'s
  `explicit_on_projection_heads_matches_the_oracle`).
- Corpus: 32 records under `lval/`, including a parametric,
  universe-polymorphic subobject chain (`PD extends PC extends PB`,
  `lval/param-chain-*`) that pins `mkBaseProjections`' reuse of the
  type's arguments and levels, a guillemet-escaped field
  (`lval/escaped-field`) and `@` on projection heads in function
  position. Rejections: `tests/lval_smoke.rs`.
- `elab_app_fn` rejects explicit universes on any head other than an
  identifier, `proj` or `dotIdent` with `IllFormedSyntax` citing
  `Parser/Term.lean:938-950`: the oracle's parser refuses those trees
  (`checkStackTop isIdentOrDotIdentOrProj`, which leanr_syntax skips),
  and every other arm would drop or overwrite the levels.
- `find_field` carries a visited set, like `get_path_to_base_structure`:
  a doctored `structureExt` subobject cycle is an error, not a stack
  overflow (`lval_smoke.rs`).
- Seams left, each naming its owner: postponement (P2), `.const` /
  `Function` (P3), `pipeProj` / `dotIdent` / `namedPattern` (P4),
  `choice` (overloading slice), private projections (private-names
  slice), `LocalRec` (`let rec` slice).
- Field-name access through a `def` alias is P3's to flip to success:
  `fun (s : S3Alias) => (s).a` is pinned as a P3 seam in
  `lval_smoke.rs` (ruling R8), where the oracle elaborates it to
  `S1.a (S2.toS1 (S3.toS2 s))` after `findMethod?` fails and the unfold
  retry runs. The unfold retry itself is covered in P1 through a field
  index, by `lval/unfold-alias-idx`.
- Known approximation carried forward: `is_mvar_app` has no `whnfR`
  (P2 owns making it exact) (closed in P2).
- Every stale `M4b-4` seam message was retargeted to its owner (P2, P3,
  P4, `M4b-4c` for `elabAsElim`, `M4b-4b` for `⟨⟩`, the match /
  macro-expansion / overloading slices); `seam_audit.rs`'s
  `no_seam_message_names_a_completed_slice` now carries an `M4b-4a P1`
  needle, measured non-vacuous.

### P2 — term-level postponement (PR #50)

- `ElabError::Postpone` (internal exception, never reaches a caller of
  `elab_term_and_synthesize`); `postpone.rs`; `elab_using_elab_fns` (catch
  with state and `lctx` restore); `resume_elab_term` / `resume_postponed`
  (catch off; restore on a postponement and, under `postponeOnError`, on
  an oracle error only — a seam or `Meta`/`Internal` failure propagates,
  `ElabError::is_oracle_error`, shared with `resolve_lval_loop`).
- Producers: `useImplicitLambda` `.postpone`, `resolveLValLoop`, and
  `elabAppArgs`. The last was missing from the spec;
  `(fun f => f Nat.zero) Nat.succ` had been a silent `FunctionExpected`.
- `is_mvar_app` is exact (`whnf_r` is `pub`).
- Corpus: 11 `p2/*` records, including `p2/lval-two-postponements`
  (two postponements resumed, restoring the coverage the
  `p2/lval-two-binders` source swap lost). Rejections: `lval_smoke.rs`,
  `app_smoke.rs`. Mechanics: `postpone_smoke.rs`.
- **Known cost:** `elab_using_elab_fns` clones the `Term.State` tables and
  mctx assignment maps on every caught elaboration, where the oracle's
  `saveState` is O(1). The owner is whichever slice first measures
  elaboration throughput. It is not a correctness seam.
- The `.postpone` seam test in `seam_audit.rs` and P1's LVal postponement
  seam are closed; `no_seam_message_names_a_completed_slice` carries an
  `M4b-4a P2` needle, measured non-vacuous. `tryPostponeIfNoneOrMVar` has
  no production caller until P4.
- Open follow-ups:
  - Pre-existing, independent of postponement: unnormalized `max 0 0`
    universe levels in nested `Prod.mk`. This forced swapping the source of
    the `p2/lval-chain` and `p2/lval-reducible-alias` corpus records.
  - Pre-existing: `StuckCoercion` when applying a lambda whose later binder
    type is a hole, e.g. `(fun x y => y) Nat.zero Nat.zero` (forced the
    `p2/lval-two-binders` source swap) and `(fun (x : Nat) f => f) Nat.zero
    Nat.succ`. Root cause: leanr has no `numScopeArgs` constant
    approximation (`Meta/ExprDefEq.lean:1271-1278`, `processConstApprox`).
  - The same gap blocks the corpus record the plan wanted,
    `p2/app-fn-after-lval`: `(fun x f => f x.1) (Prod.mk Nat.zero Nat.zero)
    Nat.succ` gives `FunctionExpected` while the oracle accepts it. The
    record was dropped, so nothing tests the lval producer feeding an
    mvar-typed app head.
  - `(fun f x => Nat.succ x.1) Nat.succ (Prod.mk Nat.zero Nat.zero)` gives
    `InvalidProjection{TypeUnknown}` while the oracle accepts it. Probed:
    annotating only `f : Nat -> Nat` still fails, annotating `x : Prod Nat
    Nat` passes, so `x`'s type is a scope-dependent mvar (`?γ f`) resumed as
    `?γ Nat.succ =?= Prod Nat Nat`. Consistent with the `numScopeArgs` gap;
    not confirmed by a fix.
  - `p2/lval-reducible-alias` and the `fun (x : outParam _) => x.1`
    rejection do not pin `whnfR`; only `postpone_smoke.rs`'s
    `is_mvar_app_sees_through_reducible_definitions` does.
  - `(fun x => Prod.fst x) (Prod.mk Nat.zero Nat.zero)` gives
    `Meta(DepthBudgetExhausted)` while the oracle accepts it. It already
    fails on main (71bfe59), so it is not a P2 regression.
  - `elab.rs`'s implicit-lambda wrap passes `catch_ex_postpone` on to
    `elab_using_elab_fns`; hard-coding `true` there survives every test.
    The only reachable case needs a postponed term whose type later becomes
    an implicit forall while it still postpones. It is unpinned.
  - For P4: dotted identifiers on a local (`x.succ`, `x.fst`) give
    `UnknownIdent` while the oracle accepts them. This predates the branch;
    P4 owns the local field split.

### P3 — generalized field notation (PR #51)

- What landed: the C3 structure resolution order (with the cycle guard),
  `forall_meta_telescope` (`leanr_meta`), `find_method`, the
  `LValResolution::Const` arms (`.const` heads and `Function.f`),
  `type_matches_base_name`, and `add_lval_arg` with both continuations
  (`whnf` and `CoeFun`) and the 512 depth cap (`MaxRecDepth`, a loop in
  `add_lval_arg_go`, not catchable). `localRec` is the only unported
  `LValResolution` arm.
- Corpus: 26 `p3/*` records (the plan said 25; `p3/explicit-unusable-name`,
  `fun (s : S1) => @(s).bad Nat.zero`, was added on a controller ruling
  because mutation J survived `p3/explicit-positional`); 234 records in
  total. Extra fixture declarations beyond the plan: `CX/CA/CP/CQ/CD` (C3
  relaxed-path fixture: mutation B survived the plan's fixture) and
  `FnJ`/`S1.viaFnJ` (two-coercion fixture: the pre-coercion-head mutation is
  equivalent on single-coercion input).
- Rejections live in `lval_smoke.rs`.
- The P1 debt is closed: `fun (s : S3Alias) => (s).a` is `p3/alias-field`,
  and the `S3Alias` `.zzz` rejection now names `S3.zzz`.
- No corpus record was dropped under the `numScopeArgs` decision.
- Open follow-ups:
  - `self_reproducing_coe_fun_hits_max_rec_depth` has thin stack headroom in
    debug: it passes at 1.5 MiB and overflows at 1.25 MiB (default test
    thread 2 MiB). Some recursion over the ~1000-deep coerced term is
    unguarded; `infer`, `instantiate_mvars` and kernel subst are
    stacker-guarded, so the location is not yet found. Not attributed to
    `leanr_meta`.
  - No end-to-end test observes `MaxRecDepth`'s non-catchability (only the
    unit assertion `max_rec_depth_is_not_catchable`): no current path lets
    it reach a catch site with an observable difference.
  - `findMethod?` candidate resolution is exact-name only, so
    `AmbiguousField` is absent (amendment 1) and private structure names are
    unmodelled (amendment 4); both belong to their named owner slices.
  - Elab0.lean's Task 1 comments carry drifted oracle cites (for example
    `App.lean:1712-1726`, `:1764-1776`); unverified and untouched.
  - Mutation I (the named-eta `Vec::insert` path) dies by panic, so the
    oracle gate does not list which records diverge.
  - Initialising `add_lval_arg`'s `unusable` empty instead of from the
    user's named-arg names (`lval.rs:611`) survives every test. The
    observable case is `def T.f (t : Nat) {t : T}` with `(x).f (t := 1)`:
    the oracle gives `UnusableLValParameter`, and the mutant would push a
    duplicate named argument and fail differently.
  - `type_matches_base_name`'s `TransparencyMode::Instances` versus
    `Reducible` is not discriminated (`lval.rs:534`, `:547`). Only Default
    versus Instances is (the `S1Df` test). Discriminating it needs an alias
    that is instance-reducible but not reducible.
  - After a whnf continuation, `NoLValParameter.f` holds `mkAppN f xs`,
    which references rolled-back telescope mvars (`lval.rs:744`). The
    oracle only prints `f.getAppFn.eta`. Whoever ports the error prose
    should render `app_fn(f)`.

### P4 — identifier forms (PR #<n>)

- What landed: `resolve_local_name` / `resolve_global_name` (replacing
  `resolve_global`; two callers in `builtin/lit/mod.rs` pass a single prefix,
  `resolve_global_name(&view, &[cname], name)`, which keeps them
  exact-name), `elab_app_fn_id` with `suffix`, the two `c ++ suffix` arms of
  `resolve_lval_aux`, `pipeProj`, `namedPattern`, `resolve_dotted_ident_fn`
  (`app/dot_ident.rs`) with `withForallBody` and
  `whnfCoreUnfoldingAnnotations`, and `@.c`. One addition beyond the plan:
  the recursor guard (`elabAsElim?`, `App.lean:1373`, `:1399-1401`) also
  covers a dot-identifier head, so `(.rec … : Nat)` raises the M4b-4c seam,
  pinned by a `seam_audit` case. Whoever owns M4b-4c must lift it together
  with `elab_app_fn_id`'s guard.
- Nested `|>.` with arguments (final-review fix): `elabAppFn`'s pipeProj
  patterns (`App.lean:2085-2097`) have no `$args*`, and `elabPipeProj`
  (`:2250-2258`) strips the arguments only from the node it was handed. So
  an inner `|>.` that still carries arguments, the base of an outer `|>.`,
  takes the generic arm (`:2120-2138`) and is elaborated whole. leanr's
  pipeProj arm now does the same for any pipeProj with arguments other than
  `call.stx`. Before the fix, `s |>.addTo Nat.zero |>.succ` was wrongly
  rejected and `s |>.addTo Nat.zero |>.twice` was silently accepted as
  `Function.twice`. Pinned by `p4/pipe-nested-args`, `p4/pipe-nested-named`,
  `p4/pipe-nested-deep` and `lval_smoke`'s
  `nested_pipe_projection_keeps_the_inner_arguments`.
- Corpus: 42 `p4/*` records, 276 in total. No corpus term was dropped under
  the `numScopeArgs` decision. Every plan mutation discriminates except the
  three survivors listed under the follow-ups below (U, R′ and probe S′),
  which the plan predicted or the controller ruled on; tasks 2 and 3 split
  tests so no assertion masked another.
- Rejections live in `lval_smoke.rs`.
- The P2 note is closed: "For P4: dotted identifiers on a local … give
  `UnknownIdent`" no longer holds (`p4/local-*`).
- The `seam_audit` needle `M4b-4a P4` was added and measured non-vacuous.
  After this slice no seam in the crate names M4b-4a.
- Open follow-ups:
  - Escape-convention divergences (amendment 8), all reject-only:
    `fun («x» : Nat) => x.succ`, `Nat.«zero».succ`,
    `fun (s : S2) => s.«toS1».a`.
  - `pick.eq_1` (reserved names, amendment 5).
  - leanr lacks `ensureAtomicBinderName` (`Binders.lean:188-191`):
    `fun (x.a : Nat) => …` is accepted by leanr and rejected by the oracle,
    a pre-existing binder-slice gap.
  - Unpinned code (every test survives the mutation): U
    (`whnf_core_unfolding_annotations` reduced to plain `whnf_core`, amendment
    6) and R′ (only the `:1988` `tryPostponeIfNoneOrMVar` call deleted; the
    `:1989-1990` arm still answers), both predicted by the plan. Probe S′ also
    survives: the `:1989-1990` arm (no expected type with postponement
    disabled) is reached by no test, because every test postpones and then
    resumes against an mvar type.
  - The `_private.` dot-ident seam in `dot_ident.rs`
    (`isInaccessiblePrivateName`, `App.lean:2024`) has no test (no private
    fixture). Being `UnsupportedSyntax`, it skips `go`'s unfold retry, whereas
    the oracle's error would retry. Owner: the slice that models private
    names.
  - No term was dropped under § Decisions. The only mutations that failed to
    discriminate are U, R′ and probe S′ above.
