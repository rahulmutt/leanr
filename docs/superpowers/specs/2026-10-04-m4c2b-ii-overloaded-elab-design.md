# M4c-2b-ii — overloaded elaboration — design

Status: approved in brainstorming 2026-10-04 (architectural path).
Second half of M4c-2b, after M4c-2b-i shipped (#73, 555ca7e).

Pinned oracle: `leanprover/lean4:v4.33.0-rc1`. Citations below were opened
against that toolchain's `src/lean/Lean` while writing this spec; they are
still subject to the "verify at plan time" rule (cites drift by 1-2 lines).

## Goal

M4c-2b-i made `resolveGlobalName` return every candidate, but every caller
that receives two or more stops with a `— M4c-2b-ii` seam. This slice ports
the oracle's overloaded elaboration: each candidate is elaborated under
`observing`, the successes are filtered (`getSuccesses`), and the result is
the one survivor, `Ambiguous term`, or `mergeFailures`' `overloaded, errors`.
It also turns the plain-throw ambiguity errors whose text leanr can render
exactly into real errors.

**Success:**
- Every new file-corpus record elaborates as the oracle does: per command,
  the same constants, or for a last command that errors, the same first
  error line.
- A candidate that stops at a seam (or any non-oracle error) is never
  treated as a failure: the application stops with that seam rather than
  picking a sibling's success or reporting ambiguity.
- No `— M4c-2b-ii` text remains; every remaining out-of-scope path is a
  named seam with a new label.
- Every existing corpus stays green.

## User decisions

1. **`choice` nodes out of scope.** leanr's parser resolves `longestMatch`
   ties first-wins (`leanr_syntax/src/parse.rs`, M3a divergence), so a
   `choice` head is unreachable from source. `head.rs`'s `choice` arm keeps
   its seam, relabelled `— choice-node parsing`; that later slice (parser
   `choice` production plus overloaded notation) reuses this slice's
   accumulator.
2. **Plain throws: port where the rendering is exact.** The ambiguity
   errors that render a `List Name` become real errors. `resolveId?`
   renders a `List Expr` through the delaborator, so it keeps a seam,
   relabelled `— delab name rendering`.
3. **Approach A:** a direct port of `observing` / `TermElabResult` /
   `applyResult`, with `elab_app_fn` threading the oracle's accumulator.
   Rejected: re-elaborating the winner (B: `getSuccesses` needs each
   success's state, and a re-run mints different mvars); a local fan-out
   inside `elab_app_fn_id` only (C: diverges from the oracle's `acc`
   shape that the `choice` slice needs).

## Oracle behaviour

- **`observing`** (`Elab/Term/TermElabM.lean:574-590`): save; run; on
  success or `.error`, capture the after-state, restore the before-state,
  return `.ok e sNew` / `.error ex sNew`. A postpone exception restores
  the before-state and is rethrown; other internal exceptions are
  rethrown.
- **`elabAppFnResolutions`** (`Elab/App.lean:1925-1950`):
  `overloaded := overloaded || fns.length > 1`; `errToSorry := false` when
  more than one; each resolution under `observing`: `elabAppLVals`, then
  `ensureHasType expectedType? e` when `overloaded`.
- **`resolveName'`** builds every candidate's constant (`mkConsts`, fresh
  level mvars) **before** the fold, so those mvars live outside
  `observing`.
- **`.x`** (`App.lean:2028-2037`): every root-resolved candidate with no
  fields becomes a resolution; it goes through the same fold (not a plain
  ambiguity throw).
- **`elabAppFn`'s generic arm** (`App.lean:2120-2138`):
  `catchPostpone := !overloaded`; `ensureHasType` when `overloaded`.
  Reachable with `overloaded` only through `choice` (out of scope), but
  the flag is threaded.
- **`getSuccesses`** (`App.lean:2140-2185`):
  1. `r₁` = the `.ok` results; at most one → return `r₁`.
  2. `r₂` = the `.ok` results, except a result `e` that is an mvar and,
     after `s.restore; synthesizeSyntheticMVars; instantiateMVars`, is
     still an mvar whose synthetic decl is a `coe` (a delayed coercion).
     A throw inside drops the candidate. `r₂` empty → `r₁`; one → `r₂`.
  3. `r₂` = the `.ok` results whose `s.restore; synthesizeSyntheticMVars
     (postpone := .no)` does not throw. Empty → `r₁`; else `r₂`.
- **`elabAppAux`** (`App.lean:2202-2217`): one candidate → `applyResult`.
  Otherwise one success → `applyResult`; several →
  `throwErrorAt f "Ambiguous term{indentD f}\nPossible interpretations:…"`;
  none → `mergeFailures`.
- **`mergeFailures`** (`App.lean:2190-2200`):
  `throwErrorWithNestedErrors "overloaded" exs` (`Elab/Util.lean:262-263`):
  `"{msg}, errors {toMessageList …}"`, with `toMessageList` an `indentD`
  (`Message.lean:859-860`).

## Design

### State (`synthetic/state.rs`)

- `TermElabResult { Ok(ExprId, SavedTermState), Err(ElabError,
  SavedTermState) }`.
- `observing(f)` and `apply_result(r)` per the oracle above. `Postpone`
  restores the before-state and is rethrown; every other `ElabError` is
  captured.
- `SavedTermState` is a value snapshot (`MetaSnapshot` copies the
  assignment maps), so restoring a later candidate's after-state is
  correct.
- The mvar id generators (`expr_mvar_gen`, `level_mvar_gen`) are **not**
  rolled back: the mvar declaration table only grows, so rewinding would
  let a later candidate reuse a failed candidate's ids.
- `binder_name_gen` (macro-scope-like `a✝` names): **plan-time probe**. If
  the oracle's restore rewinds the counter a failed candidate advanced,
  `SavedTermState` gains it; otherwise it stays monotonic.

### Fan-out (`app/head.rs`, `app/dot_ident.rs`, `app/mod.rs`)

- `head::elab_app_fn` takes and returns `Vec<TermElabResult>` (the
  oracle's `acc`) and gains `overloaded: bool`.
- `elab_app_fn_id`: a local hit stays a single resolution. Otherwise
  every global candidate's constant is built first (`mkConsts`), then
  each runs under `observing`: field LVals plus the caller's LVals through
  `elab_app_lvals`, then `ensure_has_type(expected, e)` when overloaded.
  `resolve::expect_one` shrinks to the zero-candidate `Unknown identifier`
  case (renamed accordingly).
- `.x`: every candidate becomes a resolution through the same fold.
- The generic arm honours `overloaded` (`catchPostpone`, `ensureHasType`).
- `elab_app_aux` runs the result through `app/overload.rs`.

### Selection (`app/overload.rs`)

`expect_single` is deleted. `overload.rs` holds `get_successes` (all three
stages), `merge_failures`, and the selection in `elab_app_aux`.

**Rule 1 — seams are never failures.** Before selection, if any candidate
is `Err(e)` with `!e.is_oracle_error()`, the first such error (candidate
order) is rethrown: leanr cannot know whether the oracle accepts that
candidate. The same applies inside stages 2 and 3: a non-oracle error
raised by `synthesize_synthetic_mvars` propagates instead of dropping the
candidate.

**Rule 2 — postponement.** `Postpone` escaping `observing` propagates out of
the whole application; the enclosing `elab_term` catch handles it.

### Errors (`error.rs`)

| Variant | Raised by | `oracle_first_line` |
|---|---|---|
| `AmbiguousTerm` | ≥2 successes | `Ambiguous term` |
| `Overloaded(Vec<ElabError>)` | no successes | `overloaded, errors` (trailing space: probe) |
| `AmbiguousFieldName { field, full, cands }` | `findMethod?` (`App.lean:1468`) | ``Field name `g` is ambiguous: `S.g` has possible interpretations [..]`` |
| `AmbiguousNamespace { .. }` | `open`'s `resolveUniqueNamespace` | probed text |
| `AmbiguousOpenIdent { .. }` | `open`'s `OpenDecl.resolveId` / `resolveNameUsingNamespaces` | probed text |

All three name lists use the oracle's `List Name` format (`[A.f, B.f]`);
the exact strings and the candidate order are probed at plan time. If a
probe shows a line needs the delaborator after all, that site keeps a
seam (labelled `— delab name rendering`), not a guessed string.

`AmbiguousTerm` and `Overloaded` are oracle errors (`is_oracle_error`).
`Overloaded` keeps the nested errors for tests.

### Seam relabelling

- `builtin/op/mod.rs`'s `resolve_id` (oracle `resolveId?`,
  `TermElabM.lean:2211-2224`): `— delab name rendering`.
- `head.rs`'s `choice` arm, `app/mod.rs`'s and `dispatch.rs`'s `choice`
  rows: `— choice-node parsing`.
- `lib.rs` / module docs listing M4c-2b-ii: updated.
- `seam_audit` and `scopes.rs` expectations updated.

## Testing

**File corpus** (`dump_decls.lean files`, every row oracle-probed at plan
time):

| Row | Source | Expected (oracle) |
|---|---|---|
| `overload/argType` | `A.f : Nat → Nat`, `B.f : Bool → Bool`, `open A B`, `def t := f 0` | `A.f` |
| `overload/expectedType` | `A.c : Nat`, `B.c : Bool`, `def t : Bool := c` | `B.c` |
| `overload/ambiguous` | both candidates typecheck | `Ambiguous term` |
| `overload/allFail` | neither typechecks | `overloaded, errors` |
| `overload/nestedNs` | `A.f`, `A.B.f`, used inside `namespace A.B` | per probe |
| `overload/fields` | `f.succ` over overloaded `f` | per probe |
| `overload/lvals` | `(f 0).succ` | per probe |
| `overload/dotIdent` | `.x` with a root and an opened candidate | per probe |
| `ambig/fieldName` | two opened `S.g` | exact first line |
| `ambig/openNamespace` | `open X` with two `X` namespaces | exact first line |
| `ambig/openIdent` | `open A (f)` with two resolutions | exact first line |

**Stages 2 and 3** of `getSuccesses`: corpus rows if the plan-time probe
finds a source that separates them; otherwise white-box unit pins.

**Seam propagation:** a test where one candidate reaches an unported
feature and the other succeeds; it must stop with that seam.

**Unit pins** (`synthetic/state.rs`): `observing` restores the before-state
on `Ok` and `Err`; `apply_result` restores the after-state; `Postpone`
restores and rethrows.

**Mutation evidence** (required in review, per the non-discriminating-test
history): each of these must fail at least one new test —
- drop the overloaded `ensureHasType`;
- skip stage 2; skip stage 3;
- treat a seam as a failure;
- skip restoring the before-state in `observing`.

**Gates:** `oracle_file` with `CORPUS_FLOOR` bumped; every committed corpus
unchanged; `seam_audit`; the full `mise run ci` (fmt and clippy included).

## Out of scope (named seams or unchanged)

- **`choice` nodes** (parser `longestMatch` ties, overloaded notation):
  `— choice-node parsing`.
- **`resolveId?`'s ambiguity** (`binop%` leaves): `— delab name rendering`.
- **`errToSorry`**: unchanged; leanr stops at the first error, which is
  what `errToSorry := false` gives inside the fan-out.
- **Info trees** (`mergeFailures`' `ofChoiceInfo`, `addTermInfo`): not
  modelled.
- **`checkDeprecated`**: not modelled (no deprecation attributes in the
  corpus).
- **Later M4** items listed in the M4c-2b-i spec are unchanged.

## Plan amendments (plan-time oracle probes, 2026-10-04)

- `elab_app_fn` returns `AppFn::{Done, Candidates}` instead of threading
  an accumulator, and takes no `overloaded` flag: the oracle sets the
  incoming flag only under `choice` (out of scope), so `overloaded` is
  `fns.len() > 1` inside `elab_app_fn_resolutions`.
- Rule 1 lives in `observing`: non-oracle errors are rethrown, never
  captured, so `select` only ever sees oracle errors.
- `open`'s two "ambiguous identifier" throws render `Expr` lists: they are
  `— delab name rendering` seams, and `AmbiguousOpenIdent` is dropped.
  `failed to open, errors ` is ported (`FailedToOpen`).
- Nested namespaces never overload (the inner shadows), so the
  `overload/nestedNs` rows are dropped.
- `binder_name_gen` stays monotonic: `Core.SavedState.restore` rewinds
  neither the name generator nor the macro scope.
- `Elab0` gains `instCoeListNatInt : Coe (List Nat) Int`, to give
  `getSuccesses` stage 2 a source-level discriminator. It is inert:
  only `elim.jsonl` gains its record.
- `mk_const` renders the resolved constant in
  ``too many explicit universe levels for `B.u` `` (it rendered the source
  text before, and the variant had no first line).
- Identifier candidates run in `mkConsts`' REVERSED `resolveGlobalName`
  order (`TermElabM.lean:2146-2158` cons-folds); `.x` candidates keep
  `resolveGlobalName` order (`App.lean:2032-2033`, `mapM`).

## Landed

- PR: pending (the controller fills it at merge). Head before the
  closing commit: 5315017; the closing commit is this one.
- Corpus: 131 file-query records (`CORPUS_FLOOR` 131). `leanr_meta/src`
  and the kernel are untouched; only `file-queries.jsonl` rows and one
  `elim.jsonl` record (`instCoeListNatInt`) were added.
- Shipped: `observing`/`apply_result`, `overload::select`
  (`getSuccesses` stages 1-3, `Ambiguous term`, `mergeFailures`),
  overloaded identifiers and `.x` through `elab_app_fn_resolutions`,
  `AmbiguousFieldName`, `AmbiguousNamespace`, `FailedToOpen`, and the
  `seam_audit` gate for the retired label.
- Mutation results (each applied, confirmed failing, reverted):
  - `observing`'s Ok arm without restore, capture-every-error, and
    `apply_result` without restore: all caught by Task 1's unit tests.
  - No `ensureHasType` in the candidate loop: caught by
    `overload/expectedType`, `delayedCoeStuck`, `delayedCoeStage2`,
    `argExpected`, `twoOverloads`; NOT by `overload/coe`.
  - Skip stage 2: `overload/delayedCoeStage2`. Skip stage 3: only the
    scopes test `stage_three_drops_a_stuck_instance_candidate`.
  - `mk_const` lazily inside `observing`, and `TooManyUniverseLevels` from
    source text: `overload/explicitUniv`.
  - Candidate-order mutations: dropping the identifier reversal fails
    `overloaded_candidates_run_in_mk_consts_order`; `.take(1)` on `.x`
    fails `dotIdentArgs`, `dotIdentAmbig`, `dotIdentAllFail`, and `.rev()`
    fails `dot_ident_candidates_keep_resolve_order`.
  - `AmbiguousNamespace` candidates reversed: `ambig/openHiding` and
    `openRenaming`; `AmbiguousFieldName` reversed: `ambig/fieldName`;
    `errs.remove(0)` instead of `FailedToOpen`: `ambig/openFailed`.
- Surprises:
  - (a) Candidate fold order differs between the two paths (see Plan
    amendments); each is pinned by a scopes test.
  - (b) The plan's `overload/stage3` row fails at stage 1 (`NoInst`
    fails inside the candidate, in the oracle too), so stage 3 is pinned
    by `stage_three_drops_a_stuck_instance_candidate` (oracle-probed
    `t := B.h`).
  - (c) Mutation 1 (drop `ensureHasType`) is not caught by
    `overload/coe`, since the outer `ensureHasType` inserts the coercion
    when only one candidate succeeds; other rows catch it.
  - (d) `open`'s all-failed catch admits any `UnsupportedSyntax` (it
    stands for a delab-seam throw the oracle's catch would take); this is
    wider than needed and is an open item.
- Open seams: `choice` nodes (choice-node parsing: leanr's parser never
  builds them); delab name rendering (`resolveId?`'s lowercase `ambiguous term, use
  fully qualified name, …` (`TermElabM.lean:2223`), reached only from
  `binop%`-family ident heads (`builtin/op/mod.rs` `resolve_id`), and `open`'s two
  `Expr`-list ambiguity throws, `ResolveName.lean:376` and
  `Open.lean:72`).
