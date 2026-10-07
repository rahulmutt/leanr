# M4c-2c-ii — auto-bound implicits — design

Status: approved in brainstorming 2026-10-05 (architectural path).
Second half of M4c-2c, after 2c-i (#75, ad9e955) and its follow-ups
(#76, 5c47cdd).

Pinned oracle: `leanprover/lean4:v4.33.0-rc1`. Citations were opened
against that toolchain's `src/lean/Lean` while brainstorming; they are
still subject to the "verify at plan time" rule (cites drift by 1-2 lines).

## Goal

Every unbound identifier or universe name in a declaration header or a
`variable` binder currently hits a `— M4c-2c-ii` seam. This slice ports
the oracle's auto-bound implicit machinery, plus the two options that
govern it (`autoImplicit`, `relaxedAutoImplicit`), so those headers
elaborate as the oracle does — including Mathlib's `autoImplicit false`
error messages.

**Success:**
- Every new corpus row matches the oracle: per command, the same
  constants (full ConstantInfo, binder names included), or for a last
  command that errors, the same first error line.
- No `— M4c-2c-ii` label remains after P2.
- Every existing corpus stays green; `mise run ci` passes.

## User decisions

1. **Options:** port `set_option autoImplicit` and
   `set_option relaxedAutoImplicit` (command and `set_option … in`) via a
   minimal scoped options record. Any other option name is a
   `— later M4` seam. Rejected: defaults only (leaves Mathlib's
   disabled-mode errors unported); a general options registry (no other
   consumer yet).
2. **Cut:** one spec, two PRs.
   - **P1:** the retry loop + `addAutoBoundImplicits` in def/theorem/
     axiom headers; universe-name auto-bound; mvar binders (additive
     `leanr_meta` `mk_binding` arm, `collectUnassignedMVars`,
     `mkForallFVars'`); `set_option`.
   - **P2:** `variable` binder auto-bound and `runTermElabM`'s
     mvar-rebuild branch.
3. **Approach A:** faithful exception-and-retry. Rejected: B, a syntax
   pre-scan for unresolved identifiers (resolution depends on
   elaboration — notation/macro expansion, macro scopes, dotted names,
   overloads — and binder order is elaboration-time discovery order);
   C, binding in place without restart (the new fvar must precede
   already-elaborated binders, so earlier mvars' lctxs could never see
   it).

## Oracle behaviour

- **`withAutoBoundImplicit k`** (`Elab/Term/TermElabM.lean:1959-1980`):
  if `autoImplicit` is on, loop: save state; run `k` with
  `autoBoundImplicitContext := some ctx`; on the internal
  `autoBoundImplicit` exception (`Exception.lean:20,31-41`) carrying `n`,
  `s.restore (restoreInfo := true)`, `withLocalDecl n .implicit
  (← mkFreshTypeMVar)`, push the fvar onto `ctx`, loop. Other exceptions
  propagate. If off: run `k` with `some {autoImplicitEnabled := false}`
  (still "in an auto-bound context" — this is what makes the disabled
  note fire). `withoutAutoBoundImplicit` sets `none` (`:1982-1983`).
- **`withAutoBoundImplicitForbiddenPred`** (`:1985-1986`): ORs a
  predicate into `autoBoundImplicitForbidden`. `elabHeaders` forbids the
  views' short names (`MutualDef.lean:213`); `elabAxiom` forbids its own
  (`Declaration.lean:110`).
- **Throw site** — `throwUnknownIdWithSuggestions` (`App.lean:1960-1974`):
  if not forbidden and the context is `some`:
  `checkValidAutoBoundImplicitName n allowed relaxed` (`AutoBound.lean`):
  - `.ok true` ⇒ `throwAutoBoundImplicitLocal n`;
  - `.ok false` ⇒ plain "Unknown identifier";
  - `.error note` ⇒ "Unknown identifier" plus the note: either
    ``It is not possible to treat `x` as an implicitly bound variable
    here because the `autoImplicit` option is set to `false`.`` or
    ``… because it has multiple characters while the
    `relaxedAutoImplicit` option is set to `false`.``
  Eligible names are atomic (`.str .anonymous s`, non-empty, no macro
  scopes). Strict mode (`relaxed = false`) accepts a single character
  followed by digits, subscripts, `_` or `'` (`isValidAutoBoundSuffix`).
- **Universe levels** — `elabLevel` ident arm (`Level.lean:78-85`): an
  unknown name is consed onto `levelNames` (no exception, no retry) iff
  `autoBoundImplicit` (= the context's `autoImplicitEnabled`,
  `TermElabM.lean:818`) and `isValidAutoBoundLevelName` (strict mode:
  first char lowercase + valid suffix); else ``unknown universe level
  `u` ``. `levelNames` is `Term.State`, so the retry loop's restore
  rewinds it.
- **`addAutoBoundImplicits xs`** (`TermElabM.lean:2071-2089`): for each
  auto, in order, first `collectUnassignedMVars (← inferType auto)`
  (`:1993-2016`, dependency-first, deduplicated) then the auto itself;
  then for each fvar auto and each `x ∈ xs`, if the auto's decl depends
  on `x`: ``invalid auto implicit argument `a`, it depends on explicitly
  provided argument `x` ``. Returns `autos ++ xs` (may contain mvars).
- **`mkForallFVars'`** (`Meta/ForEachExpr.lean:127-140`): if any `x`
  `shouldInferBinderName`, set user names on mvars in the binder types
  from the parameter names they fill (`setMVarUserNamesAt`), abstract,
  then reset those names. With mvars in `xs`, this decides the stored
  binder names (`theorem t : a = a` ⇒ `∀ {α : Sort u_1} {a : α}, a = a`).
- **`MkBinding.mkBinding`** mvar arm (`MetavarContext.lean:1339-1347`):
  binder type `mvarDecl.type.headBeta`, abstracted over `xs[..i]`; name
  `userName`, or `mkFreshBinderName` if anonymous; binder info
  `binderInfoForMVars` (default `.implicit`). `mvarIdsToAbstract`
  (`:1364`) makes the mvars in `xs` abstractable.
- **Call sites:**
  - `elabHeaders` (`MutualDef.lean:257-277`): `withDeclName` →
    `withAutoBoundImplicit` → `withLevelNames` → binders, type,
    `synthesizeSyntheticMVarsNoPostponing` → `addAutoBoundImplicits` →
    `mkForallFVars'` → `levelNames ← getLevelNames`; `numParams :=
    xs.size` (autos included).
  - `elabAxiom` (`Declaration.lean:109-116`): same shape, then
    `mkForallFVars vars type (usedOnly := true)`.
  - `elabVariable` (`BuiltinCommand.lean:419-425`): sanity run under
    `withSynthesize ∘ withAutoBoundImplicit`, `addAutoBoundImplicits`
    result discarded. `varDecls` stores binder syntax only.
  - `runTermElabM` (`Command.lean:774-798`): `withAutoBoundImplicit
    (elabBinders scope.varDecls …)` → `synthesizeSyntheticMVarsNoPostponing`
    → `sectionFVars` → `resetMessageLog` → `addAutoBoundImplicits xs none`
    → all fvars ⇒ `withoutAutoBoundImplicit (elabFn xs)`; else
    `mkForallFVars' xs (Sort 0)` and, under `withLCtx {} {}`,
    `forallBoundedTelescope … xs.size` ⇒ `withoutAutoBoundImplicit
    (elabFn xs')`. `sectionFVars` is built BEFORE the rebuild (it maps to
    the stale fvars on that branch).
  - `runTactic` runs `withoutAutoBoundImplicit` (`SyntheticMVars.lean:474`).
- **`set_option`** (`BuiltinCommand.lean:516`, `SetOption.lean:58`):
  updates the scope's options; `set_option … in` scopes it to one
  command.

## Design

### Core mechanism (`leanr_elab`, P1)

**`TermElabM` state** (reader-like; saved/restored around scopes):
- `auto_bound: Option<AutoBoundCtx>`,
  `AutoBoundCtx { enabled: bool, bound: Vec<ExprId> }`.
- `auto_bound_forbidden: Vec<NameId>`.
- `options: ElabOptions { auto_implicit: bool, relaxed_auto_implicit:
  bool }`, both default `true`, seeded from the command scope.

**Error variant:** `ElabError::AutoBoundImplicitLocal(NameId)`. Internal;
never rendered. `UnknownIdent` gains an optional note
(`UnknownIdent(String, Option<AutoBoundNote>)`) that renders the
disabled/strict note; whether the note reaches the first error line the
gate compares is probed at plan time.

**Throw sites:** the unknown-global paths at `app/head.rs:408` and
`app/mod.rs:193` run the oracle guard in order (forbidden ⇒ plain;
context `some` ⇒ `check_valid_auto_bound_implicit_name`). Dotted and
macro-scoped names are ineligible. `app/lval.rs` unknown-field paths are
not throw sites (the oracle's are not either; confirm at plan time).

**Universe levels:** `builtin/sort.rs:214` follows `Level.lean:78-85`
(push onto `level_names`, no retry).

**`with_auto_bound_implicit(k)`:** if enabled, loop: save
`save_term_state()` + `level_names` + `mctx.lctx_checkpoint()`; run `k`
with `auto_bound = Some(ctx)`; on `AutoBoundImplicitLocal(n)` restore all
three, declare `n` (`.implicit`, `mk_fresh_type_mvar`), push onto `ctx`,
loop. Other errors propagate. If disabled: run `k` with
`Some(ctx { enabled: false })`. Outer `auto_bound` is restored on exit.
`without_auto_bound_implicit(k)` is the `None` twin.
`with_auto_bound_forbidden(names, k)` extends the forbidden list.

`save_term_state`'s doc (`synthetic/state.rs`) says `level_names` is not
snapshotted because no path below `f` touches it; that stays true for
`commit_when`, but the retry loop does touch it, so the loop snapshots it
itself. The doc is amended to say so.

**`add_auto_bound_implicits(xs)`:** port of `addAutoBoundImplicits` +
`collectUnassignedMVars`; returns `autos ++ xs`.

**Catch-site audit.** The internal exception must pass through every
catch that the oracle's counterpart does not intercept (`observing`,
`exceptionToSorry`, `commitWhen`, coercion and unifier fallbacks,
postpone/resume, `elab_using_elab_fns`). The plan tabulates each of the
~24 `Err(e) =>` / `or_else` / `commit_when` sites in `leanr_elab`
against its oracle catch (`.error` only vs everything) and fixes
divergences; a probe row pins each observable class.

### Headers (P1)

- `elab_header` (`command/header.rs`): `with_auto_bound_forbidden(short
  names)` → `with_auto_bound_implicit` → `with_level_names` → binders,
  type, `synthesize_synthetic_mvars_no_postponing` →
  `add_auto_bound_implicits` → `mk_forall_fvars'`. `num_params` counts
  autos. The returned `level_names` include auto-bound universes and
  feed `sortDeclLevelParams` (ordering probed at plan time). The body
  telescope re-pushes the autos so header and body share it.
- `elab_axiom` (`command/axiom.rs`): same wrapping.
- `unknown_ident_to_auto_bound_seam` is deleted (header and axiom).
- **`mk_forall_fvars'`** is ported for real (`shouldInferBinderName`,
  `setMVarUserNamesAt`, name reset); the `header.rs` comment calling it
  message-only is wrong once mvars are binders.

### `leanr_meta` additive arm (P1)

Under the M4b TCB-neutral accessor precedent:
`MetaCtx::mk_binding` gains the mvar arm (`MetavarContext.lean:
1339-1347`) instead of erroring "telescope entry is not an fvar";
`abstract_range` / `elim_mvar_deps` treat mvars in `xs` as abstractable
(`mvarIdsToAbstract`). Fvar-only callers are unchanged. Unit tests in
`leanr_meta` pin type/name/binder-info and the anonymous-name fallback.

### `set_option` (P1)

- `Scope.options: ElabOptions`, inherited by nested scopes, restored at
  `end`.
- Dispatch arm `Lean.Parser.Command.set_option`; `set_option … in` via
  the existing `elab_in`.
- Only `autoImplicit` / `relaxedAutoImplicit` with `true`/`false`. A bad
  value gets the oracle's error (probed). Any other name:
  ``set_option `<name>` — later M4``.
- Term-level `set_option … in` stays out of scope.

### `variable` binders (P2)

- **`elab_variable`:** the sanity run becomes `with_synthesize(
  with_auto_bound_implicit(elab_binders → add_auto_bound_implicits))`,
  result discarded. `variable_auto_bound_seam` is deleted.
- **`elab_section_vars` (`runTermElabM`):** under
  `with_auto_bound_implicit`; then `synthesize_synthetic_mvars_no_postponing`;
  `add_auto_bound_implicits(xs)`.
  - All fvars ⇒ `without_auto_bound_implicit(elab_fn(xs))`. The autos are
    ordinary leading section vars; `header_sec_vars` / `used_vars` keep
    them iff something kept depends on them. Replaces 2c-i's `Internal`
    guard.
  - Mvars present (rebuild branch) ⇒ `mk_forall_fvars'(xs, Sort 0)`,
    then under an empty lctx and empty local instances,
    `forall_bounded_telescope(ty, xs.len())` ⇒ `elab_fn(xs')`. Whether
    `leanr_meta` already has both pieces is a plan-time check; if not,
    another additive accessor.
  - The stale-`sectionFVars` quirk is recorded as an unobservable
    divergence (leanr does not resolve hygienic section-var references
    through `section_fvars`).
- Header autos land after section autos and before header binders, as
  in the oracle.

## Testing

Rows go into `tests/oracle_decl.rs` (single declarations) and
`tests/oracle_file.rs` (`set_option`, `variable`, multi-command). Every
row is oracle-probed at plan time.

| family | covers |
|---|---|
| `auto/ident*` | `def f (x : α)`, multiple autos and discovery order, auto used only in the return type, auto in axiom and theorem |
| `auto/mvarBinder*` | `theorem t : a = a`: mvar binders, `setMVarUserNamesAt` names, anonymous-name fallback |
| `auto/level*` | `Sort u` auto, with explicit `.{v}`, order in `sortDeclLevelParams`, with scope `universe` |
| `auto/neg*` | dotted name, the decl's own short name (forbidden), depends-on-explicit error, unknown ident in the body (no auto) |
| `auto/catch*` | one row per oracle catch class from the audit (overloaded argument, coercion site, postponed elaborator) |
| `opt/*` | `autoImplicit false` + note; `relaxedAutoImplicit false` strict suffix (`α₁`, `X12` pass; `foo` noted); `set_option … in`; scoping across `section`/`end`; non-whitelisted option seam |
| `varAuto/*` (P2) | all-fvar branch; rebuild branch; inclusion via dependency; header autos after section autos; `include` of an auto ⇒ undeclared |

**Mutation discipline:** each plan task names the mutations its rows
must kill and records them in the commit body. Minimum set: drop the
`level_names` restore; swallow the auto-bound error at one catch site;
`.default` instead of `.implicit` for mvar binders; skip
`collectUnassignedMVars`; reverse the autos order; drop the forbidden
predicate.

## Plan-time probes (front-loaded risks)

1. The binder-name hygiene `setMVarUserNamesAt` produces (`α` vs `α✝`)
   and the anonymous fallback name.
2. The catch-site audit table: which leanr sites diverge.
3. `u_N` / auto-bound universe ordering in `sortDeclLevelParams`, on
   both the def and async-theorem paths.
4. Whether `forall_bounded_telescope` and an empty-lctx scope exist in
   `leanr_meta`.
5. The rendering of the note line and of a bad `set_option` value.

## Seams after this slice

- P1 leaves `variable` binder auto-bound as `— M4c-2c-ii P2`; P2 removes
  it. (done in P2)
- Any option other than the two: `— later M4`.
- Term-level `set_option … in`: unchanged (out of scope).
- Unobservable: stale `sectionFVars` on the rebuild branch; inlay hints. (withdrawn: observable — see Amendment 2)

## Amendment 1 (plan time, 2026-10-05)

Oracle probes of the 89 P1 rows (scratch `target/m4c2ciiprobe/`) changed
four points of the design above:

1. **`setMVarUserNamesAt` is not ported.** It names an mvar binder with
   `mkFreshUserName` — the parameter name plus a fresh MACRO SCOPE (`α✝`)
   — so the name is inaccessible: `theorem am3 : Eq a a := rfl` then
   `am3 (α := Nat)` fails with ``Invalid argument name `α` for function
   `am3` ``. The dumper erases binder names, and a macro-scoped name never
   matches a named argument, so the only observable property is "the mvar
   binder's name is not accessible". leanr's mvar arm names the binder
   with the mvar's `user_name` if it has one, else a fresh
   `_leanr_mkbinding_fresh.N` (leanr's macro-scope stand-in, recognised by
   `name_has_macro_scopes`). The `header.rs` comment calling
   `mkForallFVars'` message-only stays true for leanr.
2. **`throwInvalidNamedArg` is ported (first line only)** so the row
   above can pin (1): `App.lean:400-403` → ``Invalid argument name `n`
   for function `f` `` (`` for function`` alone when the head is not a
   constant). The deprecated-argument linter branch is not ported (no
   `Elab0` constant carries `deprecated_arg`).
3. **The note line is not modelled.** The disabled/strict notes render
   on the THIRD line (`Unknown identifier `α`\n\nNote: …`), and every
   gate compares the first line only. `checkValidAutoBoundImplicitName`'s
   `.error` arm therefore returns plain `UnknownIdent`; there is no
   `AutoBoundNote`.
4. **The catch-site audit collapses to one predicate.** Every generic
   catch in `leanr_elab` (`observing`, `commit_when`, the ladder's
   `postpone_on_error`, `elab_using_elab_fns`, overload/lval/dot-ident
   rethrows) either rethrows or gates on `ElabError::is_oracle_error()`.
   Adding `AutoBoundImplicitLocal` to that predicate's exclusion list
   (beside `Postpone`) is the whole audit; `auto/catchOverload` (the
   exception escapes `observing`, the retry binds `x`, and BOTH
   candidates then succeed ⇒ "Ambiguous term") pins it.

Further probed facts the plan relies on:

- The "depends on explicitly provided argument" error is unreachable
  from source: an auto's type mvar is declared outside the explicit
  binders, so `(x : β)` fails first with "Application type mismatch"
  (`auto/negDependsExplicit`). Ported, pinned by a unit test only.
- Level order: def/theorem use the post-header `levelNames`, so explicit
  `.{v}` and scope names come first, then auto universes in discovery
  order, then `u_N` (`al3` ⇒ `[v, u]`, `al9` ⇒ `[u, u_1]`). `elabAxiom`
  sorts against `expandDeclId`'s names, so axiom auto universes are
  lexicographic leftovers (`al16` ⇒ `[u, v]`; `al19.{w}` ⇒ `[w, v]`).
- Retry rewinds `levelNames`: `def al13 (α : Sort u) (x : β) …` ⇒
  `[u, u_1]` (a non-rewinding loop would push `u` twice).
- Section variables precede header autos (`ai20` ⇒ `{β} (b) {α} (x)`).
- `set_option autoImplicit 1` ⇒ ``set_option value type mismatch: The
  value`` (first line).
- `abstract_fvars` is kernel code (`leanr_kernel/src/subst.rs`, TCB).
  The mvar-aware abstraction is a new `leanr_meta`-local traversal used
  only when `xs` contains an mvar; fvar-only telescopes keep the kernel
  path byte-for-byte.

## Amendment 2 (P2 plan time, 2026-10-06)

Oracle probes of the 65 P2 rows (scratch `target/m4c2ciip2probe/`,
`expected.txt`) overturn one claim of § "`variable` binders (P2)" and add
one error:

1. **The stale `sectionFVars` is observable.** `runTermElabM` builds
   `sectionFVars` (uid ↦ fvar, `Command.lean:782-784`) from the binders'
   fvars BEFORE `addAutoBoundImplicits` and the rebuild, so on the rebuild
   branch no member of `elabFn`'s `xs` has a uid. Every uid-keyed lookup
   then misses:
   - `include n` has no effect on a theorem (`varAuto/rebuildInclude`
     ⇒ `va42 : True`; the all-fvar twin keeps `(n : Nat)`);
   - an `omit`ted instance is kept again (`varAuto/rebuildOmitInstIgnored`
     ⇒ `∀ [Wrap Nat], True`);
   - `omit n` fails (item 2).
   leanr ports the map faithfully: `SecVars` carries `section_fvars:
   Vec<(u32, ExprId)>` built from the pre-rebuild fvars, and every
   include/omit/instance lookup goes through it. The § P2 sentence
   calling the quirk unobservable is withdrawn.
2. **`elabOmit`'s "not declared" arm** (`BuiltinCommand.lean:598-599`):
   `omit` matches against every run variable, autos included; a match
   with no uid is ``invalid 'omit', `a` has not been declared in the
   current scope`` (new `ElabError::OmitUndeclared`, carrying the
   binder's user name). Reached by an auto (`varAuto/omitAuto`) and by
   every variable on the rebuild branch (`varAuto/rebuildOmitName`).
   Unpinnable sub-case: a `[T]` item matching an mvar binder or an
   anonymous instance binder; the oracle prints a hash-bearing hygienic
   name (`inst._@.843228007._hygCtx._hyg.8`), and leanr prints its own
   binder name. leanr still errors.
3. **`leanr_meta` additions** (additive, TCB-neutral, M4b precedent):
   `forall_bounded_telescope` becomes `pub` (it was `pub(crate)`), plus a
   new `MetaCtx::install_empty_lctx` (oracle `withLCtx {} {}`).

Confirmed as designed: autos lead the run (`{α} {β} (x) (n) (y)` across
two `variable` commands); header autos follow section variables; a
header `α` after a rebuild is a fresh auto, because the mvar binder is
inaccessible (`varAuto/rebuildHeaderAlphaThm`); section-variable
universes join `levelNames` (`varAuto/levelHeader` ⇒ `[u, v]`); options
are read at each re-elaboration (`varAuto/offAfter` ⇒ "Unknown
identifier").

## Landed

### P1 (headers)

- PR: pending (the controller fills it at merge). Commits: 8352b47
  (`leanr_meta` mvar entries in `mk_binding`), 58e9f57 (corpus rows,
  staged), 1e3f19d (retry loop + throw sites), 57fe644
  (`addAutoBoundImplicits`, def/theorem/axiom wiring), 05b94d4
  (universe names), 18dc6ec (`throwInvalidNamedArg`), 928e9ba
  (`set_option autoImplicit` / `relaxedAutoImplicit`), then the close-out
  and the final-review fix wave (`level_names` in `SavedTermState`).
- Corpus: file-query floor 311 (`CORPUS_FLOOR`; the plan said 309 --
  Task 1 dropped `auto/identInBinderDefault` because leanr's parser
  rejects binder defaults `(y : T := v)`; re-add it when they parse --
  and the final-review fix wave added 3 rows,
  `auto/levelOverloadNamedLeak`, `auto/levelOverloadNamedLeakThm`,
  `auto/levelOverloadMismatchLeak`: a failed overload candidate that
  auto-bound `Sort u`/`Sort v` must not leak those names; leanr was a
  wrong-Ok with levelParams `[v, u]` vs the oracle's `[u, v]` until
  `save_term_state` snapshotted `level_names`, as
  `Term.SavedState.restore`'s `set s.elab`, `TermElabM.lean:424`, does).
  The single-declaration corpus (`oracle_decl`, 79 records) is
  unchanged. The `PENDING` filter is empty.
- `KNOWN_GAPS` (4 rows, exact-id gated, each a pre-existing gap outside
  auto-bound that diverges identically without an auto; each is a
  follow-up):
  - `auto/negDependsExplicit`, `auto/negDependsExplicitAx`: coercion
    (leanr `StuckCoercion`, oracle `Application type mismatch`).
    CLOSED 2026-10-07: the `.coe` synthetic mvar now keeps the oracle's
    `f?`, so the stuck reporter raises `throwAppTypeMismatch`
    (`coeStuck/*` rows).
  - `auto/catchInst`: dotted unknown `Wrap.val` is `Unknown identifier`
    in leanr, `Unknown constant` in the oracle.
  - `auto/withUsedVarThm`: header level order `max(u_1,1)` vs the
    oracle's `max(1,u_1)` -- a possible wrong-Ok level-order bug that
    deserves its own slice.
- Mutations (full text in each commit body, `git log --format=%B`):
  - `leanr_meta` (8352b47): `.default` for the mvar arm; drop the
    `mvarIdsToAbstract` arm in `elim_app` (the brief's test survived, a
    new `?β : y` test kills it); ignore `user_name`; per-binder step back
    to kernel `abstract_fvars`; `abstract_go` never matches an MVar;
    `mk_aux_mvar_type` keeps an anonymous name; macro-scope prefix.
    Equivalent: "abstract_vars always takes the new traversal" and
    "abstract_range back to kernel `abstract_fvars`" (all tests pass;
    the per-binder loop already abstracts earlier entries).
  - Task 3: drop `AutoBoundImplicitLocal` from `is_oracle_error`; skip
    the lctx restore (a new test; the brief's survived); ignore the
    forbidden predicate; `relaxed` for `allowed`; `char::is_lowercase`;
    macro-head through `unknown_ident` (hangs).
  - Task 4: collect-before-push order; skip `collect_unassigned_mvars`;
    drop the forbidden name (def/theorem and axiom); reverse bound
    order; `num_params` before autos; count the exception as an oracle
    error (`auto/catchOverload`); disable the no-progress guard;
    disable the depends-on-explicit check; double the recursion cap.
  - Final-review fix: drop the `level_names` restore in
    `restore_term_state` ⇒ the 3 `auto/levelOverload*Leak` rows and
    `the_retry_rewinds_level_names` fail (the loop's own redundant
    snapshot was removed, so that unit test now pins this restore).
  - Task 5: drop the loop's `level_names` restore (now
    `restore_term_state`'s, see above); `push` for
    `insert(0, ..)`; ignore `relaxed`; axiom passes post-header names;
    `is_some_and(enabled)`; `parts.len() == 1`; auto-bind outside a
    context; drop the `variable` seam arm.
  - Task 6: mvar-arm binder name; report the LAST named arg (two-arg
    case added); drop the `func` suffix.
  - Task 7: no seeded options; options on the root scope; swap the two
    field mappings; force the relaxed flag in `sort.rs`.
- Surviving or equivalent mutations: Task 5 (a') is equivalent
  (`elab_level` skips already-bound names and a failed attempt's
  universes are a prefix of the next's), the restore half is killed by
  `the_retry_rewinds_level_names`; Task 7 (c) does not discriminate on
  `opt/strictBad` (both options off give the same error) but is caught
  by `opt/strictOk`, `opt/strictLevelOk`, `opt/offLevel`; Task 4 (j) is
  bounded, not killed (the cap is doubled, not removed -- removing it
  would loop); the two `leanr_meta` equivalents above.
- Deviations from this spec: `app/mod.rs` macro-quotation heads stay a
  plain `UnknownIdent` (the "Throw sites" list names `app/mod.rs:193`,
  which is NOT a throw site); `AutoBoundImplicitLocal` carries a
  `String`, not a `NameId`; `AutoImplicitDependsOnExplicit` carries
  rendered Strings; the retry loop is bounded by `MAX_REC_DEPTH`
  (oracle `withIncRecDepth`, `TermElabM.lean:1963`) plus a no-progress
  guard (Internal error). The `variable` seam keeps the label
  `— M4c-2c-ii` (not `… P2`; `variable_seams_carry_their_slice` pins
  it) and also covers unknown universes in `variable` binders. (superseded in P2: the label is removed; that test now pins only the `— later M4` annotation-update seam)
- Open seams / follow-ups: (CLOSED in P2: `variable` auto-bound and the
  `runTermElabM` mvar-rebuild branch); `setMVarUserNamesAt`; the "note"
  line (line 3 of the message, unobservable to the gate); the
  deprecated-arg linter and the "perhaps you meant" hint are
  unmodelled;
  `_leanr_`-prefixed names are excluded from auto-bound idents (the
  oracle would bind a user ident literally named `_leanr_*`) but are not
  rejected for level names; `header_unknown_ident_is_auto_bound`
  asserts only `is_ok()`.
- Pre-existing gaps found by the final review (not auto-bound; each a
  follow-up):
  - HIGH: `auto/withUsedVarThm` (`max(u_1,1)` vs `max(1,u_1)`) IS a
    wrong-Ok on main too, not only under auto-bound -- its own slice.
    (CLOSED by the Meta `Level.normalize` port, branch
    `meta-level-normalize`: leanr_meta ran the kernel's `level.cpp`
    normalize where Meta runs the pure-Lean `Level.lean:382` one. The
    sibling gap it exposed -- oracle `mkFreshLevelMVars` hands out level
    mvars in reverse order -- was `KNOWN_GAPS` `lvl/nest3`/`lvl/nest3Mk`,
    CLOSED by branch `level-mvars-reverse-order`: `MetaCtx::mk_fresh_level_mvars`.)
  - `InstanceSynthesisFailed` has no oracle first line (oracle "failed
    to synthesize instance of type class"; probe `rv/autoInstArg`).
  - A postponed `⟨…⟩` whose universe constraint stays unsolved reaches
    the kernel as `Kernel(AppTypeMismatch)`; the oracle reports "stuck
    at solving universe constraint".
  - `rv/scopeOrder`: `StuckCoercion` vs the oracle's "Application type
    mismatch" (same class as the `KNOWN_GAPS` coercion rows; closed with
    them on 2026-10-07).
- Perf note: `oracle_file` takes ~6 min; that is per-row harness setup
  (~0.8-1 s/row), not the auto-bound retry loop.
- Cite sweep: every oracle `file:line` this branch added was opened
  against `v4.33.0-rc1`; the Level.lean ident arm is :78-85, the
  throw-site function `App.lean:1960-1974`, `addAutoBoundImplicits`
  `TermElabM.lean:2071-2089`, `runTermElabM` `Command.lean:774-798`.

### P2 (variable binders)

- Commits: 25456a8 (Task 1, 65 oracle-probed `varAuto` rows, staged),
  dbd69af (Task 2: all-fvar branch, `sectionFVars` uid map,
  `OmitUndeclared`), 0ad03eb (Task 3: `runTermElabM` rebuild branch,
  stale `sectionFVars`), then this close-out.
- Corpus: file-query floor 376 (65 rows). `KNOWN_GAPS` added: none.
- Mutations (measured results; they override the commit bodies):
  - Task 2: (a) `section_fvars` built after `add_auto_bound_implicits`
    fails `varAuto/includeX`, `omitAuto`, `omitReferenced`,
    `omitInstKept`; (b) `None => continue` in `elab_omit` is killed by
    `varAuto/omitAuto`, NOT `varAuto/omitTypeAuto` (its `[Wrap α]`
    matches the instance, which has a uid); (c) dropping the inner
    `with_auto_bound_implicit` in the sanity run fails
    `variable_binders_auto_bind` and `varAuto/def` + 32 more; (d) autos
    after the binder fvars fails `varAuto/afterExplicit`, `varAuto/def`
    + 11 more; (e) seeding `elab.options` after `elab_section_vars`
    fails `varAuto/offAfter`; (f) `uid_of` always `None` fails the
    `include/*` and `omit/*` rows; (g) no `InvalidBinderAnnotation`
    first-line arm fails the first-line test and `varAuto/notClass`.
  - Task 3: (a) `section_fvars` from the last `var_uids.len()` of `ys`
    fails `rebuildInclude`, `rebuildIncludeH`, `rebuildOmitName`,
    `rebuildOmitRefH`, `rebuildOmitInstIgnored` and
    `omit_type_pattern_without_uid_errors`; (b) skipping
    `install_empty_lctx` fails `varAuto/rebuildBodyUnknown`; (c) always
    rebuilding kills include rows vi1, vi2, vi5-vi10 (not vi3/vi4) and
    `varAuto/includeX`; (d) `forall_bounded_telescope(.., len - 1)` fails
    all 24 rebuild-reaching rows and the omit test; (e)
    `install_empty_lctx` not installing fails its unit test; (f)
    `OmitUndeclared` via `names::render` fails
    `omit_type_pattern_without_uid_errors`.
- Survivors: none.
- Deviations: `OmitUndeclared` for an mvar binder or anonymous instance
  prints leanr's `fvar_message_name` (e.g. `inst✝`), not the oracle's
  hygienic hash name; the rebuild never reinstalls the outer lctx;
  Task 2 also gave `InvalidBinderAnnotation` an oracle first line
  (`Binders.lean:218`, for `varAuto/notClass`). `leanr_meta` additive
  changes: `forall_bounded_telescope` is `pub`, plus
  `MetaCtx::install_empty_lctx`.
