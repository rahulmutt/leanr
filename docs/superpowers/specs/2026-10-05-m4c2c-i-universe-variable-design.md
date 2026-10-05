# M4c-2c-i — `universe`, `variable`, `include`, `omit` — design

Status: approved in brainstorming 2026-10-05 (architectural path).
First half of M4c-2c, after M4c-2b-ii shipped (#74, 005f75a).

Pinned oracle: `leanprover/lean4:v4.33.0-rc1`. Citations below were opened
against that toolchain's `src/lean/Lean` while writing this spec; they are
still subject to the "verify at plan time" rule (cites drift by 1-2 lines).

## Goal

Every declaration so far elaborates in an empty command context: no scope
universe names, no section variables. This slice ports the scope state and
commands that feed declarations from the enclosing `section`/`namespace`:
`universe`, `variable`, `include` and `omit`, plus the oracle's three
section-variable inclusion regimes (theorem, definition, axiom).

**Success:**
- Every new file-corpus record elaborates as the oracle does: per command,
  the same constants, or for a last command that errors, the same first
  error line.
- `universe`, `variable`, `include` and `omit` are dispatch arms, not
  seams; no `— M4c-2c` label remains (auto-bound is relabelled
  `— M4c-2c-ii`).
- Every existing corpus stays green.

## User decisions

1. **Split M4c-2c.** 2c-i = `universe` + `variable` with the full
   inclusion rules; 2c-ii = auto-bound implicits (headers, levels, variable
   binders). Rationale: Mathlib sets `autoImplicit := false`, while
   `variable`/`universe` are pervasive there.
2. **Satellites:** `include` and `omit` are in (they are the inclusion
   rules; `… in` already works via M4c-2b's `elab_in`). The typeless
   `variable {α}` binder-annotation update (`replaceBinderAnnotation`) is a
   `— later M4` seam.
3. **Approach A:** a faithful port of `runTermElabM`. Each declaration
   re-elaborates the scope's variable binder SYNTAX in its own scratch
   `TermElabM`, then applies its kind's inclusion regime. Rejected:
   pre-elaborating variables once into persistent expressions (B: diverges
   on fresh level mvars such as `variable (α : Type _)`, instance
   registration and mvar identity); splicing variable binders into each
   declaration's syntax (C: inclusion must be decided after elaboration).

## Oracle behaviour

- **`elabUniverse`** (`Elab/BuiltinCommand.lean:283-284`) →
  **`addUnivLevel`** (`Elab/Command.lean:831-837`): per id, error
  ``a universe level named `u` has already been declared``
  (`Exception.lean:43-44`) if `u ∈ scope.levelNames`, else cons it.
- **`elabVariable`** (`BuiltinCommand.lean:415-430`): each binder goes
  through `replaceBinderAnnotation` (`:343`, using `typelessBinder?`
  `:320`); the binders are sanity-elaborated under `runTermElabM` (so
  errors fire at the `variable` command); then each binder is pushed to
  `varDecls` and one macro-scoped uid per binder id to `varUIds`.
- **`runTermElabM`** (`Command.lean:774-800`): `liftTermElabM` (scope
  `levelNames` become the term-level `levelNames`) → `withAutoBoundImplicit`
  → `elabBinders scope.varDecls` → `synthesizeSyntheticMVarsNoPostponing`
  → `sectionFVars := uid ↦ fvar` → `resetMessageLog` →
  `addAutoBoundImplicits` → if all fvars, `withoutAutoBoundImplicit (elabFn
  xs)`, else the mvar-rebuild branch (auto-bound only).
- **`expandDeclId`** (`DeclModifiers.lean:326-343`): explicit `.{u}`
  names are consed onto `currLevelNames` (the scope names), raising the
  "already declared" error on a clash.
- **`sortDeclLevelParams scope allUser used`** (`DeclUtil.lean:79-88`):
  scope names are exempt from "unused universe parameter"; used user names
  come first in declaration order, the rest sorted by `Name.lt`.
- **`withHeaderSecVars vars sc headers check`** (`MutualDef.lean:455-492`):
  keep the fvars of the header types; add `includedVars`; close
  transitively (`addDependencies`); if `check`, an omitted var in that set
  raises ``cannot omit referenced section variable `x` ``; then add every
  non-omitted inst-implicit var whose type's fvars are all already kept.
  Restricts lctx and local instances (`removeUnused`).
- **`withUsed`** (`MutualDef.lean:595-611`): keep the fvars of header types,
  instantiated values and let-rec bodies, closed by `removeUnused`.
- **Call sites:**
  - theorem body: `elabFunValues` under `withHeaderSecVars vars sc
    #[header]` (`MutualDef.lean:534`), check on — the proof is elaborated
    in the restricted context.
  - async theorem signature: `withHeaderSecVars` (`:1279`), then
    `mkForallFVars vars header.type` → `levelMVarToParam` →
    `sortDeclLevelParams scopeLevelNames …` (`:1279-1291`).
  - `finishElab` (`:1421-1438`): all-theorem → `withHeaderSecVars (check
    := false)`, else `withUsed`; `MutualClosure.main vars …` abstracts the
    kept vars; then `levelMVarToParamTypesPreDecls`,
    `fixLevelParams preDefs scopeLevelNames allUserLevelNames`.
  - axiom (`Declaration.lean:101-133`): `mkForallFVars vars type (usedOnly
    := true)` (`:118`) — `include` and the inst-implicit closure do NOT
    apply.
- **`elabInclude`** (`BuiltinCommand.lean:551-563`): per id, the first
  index among `varDecls.flatMapM getBracketedBinderIds` (`Command.lean:688`)
  → its uid; miss ⇒ ``invalid 'include', variable `x` has not been
  declared in the current scope``. Append to `includedVars`, remove from
  `omittedVars`.
- **`elabOmit`** (`BuiltinCommand.lean:565-606`): under `runTermElabM`,
  each omit is a name (`ident`, `[h : T]`) or a type (`[T]`, elaborated by
  `elabTermAndSynthesize`, matched by `isDefEq` with the mctx restored).
  Unused omit ⇒ `` `o` did not match any variables in the current scope ``.
  Append to `omittedVars`, remove from `includedVars`.
- **Not observable:** the `unusedSectionVars` lint (warning; the dumper
  keeps errors only); `deprecated.oldSectionVars` (no `set_option`).

## Design

### Scope state (`command/scope.rs`)

`Scope` gains, cloned into nested scopes and dropped at `end` like the
existing fields:

- `level_names: Vec<NameId>` — newest first (the oracle's list).
- `var_decls: Vec<SyntaxNode>` — bracketed-binder syntax.
- `var_uids: Vec<u32>` — parallel to the flattened binder ids of
  `var_decls`; minted from a `CommandElab` counter (the oracle's
  macro-scoped uids are only keys).
- `included_vars: Vec<u32>`, `omitted_vars: Vec<u32>`.

### Commands (`command/vars.rs`, new)

- **`universe`**: `addUnivLevel` per id.
- **`variable`**: a typeless binder ⇒ seam
  ``variable binder-annotation update — later M4``. Otherwise run the
  shared runner over `var_decls ++ binders` (sanity elaboration; any error
  stops the command), then push the binders and mint uids.
- **`include`**: as the oracle; new error `IncludeUndeclared`.
- **`omit`**: as the oracle, under the shared runner; new error
  `OmitUnmatched`. The oracle's "has not been declared in the current
  scope" branch is unreachable when every runner var has a uid; pinned by
  a unit test or dropped (decided at plan time).

### Shared runner (`run_term_elab_m`, `command/vars.rs`)

1. `elab.level_names = scope.level_names`.
2. Elaborate `scope.var_decls` with `extract_binder_group` +
   `push_binder_group` (local instances registered), then
   `synthesize_synthetic_mvars_no_postponing`.
3. Build `section_fvars: Vec<(u32, FVarId)>`; call `elab_fn(vars)`.

The mvar-rebuild branch is unreachable without auto-bound: an `Internal`
guard. Auto-bound inside variable binders keeps the existing
`unknown_ident_to_auto_bound_seam`, relabelled `— M4c-2c-ii`.

`elab_declaration_in_scope`, `variable` and `omit` call the runner.

### Level names (`command/header.rs`, `def.rs`, `axiom.rs`)

- `expand_decl_id` takes the scope names as `currLevelNames`: an explicit
  `.{u}` clashing with a scope name raises `AlreadyDeclaredUniverseLevel`;
  `level_names` (allUserLevelNames) = explicit consed onto scope.
- `fix_level_params` and the async signature pass `scope_level_names` to
  `sort_decl_level_params` instead of `&[]`.

### Inclusion (`command/vars.rs`)

Three helpers, each returning the kept vars plus a restricted lctx /
local-instance set:

- `with_header_sec_vars(vars, sc, header_tys, check)`;
- `with_used(vars, header_tys, values)`;
- `used_only(vars, ty)` (axiom: fvars of `ty`, closed through var types,
  as `mkForallFVars (usedOnly := true)`).

| Path | 2c-i |
|---|---|
| theorem body | `elab_value` runs inside `with_header_sec_vars(…, check = true)`: a non-included variable is an unknown identifier in the proof |
| async signature | `check_async_signature` abstracts the kept vars before `level_mvar_to_param` and the sort |
| `finish_elab` | theorem: `with_header_sec_vars(check = false)`; else `with_used`. After `instantiate_mvars`: `mk_forall(kept, ty)`, `mk_lambda(kept, value)` BEFORE `levelMVarToParamTypesPreDecls`, `fix_level_params` and `abstract_nested_proofs` |
| axiom | `used_only` after the header `mk_forall`, before `level_mvar_to_param` |
| example | as def (`with_used`); `Built::Check` |

**Ordering risk (probe at plan time):** the header elaborates with every
variable in the lctx, but `level_mvar_to_param_headers` sees only
`header.ty`, so a `variable (α : Type _)` level mvar survives until the
vars are abstracted, and `u_N` numbering depends on that order.

### Errors (`error.rs`)

| Variant | Message (first line) |
|---|---|
| `AlreadyDeclaredUniverseLevel(u)` | ``a universe level named `u` has already been declared`` |
| `IncludeUndeclared(x)` | ``invalid 'include', variable `x` has not been declared in the current scope`` |
| `OmitUnmatched(o)` | `` `o` did not match any variables in the current scope `` |
| `OmitReferenced(x)` | ``cannot omit referenced section variable `x` `` |

Every rendering (backticks, `[T]` pretty-printing in `OmitUnmatched`) is
verified against the oracle at plan time.

### Seam relabelling

- `command_seam`: `universe`/`variable`/`include`/`omit` leave the table.
- Auto-bound (headers and variable binders): `— M4c-2c-ii`; update
  `oracle_file.rs` (`universe_and_variable_are_m4c2c_seams`, renamed) and
  `oracle_decl.rs:61`.
- Typeless `variable` binder: `— later M4`.

## Testing

**Gate:** the M4c-2a file corpus (`dump_decls.lean files` →
`file-queries.jsonl`, `fixtures:regen-decls`, `oracle_file_gate`);
`CORPUS_FLOOR` raised from 131 to the new count. Every record is
oracle-probed at plan time (scratch in `target/m4c2cprobe/`, never `/tmp`).
Each family has at least one row that distinguishes the oracle from a
plausible wrong implementation, and each task's mutation is RUN.

- **univ/**: scope universe in a def / theorem / axiom; `universe u v` +
  `def f.{w}` (order); an unused scope name (no error, absent from
  levelParams); duplicate `universe u`; `universe u` + `def f.{u}`; a
  `universe` scoped by `section … end`.
- **var/def**: var used only in the body (included); unused var
  (excluded); var reached only through another var's type (transitive);
  inst-implicit var included only if referenced; variable order is
  declaration order.
- **var/thm**: header-only reference; a var used only in the proof is an
  unknown identifier; the inst-implicit closure; async vs. sync (header
  with an mvar).
- **var/axiom**: `include` ignored; unreferenced inst var dropped.
- **include/omit**: `include h` + theorem; `include h in theorem …`;
  undeclared include; `omit [C α] in theorem …`; omit by name; omitting a
  referenced var; unmatched omit; omit then include.
- **var/levels**: `variable (α : Type _)` (`u_1` numbering);
  `variable (α : Type u)` under `universe u`.
- **var/errors + seams**: an error inside a `variable` binder stops at
  that command; `variable {α}` ⇒ later-M4 seam; `variable (x : β)` with an
  unbound `β` ⇒ M4c-2c-ii seam.

**Unit pins:** seam labels; the runner's `Internal` guard; the omit
unreachable branch if kept.

**Suggested plan split (one PR):** (1) corpus + dumper rows; (2) `Scope`
fields, `universe`, level-name threading; (3) runner + `variable`;
(4) inclusion regimes in def / theorem / axiom; (5) `include` / `omit`;
(6) docs, seam relabels, ledger.

## Out of scope (named seams or unchanged)

- Auto-bound implicits everywhere: `— M4c-2c-ii`.
- `variable {α}` binder-annotation update: `— later M4`.
- `unusedSectionVars` lint, `deprecated.oldSectionVars`, `set_option`.
- Mutual / recursive declarations, `let rec` (the `toLift` part of
  `collectUsed`): unchanged seams.

## Landed

- PR: pending (the controller fills it at merge). Commits: e8701ce
  (corpus rows, pending), a14d0ea (universe names), 30a75ae (runner,
  `variable`, `withUsed`), 0331c1d (theorem/axiom regimes, restricted
  theorem body), ec0741c (`include`/`omit`), and the closing commit
  (floor, docs, ledger).
- Corpus: 131 → 211 file-query records (`CORPUS_FLOOR` 211; the
  `PENDING` filter is deleted). 76 planned rows plus four oracle-probed
  rows added mid-slice to kill surviving mutations: `var/levelMVar`
  (Task 3, closure-after-`abstractNestedProofs`), `varLevel/thmBodyPinsHole`
  (Task 4, async signature sorted before abstraction),
  `omit/referencedOrder` and `omit/referencedAnonInst` (Task 5, omit
  check order and `inst✝` rendering). `decl-queries.jsonl` unchanged.
  `leanr_kernel` untouched; `leanr_meta` gains one additive accessor,
  `MetaCtx::erase_locals` (with a unit test).
- Deviations: Plan amendments 1-7 (reuse `UniverseAlreadyDeclared`;
  `OmitUnmatched` renders source text; the undeclared-omit branch dropped;
  abstraction before `abstractNestedProofs`; `u_N` ordering via
  abstracting before `levelMVarToParam`; no sync-theorem row; variable
  auto-bound seam wording). Task 3 extras: `ElabError::TypeExpected`
  gained its oracle first line (`type expected, got`, for `var/errType`),
  and the typeless `variable [x]` arm (`typelessBinder?`'s `[$id]`) is the
  same `— later M4` binder-annotation-update seam as `variable {α}` when
  `x` names a section variable, otherwise an ordinary instance binder.
- Mutation results (each applied, gate run with
  `cargo test -p leanr_elab --test oracle_file oracle_file_gate`,
  reverted):
  - Task 1: `enabled` forced true → FAILED on the new rows (`— M4c-2c`
    seam stops).
  - Task 2: `fix_level_params` given `&[]` → `universe/unusedScope`,
    `universe/axiomUnusedScope`; `expand_decl_id` from `Vec::new()` →
    broad `universe/*`; `elab_universe` push instead of cons →
    `universe/order`, `universe/thmOrder`.
  - Task 3: `used_vars` over the type only → `var/defBody` and many
    more; `kept` not reversed → `var/order`, `var/multiCmd`,
    `var/instDef*`; closure after `abstract_nested_proofs` → only the new
    `var/levelMVar` (`var/auxProof` cannot see it).
  - Task 4: no lctx erase → `varThm/bodyOnly`,
    `varThm/instUsedInProofOnly`; skip the inst loop → `varThm/inst`,
    `varThm/instCoveredByBinder`; inst loop ignoring "all fvars kept" →
    `varThm/instNotCovered`; axiom via `header_sec_vars` →
    `varAxiom/inst`; async signature sorted before `mk_forall(kept)` →
    only the new `varLevel/thmBodyPinsHole`.
  - Task 5: include not clearing omitted → `omit/thenInclude`; omit not
    clearing included → `omit/includeThenOmit`; `[T]` by `ExprId`
    equality → `omit/instDefeq`, `omit/twoMatch`; break after first match
    → `omit/twoMatch`, `omit/referencedOrder`; def consulting `include` →
    `include/def`; omit check in variable order → `omit/referencedOrder`;
    anonymous inst via `names::render` → `omit/referencedAnonInst`.
- Surviving mutation: `remove_unused` skipping the type-fvar step
  survives. On the theorem path it is unobservable, as in the oracle:
  `addDependencies` has already closed `used`. Only the def/axiom
  `used_vars` path can observe it, and no row pins it. The Task 6
  candidate row (`variable (n : Nat) (h : (fun (_ : Nat) => True) n)` +
  a def using `h`) diverges for an unrelated reason: the oracle's
  binder type is beta-reduced (`h : True`), leanr keeps the redex
  `(fun _ => True) n`. The same divergence shows on a plain def header
  binder (`def f (n : Nat) (h : (fun (_ : Nat) => True) n)`), so it is a
  pre-existing binder-type gap, not a section-variable one. The row was
  not added; pinning the type step waits on that gap or a redex-free
  probe.
- Open seams: auto-bound implicits (`— M4c-2c-ii`); the `variable {α}` /
  `variable [x]` binder-annotation update (`— later M4`); `OmitUnmatched`
  source-text rendering (comments inside the item differ);
  `IncludeUndeclared` renders the id by joining components, so escaped
  ids differ from the oracle.
