# M4c-1 — elaborating a single declaration — design

Status: approved in brainstorming 2026-10-03 (architectural path).
First slice of M4c (command elaboration), after M4b (term elaborator) closed
with #69.

Pinned oracle: `leanprover/lean4:v4.33.0-rc1`. Every citation below was
opened against that toolchain's `src/lean` while writing this spec. They are
still subject to the "verify at plan time" rule (cites drift by 1-2 lines).

## Goal

leanr can elaborate terms, but it cannot yet turn a command into a
declaration. This slice adds the smallest end-to-end vertical. It takes one
non-recursive `def`/`theorem`/`abbrev`/`opaque`/`axiom`/`example`, runs the
oracle's `elabMutualDef` → `addPreDefinitions` → `addNonRecAux` subset, and
admits the kernel-checked `ConstantInfo`s into an environment that grows.
The result is differential-tested against the oracle's own result for the
same source.

**Success:**
- `CommandElab::elab_decl` elaborates every in-scope corpus record. The new
  constants it adds equal the oracle's exactly, in order: the main
  declaration plus every `_proof_N` aux theorem from `abstractNestedProofs`.
- Every oracle-rejected record is rejected by leanr with the same first
  error line.
- Every out-of-scope input fails with a named seam (`UnsupportedSyntax`
  plus a slice label), never with a wrong `Ok` or an unrelated error.
- Every existing corpus (synth, elab, op, kernel, syntax) stays green.

## Decomposition (agreed)

- **M4c-1 (this spec):** a single declaration.
- **M4c-2:** the command loop over a whole fixture file, plus `namespace`,
  `section`, `open`, `universe` and `variable`, plus auto-bound implicits.
- **Later M4:** recursion (needs `match` and the equation compiler),
  `mutual`, `where`/`let rec`, attributes, `instance`/`structure`/`inductive`,
  `letToHave`, and compilation.

## User decisions

1. **Gate:** compare the full `ConstantInfo` and the aux declarations. That
   is name, `levelParams` in order, type, value, hints/height, safety and
   `all`, plus the set and order of aux declarations added. Attributes and
   compilation are seams.
2. **Universes:** explicit `.{u,v}`, plus `levelMVarToParam` and
   `collectLevelParams`/`sortDeclLevelParams` (leftover level mvars become
   `u_1, u_2, …`). Auto-bound implicits go to M4c-2.
3. **Approach A:** run the term elaborator once per declaration, then
   promote and commit (the oracle's `liftTermElabM` shape).
4. **Harness:** a per-record oracle dump over Elab0. There is no base/target
   `.olean` split.
5. **`letToHave` is a seam.** It is on by default
   (`Elab/PreDefinition/Basic.lean:21`) and is a 449-line Meta pass
   (`Meta/LetToHave.lean`). M4c-1 detects a `let` in the declaration's
   final type or value and fails with a named seam. The port is a follow-up
   slice.

## The oracle model

Sources: `Elab/MutualDef.lean`, `Elab/PreDefinition/{Main,Basic}.lean`,
`Elab/DeclUtil.lean`, `Meta/AbstractNestedProofs.lean`, `Meta/Closure.lean`,
`Meta/Tactic/AuxLemma.lean`.

1. **`expandDeclId`** (`Elab/DeclModifiers.lean:326`). Builds the
   declaration name (M4c-1 has no namespace, so it is the root name) and
   puts the `.{u,v}` names into scope as level names.
2. **`elabHeaders`** (`MutualDef.lean:209`). Elaborates the binders, then
   the type. An omitted type becomes a fresh type mvar. Then
   `mkForallFVars`.
3. **`levelMVarToParamHeaders`** (`MutualDef.lean:1148`), which uses
   `levelMVarToParam` (`Term/TermElabM.lean:1059`,
   `MetavarContext.lean:1489`). Each level mvar left in the header type
   becomes a fresh `u_N`, skipping names already in use.
4. **Sync vs. async.** `Elab.async` defaults to `false`, but the `lean`
   command line sets it to `true` (`Elab/Frontend.lean:291-292`; the `CoreM.lean:35` default is `false`). With it on, a
   single `theorem` whose header type has no mvars takes `elabAsync`
   (`MutualDef.lean:1266`), which takes its level params **from the header
   type only**. Everything else takes `elabSync` → `finishElab`. leanr
   matches the command line, so the dumper sets `Elab.async=true` and leanr
   ports both branches.
5. **`finishElab`** (`MutualDef.lean:1343`).
   - `elabFunValues` elaborates the body against the header type, then
     `synthesizeSyntheticMVarsNoPostponing`, then `instantiateMVars`. A
     thrown error is **logged**, and the value becomes a labeled `sorry`
     (`:1398-1400`). The declaration is still added.
   - The pre-definitions are then built (with `mkLambdaFVars` over the
     header binders).
6. **`addPreDefinitions`** (`PreDefinition/Main.lean:288`).
   `ensureNoUnassignedMVarsAtPreDef` runs first. A single non-recursive
   pre-definition then goes to `addAndCompileNonRec` → `addNonRecAux`.
7. **`fixLevelParams`** (`PreDefinition/Basic.lean:75`). Runs
   `collectLevelParams` over the type and value, then
   `sortDeclLevelParams(scope, allUser, used)` (`Elab/DeclUtil.lean:79`),
   which raises the "unused universe parameter" error. It then rewrites
   self-`const`s to the final level params.
8. **`addNonRecAux`** (`PreDefinition/Basic.lean:179`):
   - Runs `abstractNestedProofs` (`:120`), which is skipped for `theorem`
     and `example`.
     - The value goes through `Meta.abstractNestedProofs`, which calls
       `mkAuxTheorem` (`Meta/Closure.lean:457`).
     - That uses `Closure.mkValueTypeClosure` with `zetaDelta := true`,
       then `mkAuxLemma` (`Meta/Tactic/AuxLemma.lean:43`).
     - `mkAuxLemma` names the aux with the `_proof` kind and adds it with
       `addDecl` **immediately**, as a `thmDecl`, or as an unsafe opaque
       `defnDecl` if anything is unsafe.
     - Aux lemmas are cached in `auxLemmasExt`, keyed by type, so
       identical proofs share one aux.
   - Runs `letToHaveType`/`letToHaveValue`. This is the seam from
     decision 5.
   - Builds the `Declaration`:

     | kind | Declaration | hints / notes |
     |---|---|---|
     | `def`, `example` | `defnDecl` | `regular (getMaxHeight env value + 1)` (`Environment.lean:2890`), safe |
     | `abbrev` | `defnDecl` | `abbrev` hints |
     | `theorem` | `thmDecl` | — |
     | `opaque` | `opaqueDecl` | — |

     `all = [name]` throughout.
   - Calls `addDecl`.
   - The rest is not compared (seams): attributes, `markMeta`/
     `noncomputable` tagging, compilation, docs and info.
9. **`example`** runs under `withoutModifyingEnv` (`MutualDef.lean:1197`),
   so it adds no constants.
10. **`axiom`** goes through `elabAxiom` (`Elab/Declaration.lean:101`, `axiomDecl` at `:125`), not
    `elabMutualDef`. The plan opens it and records its steps. The expected
    shape is header, then `levelMVarToParam`, then level-param sort, then
    `axiomDecl`.

## Architecture

### `leanr_kernel` — one additive API (TCB-neutral)

> **Superseded by Amendment 1 item 1:** the landed API is
> `add_decl_in(&mut self, scratch: &mut Store, d)`; its scratch lifecycle
> contract is in its doc comment (`crates/leanr_kernel/src/env.rs`).

`Environment::add_decl_from_scratch(&mut self, scratch: &Store, d:
Declaration) -> Result<(), KernelError>`. It promotes every id in `d` into
`self.store` with the existing `bank::scratch::{promote, promote_name,
promote_level}`, then calls `add_decl`. A failed check leaves `constants`
unchanged. The plan verifies that ids promoted but left orphaned by a
rejected declaration are harmless, i.e. unreachable from `constants`.

### `leanr_meta` — new ports (under the additive-accessor precedent)

| Port | Oracle |
|---|---|
| `level_mvar_to_param` | `MetavarContext.lean:1489` |
| `collect_level_params` | `Util/CollectLevelParams.lean:72` |
| `sort_decl_level_params` | `Elab/DeclUtil.lean:79` |
| `get_max_height` | `Environment.lean:2890` |
| `abstract_nested_proofs` | `Meta/AbstractNestedProofs.lean` (118 lines) |
| `mk_value_type_closure` + `mk_aux_theorem` | `Meta/Closure.lean` (465 lines) — the largest port in the slice |
| `mk_aux_lemma` | `Meta/Tactic/AuxLemma.lean:43` — including `_proof` naming via `mkAuxDeclName` |

Notes on these ports:
- `sort_decl_level_params` is a pure function.
- `mk_aux_lemma`'s cache is per declaration in M4c-1, because the
  environment resets for each record. An env-wide `auxLemmasExt` is an
  M4c-2 concern.
- `instantiate_level_mvars` becomes `pub` if the elaborator needs it.
- Aux declarations are not added to the environment during elaboration.
  They are **returned** to the caller (see the data flow below).
  `mkAuxLemma` would otherwise need the environment to change while it is
  borrowed. Within one declaration, nothing after `abstractNestedProofs`
  looks up the aux constant before `addDecl`:
  - `getMaxHeight` ignores theorems.
  - If a plan-time read of the code finds a lookup, the plan raises it as a
    design amendment.

### `leanr_elab` — new `command/` module

- **`DefView::from_syntax`.** Decodes `declModifiers`, `declId`,
  `declSig`/`optDeclSig` and `declValSimple`. It raises named seams for the
  following, and never falls through to an unrelated error:
  - attributes, docstrings, and any modifier other than none
    (`private`/`protected`/`noncomputable`/`unsafe`/`partial`/`nonrec`)
  - `declValEqns`, `where`, termination hints, `deriving`
  - `instance`, `structure`, `inductive` and other commands
  - a body that names the declaration itself. In the oracle that is
    recursion; in leanr it would otherwise surface as an unknown identifier.
    This is detected syntactically before elaboration.
- **`CommandElab { env: Environment, exts: … }`.**
  `elab_decl(&mut self, stx) -> Result<Vec<Name>, ElabError>` returns the
  new constants' names in admission order.

### How a declaration flows

1. `elab_decl` opens a scope: a fresh scratch `Store`, a `MetaCtx` and a
   `TermElabM`, all borrowing `self.env.view()`.
2. Oracle steps 1-8 run inside that scope and return `(scratch,
   Vec<Declaration>)`, with the aux `_proof_N` theorems first and then the
   main declaration.
3. The scope ends and releases the borrow.
4. Each declaration is committed in order with `add_decl_from_scratch`. The
   first failure stops the loop and is returned. The declarations already
   committed stay, which matches the oracle: an aux lemma's `addDecl` has
   already happened by then.
5. `example` skips the commit.

**Seams:**
- Environment extensions are read-only in M4c-1. `abbrev`'s
  `@[reducible]`/`@[inline]` and `instance_reducible` are not written.
- A `let` remaining in the final type or value raises the `letToHave` seam
  (decision 5).

## Errors

New `ElabError` variants, each with an `oracle_first_line`:

| Variant | Raised by |
|---|---|
| already declared | `expandDeclId` / `addDecl` |
| unused universe parameter | `sortDeclLevelParams` |
| unassigned mvars | `ensureNoUnassignedMVarsAtPreDef`, header "failed to infer" |
| `Kernel(KernelError)` | the kernel rejects the declaration |

Notes:
- **Logged errors.** The oracle *logs* most command errors rather than
  throwing them (`finishElab` turns a failed body into `sorry`, and the
  declaration is still added). The dumper therefore writes an `err` record
  whenever the message log has an error, carrying the first error's first
  line. leanr must return `Err` with the same first line. leanr does not
  model the sorry'd declaration.
- **Seams** stay `UnsupportedSyntax("<what> — <slice label>")`.
  `seam_audit.rs` covers the new labels.

## Harness

- **`tests/fixtures/elab/dump_decls.lean`.**
  - Runs in prelude mode over Elab0, with `LEAN_PATH=tests/fixtures/elab`
    (never stock Init) and `Elab.async=true`.
  - For each `(id, src)`, it runs `elabCommand` from the Elab0 environment
    and diffs `env.constants` before and after, in insertion order.
  - It writes `{id, src, consts: [{name, kind, levelParams, type, value?,
    hints?, safety?, all}]}` using the canonical Expr JSON (the same
    encoding as `dump_elab.lean`).
  - It writes `{id, src, err}` instead when the log has an error.
- **mise task:** `fixtures:regen-decls` produces
  `tests/fixtures/elab/decl-queries.jsonl`.
- **`crates/leanr_elab/tests/oracle_decl.rs`.**
  - A `with_command_elab` support helper replays Elab0 into an owned
    `Environment`, once per record.
  - The test runs `elab_decl` and encodes each new constant with
    `encode_expr`, then requires exact JSON equality with the record.
  - It enforces a minimum-record floor, and asserts no fvars, no mvars and
    no `sorryAx` in the admitted constants.

## Corpus

About 35 records. Every one is oracle-probed when the plan is written, and
any probe outcome that differs from this list amends the spec.

- **Kinds:** one plain record each for `def`, `theorem`, `abbrev`,
  `opaque`, `axiom` and `example` (`example` gives `consts: []`).
- **Types:** an omitted type (inferred), and an explicit type that needs
  unification with the body.
- **Universes:**
  - explicit `.{u}` and `.{u,v}`
  - `Sort _` in the header, giving `u_1`
  - `@id`-style bodies whose level mvars become params
  - the order chosen by `sortDeclLevelParams` (user names first, then
    `u_N`)
  - the unused `.{u}` error
  - the async theorem path, where a universe appears only in the value
- **Heights:** a chain def → def → def, a def over a theorem (heights
  ignore theorems), and `abbrev`'s hints. Within one record, preceding
  declarations come from Elab0. Multi-declaration chains wait for M4c-2's
  file loop, so the chain uses Elab0 constants of known height.
- **Nested proofs:**
  - one proof giving `_proof_1`
  - two identical proofs sharing one aux (cache)
  - two distinct proofs giving `_proof_1` and `_proof_2`
  - a proof under a binder (closure over fvars)
  - a proof mentioning a universe (closure over level params)
  - a theorem body (no abstraction)
- **Errors:** an already-declared name (an Elab0 constant), unassigned
  mvars, a body type mismatch, and an unused universe.
- **Seams** (leanr-only smoke tests, not oracle records): an attribute, a
  modifier, `declValEqns`, self-reference, `let` in the body, `instance`.

## Testing discipline

- Each `leanr_meta` port gets unit tests derived from the oracle source,
  with values from scratch `run_meta` probes where no corpus record
  discriminates.
- Every task lists its mutations and their kill tests. Each mutation is run
  for real and reverted. Briefs' tests are not trusted until a mutation
  fails them.
- A final citation sweep covers the whole branch.
- `mise run ci` (including fmt and clippy) blocks before every push.

## Out of scope (named seams)

- namespaces, sections, `open`, `universe`, `variable`, auto-bound
  implicits, the command loop (M4c-2)
- recursion, `mutual`, `where`/`let rec`, `declValEqns`/`match`
- attributes, modifiers, `instance`/`structure`/`inductive`, `deriving`
- `letToHave`, compilation, docs/info trees, env-wide `auxLemmasExt`
- writes to environment extensions (reducibility status)

## Plan shape (suggestion for writing-plans)

There are two plans, one PR each:

- **P1 substrate:** the kernel `add_decl_from_scratch`; the level-param
  ports; `get_max_height`; the Closure, `mk_aux_lemma` and
  `abstract_nested_proofs` ports, with unit tests.
- **P2 command elaborator:** `DefView`, `CommandElab`, the pipeline,
  errors, the dumper, the corpus and the gate.

## Amendment 1 (plan-time refinements and execution-time rulings)

1. **The kernel API is `add_decl_in(&mut self, scratch: &mut Store, d)`.** It promotes every id of `d` into `self.store` (`promote_declaration`), then checks against a fresh scratch. The plan's first version skipped the promote walk. The P1 gate found that this breaks cross-declaration references inside one scratch store: the main declaration references the aux by its scratch NameId, but the kernel looks constants up by persistent id. The plan was corrected at execution time (ruling R5) back to the spec's original design. Promoted ids of a rejected declaration remain in the store as orphans unreachable from `constants`.
2. **The aux-lemma cache is env-wide in the oracle.** In the probe, `foo3` reused `foo1._proof_1` from an earlier declaration. M4c-1's corpus resets the environment for each record, so a per-declaration cache (`AuxLemmas`) is observably identical there, but only for ONE `elab_decl` per `CommandElab`. A second call on the same `CommandElab` that would mint an aux lemma after an earlier one was admitted is the named seam `aux-lemma reuse across declarations (auxLemmasExt) — M4c-2` (P2 final review C3; probe: an identical `nb` after `na` reuses `na._proof_1`). M4c-2's file loop must lift the cache to `CommandElab` scope, keyed by type and level params, and must also keep the earlier declarations' aux names as conflicts.
3. **Pending aux names count as "in the environment"** in two places: `mkUniqueName`'s conflict check, and `isNonTrivialProof`'s "constant not in env" test. In the oracle both see aux lemmas that `mkAuxLemma` has already added.
4. **New named seams in P1:**
   - a `letE` reached by `abstractNestedProofs` (unreachable from P2, which rejects `let` first);
   - an unassigned mvar reached by the Closure walk (unreachable after `ensureNoUnassignedMVars`);
   - an aux lemma over unsafe constants (the oracle's unsafe `defnDecl` would be rejected by `add_decl_in`);
   - Closure with `zetaDelta := false` (`check` and dependent let-decls) is not ported, because no M4c-1 caller passes it;
   - **`abstractNestedProofs` itself looks up a pending aux constant.** Trigger: a binder type of some `lam`/`forallE` telescope the walk opens (the value's own, or one nested in a binder type or argument) holds a non-trivial proof, and an `is_proof`/`infer_type` in that telescope's BODY whnf's through a K-like recursor (`Eq.rec` iota, `to_ctor_when_k`) over it. Only the body can trigger it: as in the oracle (`visitBinders`, `AbstractNestedProofs.lean:77-89`), every binder type is visited under the telescope's ORIGINAL types, and only the body runs under the visited (aux-mentioning) types (final review Important #1). The oracle succeeds because `mkAuxLemma` has already called `addDecl`. leanr returns `MetaError::Unsupported("...pending aux lemma...M4c-1 seam...")`. The fix, a pending-constant overlay for infer/whnf, is deferred to a follow-up. This corrects the spec's claim that nothing looks up the aux constant before `addDecl`.
5. **`levelMVarToParamHeaders` applies only to `theorem` or Prop-typed headers** (`MutualDef.lean:1148-1160`). Definition headers keep their level mvars until `levelMVarToParamTypesPreDecls` (`MutualDef.lean:1434`, `PreDefinition/Basic.lean:56-58`), which covers **types only**. A level mvar left in a value is an error (`ensureNoUnassignedLevelMVarsAtPreDef`, `PreDefinition/Main.lean:76-97`). This sharpens spec § The oracle model step 3, and P2's plan owns it.
6. **Mutation rulings.** Task 6 mutation 5 (abstract decl i's type over all `xs`) is NOT equivalent, although the plan called it so: the range length shifts de Bruijn indices (oracle `abstractRange i xs`). It is killed by `closure_renames_level_params_to_u_n`. Task 7 mutation 6 (advance `next_idx` past the candidate) is EQUIVALENT in this port: `pending` never shrinks and the generator serves only `_proof`.
7. **Oracle name.** The nested-proof marker is `Lean.Grind.nestedProof`, not `Grind.nestedProof`.
8. **Plan-cite drift.** Closure.lean cites drifted by about 13-25 lines, MetavarContext/Level cites by 1-3. All were corrected in code.

## Amendment 2 (P2 plan-time findings, 2026-10-03)

Every corpus record was run through the final dumper while the P2 plan (`docs/superpowers/plans/2026-10-03-m4c1-p2-command-elab.md`) was written. These findings refine the spec.

1. **Async theorems report through snapshot tasks.** With `Elab.async=true`, every well-formed theorem takes `elabAsync`: `levelMVarToParamHeaders` runs before the `!type.hasMVar` test (`MutualDef.lean:1236-1242`). Its body errors go to `Command.State.snapshotTasks`, not `messages`. The dumper walks both. Without that, an ill-typed theorem dumps as `consts: []` with no error.
2. **The theorem signature uses the type only.** `elabAsync` sorts level params from the header type alone (`:1288-1291`), so a universe used only in a proof is "unused". The rest of the theorem path is `finishElab`, shared with defs.
3. **`u_N` order depends on the path.** For a theorem or a Prop-typed def, header level mvars become params early and join the header's `levelNames`, so they sort as user names, in declaration order (`u_1 … u_9, u_10`). For other defs and for axioms they are leftovers and sort lexicographically (`u_1, u_10, u_2, …`). The corpus pins both.
4. **The value's binders are `cleanupAnnotations`'d** (`forallBoundedTelescope … (cleanupAnnotations := true)`, `:536`). An `optParam` binder stays in the type but not in the value.
5. **A binder group's type is elaborated once per name** (`elabBinderViews`). leanr's `push_binder_group` elaborated it once per group, a pre-existing divergence in `forall`/`depArrow`/`let` binders. P2 fixes it.
6. **`example` is kernel-checked.** It is `addDecl`'d under `withoutModifyingEnv`, so leanr runs `leanr_kernel::check_declaration` and discards the result, instead of skipping the commit (§ How a declaration flows, step 5).
7. **Harness changes:**
   - The environment's constant map is unordered, so `consts` is sorted by `Name.lt`. The gate sorts leanr's names with `name_cmp` and checks the admission order (aux first) separately.
   - Compile errors are logged as errors, and Elab0 lacks the compiler's runtime support (`Nat.succ` needs `Nat.add`). Compilation stays a seam, and the corpus avoids values whose codegen needs missing constants.
   - leanr's parser has no `binderDefault`. The explicit `optParam` spelling covers that path.
8. **Error first lines need diagnostics leanr lacked:**
   - `mvarArgNames`;
   - the `.custom` error kind (failed-to-infer binder and definition types);
   - `LevelMVarErrorInfo`;
   - most-recent-first reporting;
   - `Type mismatch` vs `Application type mismatch: The argument`/`The last` (`ensureArgType`'s `f?`).

   P2 ports all of these as term-elaborator changes.
9. **Corpus:** 79 records, up from about 35: 54 admitting and 25 erroring. The list is in the plan's Task 1.

## Landed

### P1 (declaration substrate)

Commits (`git log --oneline main..HEAD`):

- `5d6a14b` leanr_kernel: add_decl_in promotes the declaration before checking (R5)
- `1f42e3f` leanr_meta: abstractNestedProofs pending-aux lookup seam (review R4)
- `f7e8e77` leanr_meta: abstractNestedProofs + AuxLemmas accumulator (mkAuxLemma/mkAuxTheorem)
- `e95f45f` leanr_meta: Closure.mkValueTypeClosure (zetaDelta := true)
- `221b8a4` leanr_meta: Core.betaReduce + zetaReduce (transform_with)
- `d1c3b7a` leanr_meta: getMaxHeight
- `521352c` leanr_meta: correct Task 3 oracle cites
- `8be6d50` leanr_meta: levelMVarToParam + Level.update*! simplifying rebuilds
- `63ce557` leanr_meta: collectLevelParams, sortDeclLevelParams, Name.cmp ports
- `f9efe6f` leanr_kernel: add_decl_in admits a declaration built in a caller scratch store
- `0df1b6e` docs: M4c-1 P1 declaration-substrate plan
- `cc033b2` docs: M4c-1 single-declaration elaboration — design spec
- (this commit) leanr_meta: M4c-1 P1 gate, foo2 + aux committed over Meta0; spec amendment 1

Mutation outcomes (from each commit body):

- add_decl_in: scratch-less check FAILS both tests; add_core unpromoted FAILS the admit test; R5 promote step removed FAILS the cross-decl and admit tests.
- Task 3 (levelMVarToParam and level-param ports): 6 mutations killed plus 5 more in collect/sort (all killed), and one equivalent (unchanged-max else_k builds raw max).
- Task 4 (getMaxHeight): 3 mutations killed.
- Task 5 (beta/zeta): 4 mutations killed.
- Task 6 (Closure): mutations 1-5 killed (5 is not equivalent, see item 6).
- Task 7 (abstractNestedProofs): mutations 1-5 killed, 6 equivalent. R4 seam pin killed by removing the map_err.
- Task 8 gate: (a) closure_new_level_param keeps `u`: gate test FAILS and `closure_renames_level_params_to_u_n` FAILS; (b) commit order swapped (main first): gate FAILS with UnknownConstant(foo2._proof_1); (c) Task 7 mutation 6 stays equivalent (single aux).

Final review fixes (`final-findings.md`; new commits on top of `2aee529`):

- `febfcd8` Important #1: `abstractNestedProofs` visits every binder type under the telescope's ORIGINAL lctx and only the body under the visited types (`visitBinders`, `AbstractNestedProofs.lean:77-89`). Before, an aux closing over an earlier binder got that binder's abstracted proof in its binder domain (silent wrong Ok). leanr re-pushes under new fvars (no kernel `modifyLocalDecl`), so the visit-cache entries from the type visits are copied old → new. Pins `binder_types_are_visited_under_the_original_lctx` and `binder_type_cache_entries_still_hit_in_the_body` (oracle probes `fooP`, `fooQ`). Amendment 1 item 4's seam trigger is reworded to body-only.
- `a67fb6c` Important #2: `anp_visit`, `core_transform_visit` (`beta_reduce`) and `transform_visit` (`zeta_reduce`, pre-existing) recurse through `guarded`. A depth-100000 term no longer aborts with a stack overflow.
- `ef77c86` Important #3: `add_decl_in`'s scratch lifecycle contract is documented (doc only), and `add_decl` points to it.
- (this commit) Minors: `sorryAx` / `Lean.Grind.nestedProof` are interned once per `abstract_nested_proofs` call, and intern errors propagate; a closure pin covers simultaneous `u`/`u_1` renaming; this spec now points from `add_decl_from_scratch` to Amendment 1 item 1.

Oracle cites corrected in the final sweep (code, plan and spec together): `Transform.lean:202` to `:204` (transform.rs); `CoreM.lean:80` to `:79` (`idx` field); `CoreM.lean:116-119` to `:117-120` (`isConflict`); `Level.lean:519-538` to `:519-537`; `DeclUtil.lean:79-89` to `:79-88`; `Environment.lean:2890-2902` to `:2890-2901`.

### P2 (command elaborator)

Commits (`git log --oneline main..HEAD`):

- `bc29f40` docs: M4c-1 P2 command-elaborator plan; spec amendment 2 (plan-time oracle findings)
- `3288632` M4c-1 P2: dump_decls.lean oracle corpus (79 records) + parse gate
- `84fd964` leanr_elab: declaration error variants + Type/Application type mismatch first lines
- `6f00a34` leanr_elab: elaborate a binder group's type once per name (elabBinderViews)
- `52600eb` leanr_elab: unassigned-mvar diagnostics (custom/level error infos, mvarArgNames, logUnassigned*)
- `b629c57` leanr_elab: command::view — DefView decoding and M4c-1 named seams
- `62ce25a` leanr_elab: CommandElab + def/abbrev/opaque/example pipeline; oracle_decl gate (43 records)
- `1b45156` leanr_elab: theorems and Prop headers (levelMVarToParamHeaders, async signature, pushMain Prop check)
- `dbb8600` leanr_elab: abstractNestedProofs in the def pipeline; aux theorems committed first
- `2a438eb` leanr_elab: document elab_def aux ordering and partial failure; fix elab_decl persistence cite
- `5ef73af` leanr_elab: axiom (elabAxiom); oracle_decl gate covers the whole corpus
- (this commit) M4c-1 P2: full oracle_decl gate (79 records), declaration seam audit, docs, spec Landed

Mutation outcomes (from each commit body):

- Task 1 (corpus): `CORPUS_FLOOR` 79 -> 80 FAILS the parse gate.
- Task 2 (error variants): 3 mutations killed (`arg_already_in_f`, the app remap in `args.rs`, the `TypeMismatch` arm strings); spine-vs-`f_args` compare is equivalent (the head is a constant).
- Task 3 (`elabBinderViews`): hoisting `elab_type` out of the per-name loop FAILS `binder_group_type_is_elaborated_per_name`.
- Task 4 (unassigned-mvar report): 6 mutations killed (oldest-first, `mvarArgNames` registration, `fun` and binder-group registration, level message, macro-scopes); dropping the visited skip is equivalent (leanr returns at its first error).
- Task 5 (`DefView`): 5 mutations killed (dotted self-reference, `starts_with(name)`, modifiers, dotted names, the termination seam). The termination seam runs on a synthetic tree, because the parser has no `Termination.suffix` content.
- Task 6 (pipeline): mutations 1-6 and 8-9 killed. Mutations 1 and 7 survived the corpus and got unit tests (`level_mvar_to_param_prepends_new_names_most_recent_first`, `level_mvar_without_error_info_hits_the_fallback`).
- Task 7 (theorems): 5 mutations killed (header `is_prop_full`, async signature skip and its late-collect variant, the pushMain Prop check, keeping `header.level_names`); `is_prop_full` -> `MetaCtx::is_prop` is equivalent on the corpus (pinned by a unit test).
- Task 8 (abstractNestedProofs): 4 mutations killed (main-before-aux, pre-abstraction height, skip abbrev, abstract example); abstracting a theorem is equivalent (proofs come back unchanged).
- Task 9 (axiom): 3 mutations killed (sort order, skipping `ensureNoUnassignedMVars`, the auto-bound mapping).
- Task 10 (gate): the `not yet ported (M4c-1 P2 Task N)` scan FAILS on a re-added label.

Oracle cites corrected in the sweep (code, plan and spec together): `Elab.async` is set on in `Elab/Frontend.lean:291-292`, not `CoreM.lean:35` (which declares it with default `false`); the async test is `MutualDef.lean:1236-1242` (was 1239-1247); `elabAsync`'s signature is `:1278-1298` and its type-only level sort `:1288-1291`; `pushMain` is `:1051-1053`; `mkThmDecl` is `PreDefinition/Basic.lean:192-197`; `expandDeclId` is `DeclModifiers.lean:326-343`; `elabAxiom` is `Declaration.lean:101-133` with `withAutoBoundImplicit` at `:109`.

Open seams carried forward:

- M4c-2: the command loop, namespaces/`protected`/dotted names, auto-bound implicits (header unknown identifier or universe), (the env-wide `auxLemmasExt` cache and the command loop: CLOSED in M4c-2a). The header auto-bound seam also fires for a dotted unknown name, where the oracle says "Unknown identifier".
- later M4: recursion (self-reference), `declValEqns`/`where`/termination hints, attributes, modifiers, `deriving`, `instance`/`structure`/`inductive`, `opaque` without a value, `letToHave`, compilation. The parser's missing `binderDefault` and its missing `Termination.suffix` content (`termination_by`/`decreasing_by` lex as application arguments, so from source they read "Unknown identifier `termination_by`" instead of the termination seam).
- P1's pending-aux lookup seam (Amendment 1 item 4), now surfaced as `UnsupportedSyntax` by `def.rs`.
- Aux theorems are dropped on an error between `abstract_nested_proofs` and `commit`.
- `Kernel(_)` errors have no oracle first line.
- The gate encoder erases binder names (`dump_decls.lean`'s `biStr`). Binder names are pinned only by `oracle_decl.rs`'s `quoted_binder_name_is_decoded` and `binder_smoke.rs`'s quoted/dotted binder tests. Add a binder-name channel to the dumper at the next corpus regen.
- After a kernel rejection of the main declaration, its aux theorems stay in the environment (as in the oracle). A re-declaration on the same `CommandElab` then collides on `foo._proof_1`, an error, never a wrong `Ok`. M4c-2, with the `auxLemmasExt` seam. (M4c-2a: the cache now keeps it; with the stop-at-first-error loop the re-declaration is unreachable through `elab_commands`)
- A binder with no type (`def f2 {α} (a : α)`) is the oracle's `expandBinderType` hole (`Binders.lean:24-28`), not auto-bound; the oracle admits `f2.{u_1}`. leanr seams it as ``binder group: missing `: T` (`expandBinderType` hole) — later M4``.
- `def _root_ : Nat := …` is an oracle error ("invalid declaration name `_root_`, …", `DeclModifiers.lean:268-269`); leanr seams it with the dotted-name M4c-2 seam.
- Names in messages are rendered without `«»` escaping (leanr's `Name` `Display`); the oracle escapes a component that needs it (`«a.b».c`). Only reachable for quoted names that contain `.` or non-identifier characters.

Final review fixes (`.superpowers/sdd/2026-10-03-m4c1-p2-command-elab/final-findings.md`):

- C1: identifiers are decoded (`«»` stripped, `ident.getId`) everywhere a source identifier becomes a `Name`: the declaration name and `.{u}` names (`view.rs`), `Sort u` level identifiers, binder names (`intern_binder_name`), and every lookup (`app::head::ident_prefixes`: `elab_app_fn_id`, `isLocalIdent?`, `fun`'s global-name gate, `binop%`'s `resolveId?`). `def «gq»` admits `gq`; `def «a.b»` admits the ATOMIC `«a.b»` (no longer a dotted seam); `def sr : Nat := «sr»` is the recursion seam.
- C2: `ensureAtomicBinderName` (`Binders.lean:188-191`) in `push_binder_group` (`elabBinderViews`, `:213`), `fun` (`elabFunBinderViews`, `:426`) and the `let` telescope's bare-ident arm; `ElabError::InvalidBinderName`.
- C3: the `auxLemmasExt` seam above (`CommandElab::aux_admitted`).
- I4: `elab_decl` labels any unlabelled term/binder seam ` — later M4` (`command::label_seam`).
- M5/M6: `push_binder_group`'s doc restored; `_root_x` is admitted (only `_root_` or a `_root_.` prefix seams).
- `letToHave` seam CLOSED (letToHaveType/Value ported, PR "port Meta.letToHave"): see docs/superpowers/specs/2026-10-07-let-to-have-design.md § Landed.
