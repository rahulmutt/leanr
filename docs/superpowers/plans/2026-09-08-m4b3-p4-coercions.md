# M4b-3 P4 — coercions: implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Port the oracle's coercion machinery — `Lean/Meta/Coe.lean`
(`expandCoe`, `coerceSimple?`, `coerceToFunction?`, `coerceToSort?`,
`coerce?`), the `Meta.transform` traversal it runs on, `mkCoe` and the
`.coe` synthetic-mvar arm of the ladder, and `ensureType` — into
`leanr_meta` and `leanr_elab`, decode the `Lean.Meta.coeDeclAttr` tag
extension in `leanr_olean`, and land the verbatim `Init/Coe.lean` class
chain in both fixture tiers — every step differentially verified
against the pinned oracle.

**Architecture:** Two new `leanr_meta` modules mirror the oracle 1:1
(`transform.rs` ↔ `Meta/Transform.lean`, `coe.rs` ↔ `Meta/Coe.lean`),
fed by one new decoded extension and by `try_synth_instance`, which
moves DOWN from `leanr_elab`'s ladder into `leanr_meta` because the
oracle's `trySynthInstance` is Meta-level. `leanr_elab` gains
`mk_coe` / `ensure_has_type` / `ensure_type` in a new `coe.rs` and
rewires its six mismatch sites through them; the ladder's `Coe` arm and
the reporter's `Coe` seam become real code. The synthesis tier is
proved FIRST (Task 1: the chain in `Synth0.lean`, records pinning the
full instance term), then the elaborator tier lands its fixture chain
with no new records (Task 6, a pure regression gate) and finally its
records, one mechanism at a time (Tasks 7–9), so no commit leaves either
corpus red.

**Tech Stack:** Rust (workspace crates `leanr_olean`, `leanr_meta`,
`leanr_elab`), Lean 4 fixtures (`prelude`-mode, import-free), `mise`
task runner, `serde_json` for the differential corpora.

**Spec:** `docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md`
— § P4 (the shape) and § Amendment 5 (the reasoning; items are cited
below as "A5 item N"). Executors read both.

## Global Constraints

Copied from the spec (§ Global constraints, § Amendment 5) and
`AGENTS.md`. Every task's requirements implicitly include this section.

- **Pinned oracle: `leanprover/lean4:v4.33.0-rc1`** (`lean-toolchain`).
  Every citation in this plan is against that toolchain's sources, found
  locally at
  `/home/dev/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/`.
  **Never bump the pin.**
- **Kernel is byte-untouched.** `leanr_kernel` depends on no workspace
  crate and no existing kernel function is modified.
- **`leanr_meta` changes are ADDITIVE ONLY** (A5 item 12): two new
  modules, `try_synth_instance` + `LOption` moved in from `ladder.rs`,
  `with_transparency`, `whnf_r`, `mk_arrow`, one `MetaError` variant,
  one `EnvExtensions` field. No existing `leanr_meta` path changes
  behaviour. `unfold_definition`, `get_level`, `head_beta`, `beta_rev`
  stay `pub(crate)`.
- **`leanr_olean` gains one additive decoder** (`Lean.Meta.coeDeclAttr`,
  A5 item 2). It is an untrusted-input parser: it must never panic on
  arbitrary bytes (`docs/THREAT_MODEL.md`). No existing decode path
  changes.
- **Named seams, never silent divergence.** Where the oracle does
  something this plan does not implement, detect the shape and return
  `ElabError::UnsupportedSyntax(..)` naming the seam and its owner. Where
  this plan RETIRES a seam, delete its message entirely and gate that it
  never comes back (`tests/seam_audit.rs`'s retired-label pattern).
- **Correctness is byte-for-byte agreement with the pinned oracle**, via
  the committed corpora `tests/fixtures/elab/elab-queries.jsonl` (107
  records today) and `tests/fixtures/meta/synth-queries.jsonl` (20
  records today, 18 compared). Never re-baseline a record to make a
  test pass: a record that moves means the code is wrong. **All 107
  elab records and all 20 synth records must stay byte-identical
  through every task** (A5 item 11).
- **Every discriminator is a claim until measured** (A5 item 10,
  § Amendment 4 item 11). Each task that adds a record or a test names
  the mutation it is supposed to kill and includes the step that applies
  the mutation and watches the test go red. A record that survives its
  mutation is replaced, not shipped.
- **`mise run ci` gates `cargo fmt --check` and clippy**, not only tests.
  Run it before every commit; the test tasks alone do not cover it.
- **Fixture regeneration:** `mise run fixtures:regen` rebuilds every
  `.olean` (`Instances.olean`, `Synth0.olean`, `Elab0.olean`, …), re-runs
  `dump_synth.lean` into `synth-queries.jsonl`, and then via
  `depends_post` runs `fixtures:regen-elab` (`dump_elab.lean` into
  `elab-queries.jsonl`). When only `dump_elab.lean`'s query lists changed
  and `Elab0.lean` did not, `mise run fixtures:regen-elab` alone suffices.
  Both need the pinned Lean toolchain on `PATH` (`mise run
  elan:bootstrap`). **A query whose oracle-side elaboration THROWS is
  printed to stderr and DROPPED** by both dumpers — after every regen,
  read stderr for `elaboration failed for <id>` / `"exc"` records.
- **Determinism:** no wall-clock, no `maxHeartbeats`; leanr counts
  deterministic `MetaCtx::step`s.
- **Commit messages** end with the session trailer this session was
  given: `Claude-Session: https://claude.ai/code/session_01P6daLFfQsqbKWFUWVvJqZs`.

## File Structure

**Created:**
- `crates/leanr_meta/src/transform.rs` — `TransformStep` and
  `MetaCtx::transform` (`Meta/Transform.lean:13-26`, `:97-187`), Task 4.
- `crates/leanr_meta/src/coe.rs` — `expand_coe`, `coerce_simple`,
  `coerce_to_function`, `coerce_to_sort`, `is_type_app`, the monad-lift
  guard, `coerce` (`Meta/Coe.lean`), Task 5.
- `crates/leanr_elab/src/coe.rs` — `mk_coe`, `ensure_has_type`,
  `ensure_type`, `synthesize_coe_mvar` (`TermElabM.lean:1294-1340`,
  `:1935-1949`, `SyntheticMVars.lean:545-560`), Tasks 7 and 9.

**Modified:**
- `tests/fixtures/meta/Synth0.lean`, `tests/fixtures/meta/dump_synth.lean`,
  `tests/fixtures/meta/Synth0.olean`, `tests/fixtures/meta/synth-queries.jsonl`
  — the chain and six synthesis records (Task 1).
- `tests/fixtures/Instances.lean`, `tests/fixtures/Instances.olean` — an
  existence-only `Monad` axiom for the guard's unit test (Task 5).
- `tests/fixtures/elab/Elab0.lean`, `tests/fixtures/elab/Elab0.olean` —
  the chain, `Int`, `Big`, `Wrapper`, `Fn`, `Carrier` and their instances
  (Task 6); `tests/fixtures/elab/dump_elab.lean`,
  `tests/fixtures/elab/elab-queries.jsonl` — `coeQueries` (Tasks 7–9).
- `crates/leanr_olean/src/interp_id.rs`, `crates/leanr_olean/src/module_data.rs`
  — the `coeDeclAttr` arm, the `coe_decls` field, its decode test (Task 2).
- `crates/leanr_meta/src/metactx.rs` — `EnvExtensions::coe_decls`, the
  `coe_decls` set, `is_coe_decl`, `with_transparency` (Tasks 2, 4);
  `src/lib.rs` — module and re-export lines (Tasks 3–5); `src/error.rs`
  — `CoeExpansionMismatch` (Task 4); `src/synth.rs` — `LOption`,
  `try_synth_instance`, `has_mvar_outside_out_params` (Task 3);
  `src/whnf.rs` — `whnf_r` (Task 4); `src/test_support.rs` —
  `with_synth0_ctx` (Task 5).
- Every `EnvExtensions { .. }` construction site (Task 2 lists all 18)
  and both `Replayed` structs (`crates/leanr_meta/tests/support/mod.rs`,
  `crates/leanr_elab/tests/support/mod.rs`), plus `synth_sweep.rs`'s
  closure loader.
- `crates/leanr_elab/src/synthetic/ladder.rs` — `LOptionExpr` and the
  pre-test deleted in favour of `leanr_meta::LOption` /
  `MetaCtx::try_synth_instance` (Task 3); the `Coe` arm (Task 7).
- `crates/leanr_elab/src/synthetic/report.rs` — `StuckCoercion` (Task 7).
- `crates/leanr_elab/src/error.rs` — `StuckCoercion`, `TypeExpected`
  (Tasks 7, 9).
- `crates/leanr_elab/src/elab.rs` — `elab_term_ensuring_type` rewired
  (Task 7); `src/builtin/ascription.rs` — the `($e :)` arm (Task 7);
  `src/app/args.rs` — `elab_and_add_new_arg` (Task 7),
  `synthesize_pending_and_normalize_fun_type` (Task 8);
  `src/builtin/binder.rs` — `elab_type` (Task 9); `src/lib.rs`,
  `src/app/mod.rs`, `src/dispatch.rs` — ledger reconciliation (Task 10).
- `crates/leanr_elab/tests/oracle_elab.rs` — `CORPUS_FLOOR` (Tasks 7–9);
  `tests/seam_audit.rs` — retired-label gate, updated seam tests
  (Tasks 8, 10); `tests/synthetic_smoke.rs`, `tests/app_smoke.rs` — arm
  and rewire tests (Tasks 7–9).
- `crates/leanr_meta/tests/oracle_synth.rs` — the compared-count
  constant (Task 1).

## Orientation for the implementer

Read these before Task 1. They are short and they are what the code below
mirrors.

- **The oracle:** `Meta/Coe.lean:21-29` (`coeDeclAttr`, `isCoeDecl`),
  `:44-70` (`expandCoe`), `:78-98` (`coerceSimpleRecordingNames?`,
  `coerceSimple?`), `:100-126` (`coerceToFunction?`, `coerceToSort?`),
  `:128-132` (`isTypeApp?`), `:201-257` (`coerceMonadLift?` — the guard's
  shape, A5 item 6), `:259-278` (`coerceCollectingNames?`, `coerce?`);
  `Meta/Transform.lean:13-26` (`TransformStep`), `:97-176`
  (`transformWithCache`), `:179-187` (`Meta.transform`);
  `Meta/SynthInstance.lean:1014-1017` (`trySynthInstance`);
  `Meta/WHNF.lean:793-818` (`unfoldProjInst?`, the reduction `expandCoe`
  actually performs on a class projection, A5 item 5);
  `Elab/Term/TermElabM.lean:1294-1322` (`mkCoe`), `:1334-1340`
  (`ensureHasType`), `:1935-1949` (`ensureType`);
  `Elab/SyntheticMVars.lean:545-560` (the `.coe` ladder arm), `:304-310`
  (the `.coe` reporter arm); `Elab/App.lean:54-62` (`ensureArgType`),
  `:378-380` (`coerceToFunction?` in `synthesizePendingAndNormalizeFunType`);
  `Lean/Attributes.lean:180-201` (`registerTagAttribute` — why the
  extension is named `Lean.Meta.coeDeclAttr`).
- **leanr's counterparts today:** `crates/leanr_elab/src/synthetic/ladder.rs:42-46`
  (`LOptionExpr`), `:171-180` (`try_synth_instance`), `:207-237`
  (`has_mvar_outside_out_params`), `:322-324` (the `Coe` arm seam);
  `synthetic/report.rs:97-99` (the reporter seam); `elab.rs:293-307`
  (`elab_term_ensuring_type`); `builtin/ascription.rs:141-149`;
  `app/args.rs:104-134` and `:863-885`; `builtin/binder.rs:24-36`;
  `crates/leanr_meta/src/whnf.rs:2594-2680` (`unfold_definition`,
  `unfold_definition_app`) and `:2441-2540` (`unfold_proj_inst_when_instances`,
  `unfold_proj_inst`); `assign.rs:695-714` (`mk_aux_mvar`, the meta-tier
  mvar minter `coe.rs` reuses); `level.rs:718-730` (`fresh_level_mvar`);
  `metactx.rs:257-268` (`EnvExtensions`); `crates/leanr_olean/src/interp_id.rs:955-1080`
  (the extension-name `match`).
- **The spec:** § P4 and § Amendment 5. Items 3 (why `try_synth_instance`
  moves), 5 (why `expand_coe` needs no `whnf.rs` change), 6 (the guard),
  9–10 (fixtures and discriminators) are the ones the tasks below cite
  most.
- **How the corpora are made:** `dump_synth.lean`'s `synthQueries` is a
  `List (Name × Nat × MetaM Expr)` and each record pins verdict, the
  instance TERM and post-synthesis `assigns`; `dump_elab.lean`'s query
  lists are `List (String × String)` of `(id, source)` concatenated in
  `main`. Both drop a throwing query with a stderr line.

**One mechanism to hold in mind throughout — what `expandCoe` actually
does.** `CoeT.coe` and its eleven siblings are class projections, which
the oracle deliberately keeps NON-reducible (`WHNF.lean:810-811`). So
`unfoldDefinition?` under `.instances` does not delta them; its
`matchConstAux` failure continuation runs `unfoldProjInst?`, which
delta-betas the projection at default transparency and then reduces the
resulting `inst.1` against the instance's constructor under
`.instances`. `CoeT.coe Nat n Int inst` therefore becomes
`CoeHTCT.coe Nat Int inst' n`, which `.visit` feeds back into `pre`, and
so on down the chain until `Coe.coe Nat Int instCoeNatInt n` becomes
`Int.ofNat n`. leanr's `unfold_definition_app` already routes both
failure sub-conditions to `unfold_proj_inst` (M4a plan 4 task B6), so
`expand_coe` is `transform` + `unfold_definition` + `head_beta` under a
scoped `Instances` transparency and nothing else (A5 item 5). If a
coercion record emits a `CoeT.coe` or `.proj` node, the transparency
scope is wrong, not `whnf.rs`.

---

### Task 1: the coercion chain at the synthesis tier

`Synth0.lean` gains `semiOutParam`, the verbatim `Init/Coe.lean:131-287`
chain, a two-step `Coe` chain, a `CoeFun` carrier and a `CoeSort`
carrier; `dump_synth.lean` gains six queries pinning the FULL instance
term the tabled resolver picks through the diamond (A5 item 9). This is
the P2b-i precedent: prove the shape one tier down before the
elaborator depends on it. No Rust code changes except the gate's
compared-count constant.

**Files:**
- Modify: `tests/fixtures/meta/Synth0.lean` (append after `def Dual`, `:227`)
- Modify: `tests/fixtures/meta/dump_synth.lean` (`synthQueries`, `:278-303`, and the doc block above it)
- Modify: `crates/leanr_meta/tests/oracle_synth.rs:363-369` (`compared, 18` → `24`)
- Regenerated: `tests/fixtures/meta/Synth0.olean`, `tests/fixtures/meta/synth-queries.jsonl`, and every other artifact `fixtures:regen` rewrites (all byte-identical except these two)

**Interfaces:**
- Consumes: nothing new.
- Produces: fixture constants `semiOutParam`, `Coe`…`CoeSort` (twelve classes, seventeen instances, twelve `coe_decl` tags), `M`, `Big`, `instCoeNM`, `instCoeMBig`, `FnN`, `instCoeFunFnN`, `SortN`, `instCoeSortSortN`; records `coeChain/synth/0..3`, `coeFun/synth/0`, `coeSort/synth/0`. Task 2's decoder test reads the twelve tagged names from `Synth0.olean`; Task 5's unit tests run over this environment.

- [ ] **Step 1: Append the fixture block to `tests/fixtures/meta/Synth0.lean`**

After `def Dual (a : Type) : Type := a` (`:227`), append:

```lean
-- === M4b-3 P4: the coercion class chain (design spec § P4, § Amendment 5 item 9) ===
--
-- `semiOutParam` at the ROOT namespace, verbatim from
-- `Init/Prelude.lean:725`, for the same reason `outParam` above is:
-- `Coe`'s first parameter is `semiOutParam (Sort u)`, and only the root
-- name is the real gadget. For synthesis it is inert apart from being
-- reducible (it is consulted only by `computeSynthOrder`, whose result
-- is already serialized into `InstanceEntry.synthOrder` and read by
-- `leanr_meta::instances`).
@[reducible] def semiOutParam (α : Sort u) : Sort u := α

-- The chain, VERBATIM from `Init/Coe.lean:131-287` of the pin with the
-- doc comments dropped and nothing else changed: twelve classes,
-- seventeen instances (anonymous, so Lean auto-names them exactly as
-- it does in Init), twelve `attribute [coe_decl]` lines. A stand-in
-- chain was rejected (§ Amendment 5 item 9): the diamond of reflexive
-- (`CoeTC α α`) and transitive (`[Coe β γ] [CoeTC α β] : CoeTC α γ`)
-- instances is exactly what the Mathlib synthesis nightly hits, and the
-- resolver's path through it is observable ONLY at this tier — the
-- elaborator tier unfolds the instance away (`expandCoe`).
class Coe (α : semiOutParam (Sort u)) (β : Sort v) where
  coe : α → β
attribute [coe_decl] Coe.coe

class CoeTC (α : Sort u) (β : Sort v) where
  coe : α → β
attribute [coe_decl] CoeTC.coe
instance [Coe β γ] [CoeTC α β] : CoeTC α γ where coe a := Coe.coe (CoeTC.coe a : β)
instance [Coe α β] : CoeTC α β where coe a := Coe.coe a
instance : CoeTC α α where coe a := a

class CoeOut (α : Sort u) (β : semiOutParam (Sort v)) where
  coe : α → β
attribute [coe_decl] CoeOut.coe

class CoeOTC (α : Sort u) (β : Sort v) where
  coe : α → β
attribute [coe_decl] CoeOTC.coe
instance [CoeOut α β] [CoeOTC β γ] : CoeOTC α γ where coe a := CoeOTC.coe (CoeOut.coe a : β)
instance [CoeTC α β] : CoeOTC α β where coe a := CoeTC.coe a
instance : CoeOTC α α where coe a := a

class CoeHead (α : Sort u) (β : semiOutParam (Sort v)) where
  coe : α → β
attribute [coe_decl] CoeHead.coe

class CoeHTC (α : Sort u) (β : Sort v) where
  coe : α → β
attribute [coe_decl] CoeHTC.coe
instance [CoeHead α β] [CoeOTC β γ] : CoeHTC α γ where coe a := CoeOTC.coe (CoeHead.coe a : β)
instance [CoeOTC α β] : CoeHTC α β where coe a := CoeOTC.coe a
instance : CoeHTC α α where coe a := a

class CoeTail (α : semiOutParam (Sort u)) (β : Sort v) where
  coe : α → β
attribute [coe_decl] CoeTail.coe

class CoeHTCT (α : Sort u) (β : Sort v) where
  coe : α → β
attribute [coe_decl] CoeHTCT.coe
instance [CoeTail β γ] [CoeHTC α β] : CoeHTCT α γ where coe a := CoeTail.coe (CoeHTC.coe a : β)
instance [CoeHTC α β] : CoeHTCT α β where coe a := CoeHTC.coe a
instance : CoeHTCT α α where coe a := a

class CoeDep (α : Sort u) (_ : α) (β : Sort v) where
  coe : β
attribute [coe_decl] CoeDep.coe

class CoeT (α : Sort u) (_ : α) (β : Sort v) where
  coe : β
attribute [coe_decl] CoeT.coe
instance [CoeHTCT α β] : CoeT α a β where coe := CoeHTCT.coe a
instance [CoeDep α a β] : CoeT α a β where coe := CoeDep.coe a
instance : CoeT α a α where coe := a

class CoeFun (α : Sort u) (γ : outParam (α → Sort v)) where
  coe : (f : α) → γ f
attribute [coe_decl] CoeFun.coe
instance [CoeFun α fun _ => β] : CoeOut α β where coe a := CoeFun.coe a

class CoeSort (α : Sort u) (β : outParam (Sort v)) where
  coe : α → β
attribute [coe_decl] CoeSort.coe
instance [CoeSort α β] : CoeOut α β where coe a := CoeSort.coe a

-- A two-step chain `N → M → Big` through two plain `Coe` instances.
-- `CoeT N n Big` is solvable ONLY through `CoeTC`'s transitive
-- instance (`[Coe β γ] [CoeTC α β] : CoeTC α γ`, with `β := M` found
-- by the search), so its recorded instance term is the discriminator
-- for the resolver's candidate order through the diamond (§ Amendment 5
-- item 10). `M` and `Big` are new opaque carriers; the requirement is
-- the chain, not the names.
inductive M where
  | ofN : N → M

inductive Big where
  | ofM : M → Big

instance instCoeNM : Coe N M := ⟨M.ofN⟩
instance instCoeMBig : Coe M Big := ⟨Big.ofM⟩

-- `CoeFun` / `CoeSort` carriers, for the two outParam-bearing classes:
-- the goal's last argument is an mvar the search ASSIGNS (P2b-i's
-- `assignOutParams`), observable in the record's `assigns`.
structure FnN where
  f : N → N

instance instCoeFunFnN : CoeFun FnN (fun _ => N → N) := ⟨FnN.f⟩

structure SortN where
  ty : Type

instance instCoeSortSortN : CoeSort SortN Type := ⟨SortN.ty⟩
```

- [ ] **Step 2: Add the six queries to `tests/fixtures/meta/dump_synth.lean`**

In the doc block above `synthQueries` (the bullet list ending with the
`stuck` bullet at `:274-277`), add:

```
* `coeChain/0..3` — the `CoeT` chain (M4b-3 P4, § Amendment 5 item 9).
                  `/0`: `CoeT N N.zero M`, one `Coe` step;
                  `/1`: `CoeT N N.zero Big`, TWO steps — solvable only
                  through `CoeTC`'s transitive instance, so the
                  recorded instance term pins the resolver's path
                  through the reflexive/transitive diamond; `/2`:
                  `CoeT N N.zero N`, the reflexive instance (declared
                  LAST, hence tried FIRST); `/3`: `CoeT N N.zero
                  NoBase`, `.none` — the whole diamond is explored and
                  the search must TERMINATE on it.
* `coeFun/0`, `coeSort/0` — `CoeFun FnN ?γ` (`?γ : FnN → Type`) and
                  `CoeSort SortN ?β` (`?β : Type`): each class's last
                  parameter is an `outParam`, so the goal mvar is
                  ASSIGNED by the search and shows up in `assigns`.
```

Then, in `synthQueries`, append after the `stuck` entry (keep it last-but-
these; ordering only affects record order in the file):

```lean
  , (`coeChain, 0, pure (mkApp3 (mkConst `CoeT [levelOne, levelOne]) nTy (mkConst `N.zero) (mkConst `M)))
  , (`coeChain, 1, pure (mkApp3 (mkConst `CoeT [levelOne, levelOne]) nTy (mkConst `N.zero) (mkConst `Big)))
  , (`coeChain, 2, pure (mkApp3 (mkConst `CoeT [levelOne, levelOne]) nTy (mkConst `N.zero) nTy))
  , (`coeChain, 3, pure (mkApp3 (mkConst `CoeT [levelOne, levelOne]) nTy (mkConst `N.zero) (mkConst `NoBase)))
  , (`coeFun,   0, do
      let γ ← mkFreshExprMVar (mkForall `f BinderInfo.default (mkConst `FnN) (mkSort levelOne))
      pure (mkApp2 (mkConst `CoeFun [levelOne, levelOne]) (mkConst `FnN) γ))
  , (`coeSort,  0, do
      pure (mkApp2 (mkConst `CoeSort [levelOne, levelOne]) (mkConst `SortN) (← mkFreshExprMVar (mkSort levelOne))))
```

`nTy` is the file's existing `mkConst `N` helper; `levelOne` is
`Lean.levelOne`. `N : Type`, so every `Sort u`/`Sort v` here is
`Type = Sort 1`. If `mkForall`'s argument order does not compile against
the pin, use `Lean.mkForall `f BinderInfo.default (mkConst `FnN) (mkSort levelOne)`
— the pinned `Expr.lean` exports it as `mkForall (n : Name) (bi : BinderInfo) (t b : Expr)`.

- [ ] **Step 3: Regenerate and read the dumper's stderr**

```bash
mise run fixtures:regen 2>&1 | tee /tmp/claude-1000/-workspace/dac4073b-f7e4-4765-a43e-af6f8b0b6a69/scratchpad/regen-task1.log
grep -n 'exc\|failed\|error' /tmp/claude-1000/-workspace/dac4073b-f7e4-4765-a43e-af6f8b0b6a69/scratchpad/regen-task1.log
git status --short
```

Expected: `Synth0.lean` compiles (an auto-bound universe error on `γ`
means `autoImplicit` is off in this invocation — it is on by default
for a bare `lean` call, as `Instances.lean`'s own `Op`/`Lvl` rely on);
`synth-queries.jsonl` gains six records and no new `"exc"` record;
`git status` shows ONLY `Synth0.lean`, `Synth0.olean`, `dump_synth.lean`,
`synth-queries.jsonl` modified. Any other artifact moving means the
regen environment drifted — stop and report rather than committing it.

Verify the counts and the verdicts:

```bash
grep -c '' tests/fixtures/meta/synth-queries.jsonl                       # 26
grep -o '"id":"coe[^"]*","[^}]*"ok":[a-z]*' tests/fixtures/meta/synth-queries.jsonl
```

Expected: `coeChain/synth/0..2`, `coeFun/synth/0`, `coeSort/synth/0` are
`"ok":true`; `coeChain/synth/3` is `"ok":false`. Confirm `coeChain/synth/1`'s
`val` mentions BOTH `instCoeNM` and `instCoeMBig` (the two-step path) and
that `coeFun/synth/0` and `coeSort/synth/0` each carry a non-empty
`assigns`. Also check every new record has `"near_budget":false`.

- [ ] **Step 4: Run the synthesis gate to verify the count assertion fails**

```bash
cargo test -p leanr_meta --test oracle_synth
```

Expected: the six new records are COMPARED and agree (the resolver
already handles the diamond — this is P2a/P2b-i machinery), then the
final assertion fails with `expected 18 compared synthesis records` vs
24. **If any new record DISAGREES**, that is a real resolver divergence:
do not add it to `SEAM_EXCLUSIONS` (an entry is allowed only for a seam
already documented in the engine) — stop, record the exact diff in the
task report, and escalate; the spec's § Amendment 5 item 9 makes the
synthesis-tier agreement a precondition for Tasks 5–9.

- [ ] **Step 5: Raise the compared count**

In `crates/leanr_meta/tests/oracle_synth.rs:363-369`, change `compared, 18`
to `compared, 24` and the message's `expected 18` to `expected 24`, and
add to the message's trailing explanation: `M4b-3 P4 task 1 added the six
coe* records`.

- [ ] **Step 6: Run the gate and the whole meta tier**

```bash
cargo test -p leanr_meta --test oracle_synth
mise run meta:fast
```

Expected: PASS; `oracle_fast` untouched (its corpus did not change).

- [ ] **Step 7: Commit**

```bash
mise run ci
git add tests/fixtures/meta/Synth0.lean tests/fixtures/meta/Synth0.olean tests/fixtures/meta/dump_synth.lean tests/fixtures/meta/synth-queries.jsonl crates/leanr_meta/tests/oracle_synth.rs
git commit -F - <<'MSG'
M4b-3 P4 task 1: the coercion class chain at the synthesis tier

Synth0.lean gains semiOutParam and the verbatim Init/Coe.lean:131-287
chain plus a two-step Coe chain (N -> M -> Big) and CoeFun/CoeSort
carriers; dump_synth.lean gains six records pinning the FULL instance
term through the reflexive/transitive diamond, a .none goal, and the
two outParam classes' assigns. The 20 committed records are
byte-identical; compared count 18 -> 24.

Claude-Session: https://claude.ai/code/session_01P6daLFfQsqbKWFUWVvJqZs
MSG
```

---

### Task 2: decode `Lean.Meta.coeDeclAttr` and thread it to `MetaCtx`

The tag attribute's extension is named after its `builtin_initialize`d
constant (`registerTagAttribute`'s `ref := decl_name%`,
`Attributes.lean:181,185`), and its exported entries are a bare sorted
`Array Name` (`:189-193`) — A5 item 2. Empty extensions are not exported
(`Environment.lean:1855`), so the decoder's absent-means-empty default is
already right; only a present entry needs an arm.

**Files:**
- Modify: `crates/leanr_olean/src/interp_id.rs:963` (locals), `:1069-1074` (add the arm before `_ => continue`), `:1085-1103` (the `ModuleData` literal)
- Modify: `crates/leanr_olean/src/module_data.rs:396-398` (the field), `:826-880` (the test, after `class_extension_decodes_out_param_positions`)
- Modify: `crates/leanr_meta/src/metactx.rs:257-268` (`EnvExtensions`), the `MetaCtx` struct and `MetaCtx::new`, plus a new `is_coe_decl`
- Modify — every `EnvExtensions { .. }` literal that lists fields explicitly (the compiler flags each; the full list): `crates/leanr_elab/tests/oracle_elab.rs:90`, `crates/leanr_elab/tests/binder_smoke.rs:46`, `crates/leanr_elab/tests/support/mod.rs:74` and `:757`, `crates/leanr_meta/tests/oracle_synth.rs:162`, `:425`, `:518`, `crates/leanr_meta/tests/oracle_fast.rs:146`, `:297`, `:331`, `crates/leanr_meta/tests/synth_sweep.rs:362`, `crates/leanr_meta/src/test_support.rs:177`, `:225`, `:271`, `:484`, `crates/leanr_meta/src/whnf.rs:3063`, `:3569`; sites written with `..Default::default()` need nothing.
- Modify: `crates/leanr_meta/tests/support/mod.rs:47-55` and `:61-82` (`Replayed` + `replay_fixture_in`), `crates/leanr_elab/tests/support/mod.rs` (its own `Replayed` and every `let Replayed { .. } = replay_fixture_in(..)` destructuring), `crates/leanr_meta/tests/synth_sweep.rs:345-372` and `:598-612` (the closure loader's extend loop and the helper's parameter list)

**Interfaces:**
- Produces: `leanr_olean::ModuleData::coe_decls: Vec<NameId>`;
  `leanr_meta::EnvExtensions::coe_decls: &'a [NameId]`;
  `MetaCtx::is_coe_decl(&self, name: NameId) -> bool` (`pub`).

- [ ] **Step 1: Write the failing decode test**

Append inside `mod tests` of `crates/leanr_olean/src/module_data.rs`,
after `class_extension_decodes_out_param_positions`:

```rust
    /// `Lean.Meta.coeDeclAttr` decodes (M4b-3 P4 task 2). The extension
    /// is a `registerTagAttribute` (`Attributes.lean:180-201`): a bare,
    /// `Name.quickLt`-sorted `Array Name` of the tagged declarations,
    /// named after the `builtin_initialize`d constant (`ref :=
    /// decl_name%`), NOT after the attribute keyword `coe_decl`.
    /// `Synth0.lean` tags exactly the twelve `*.coe` projections of the
    /// verbatim `Init/Coe.lean` chain (M4b-3 P4 task 1); `Sample.olean`
    /// tags nothing, and an EMPTY extension is not exported at all
    /// (`Environment.lean:1855`, `filterNonEmpty`), so the absent case is
    /// asserted too rather than assumed.
    #[test]
    fn coe_decl_attribute_decodes_tagged_names() {
        let bytes = fixture("meta/Synth0.olean");
        let mut env = Environment::default();
        let md = ModuleData::parse(&bytes, env.store_mut()).expect("decode");
        let render = |n: NameId| env.store().to_name(None, Some(n)).to_string();
        let mut got: Vec<String> = md.coe_decls.iter().map(|n| render(*n)).collect();
        got.sort();
        let mut want: Vec<String> = [
            "Coe.coe", "CoeDep.coe", "CoeFun.coe", "CoeHTC.coe", "CoeHTCT.coe",
            "CoeHead.coe", "CoeOTC.coe", "CoeOut.coe", "CoeSort.coe", "CoeT.coe",
            "CoeTC.coe", "CoeTail.coe",
        ]
        .iter()
        .map(|s| s.to_string())
        .collect();
        want.sort();
        assert_eq!(got, want, "coeDeclAttr entries");

        let bytes = fixture("Sample.olean");
        let mut env = Environment::default();
        let md = ModuleData::parse(&bytes, env.store_mut()).expect("decode");
        assert!(md.coe_decls.is_empty(), "Sample.olean tags nothing");
    }
```

- [ ] **Step 2: Run it to verify it fails**

```bash
cargo test -p leanr_olean coe_decl_attribute_decodes_tagged_names
```

Expected: compile error, `no field coe_decls on type ModuleData`.

- [ ] **Step 3: Add the field and the arm**

In `crates/leanr_olean/src/module_data.rs`, after `pub classes: Vec<ClassEntry>,`:

```rust
    /// Typed decode of the `Lean.Meta.coeDeclAttr` entries (M4b-3 P4):
    /// the declarations tagged `@[coe_decl]`, which `expandCoe`
    /// (`Meta/Coe.lean:44-70`) unfolds. A `registerTagAttribute`
    /// extension (`Attributes.lean:180-201`), named after its
    /// `builtin_initialize`d constant, exporting a bare
    /// `Name.quickLt`-sorted `Array Name` (private declarations
    /// filtered out at the exported level, `:192`). Empty when the
    /// module tags nothing — an empty extension is not exported at all
    /// (`Environment.lean:1855`). All other extension entries stay
    /// opaque.
    pub coe_decls: Vec<NameId>,
```

In `crates/leanr_olean/src/interp_id.rs`, next to `let mut classes = Vec::new();`
(`:963`) add `let mut coe_decls = Vec::new();`; before the `_ => continue,`
arm (`:1074`) add:

```rust
                // TagAttribute (`registerTagAttribute`,
                // Attributes.lean:180-201): entries are a bare `Array
                // Name`, no scoped wrapper and no ctor around each name
                // — the same posture as `Lean.classExtension` above
                // minus the `ClassEntry` ctor. Named after the
                // `builtin_initialize`d constant (`ref := decl_name%`,
                // `:181`), which is why the key is `coeDeclAttr` and
                // not the attribute keyword `coe_decl`; confirmed by
                // string-probing the toolchain's `Init/Coe.olean`
                // (design spec § Amendment 5 item 2).
                "Lean.Meta.coeDeclAttr" => {
                    for e in array(&pf[1])? {
                        coe_decls.push(self.name_req(e)?);
                    }
                }
```

and add `coe_decls,` to the `Ok(crate::ModuleData { .. })` literal after
`classes,`.

- [ ] **Step 4: Run the decode test to verify it passes**

```bash
cargo test -p leanr_olean coe_decl_attribute_decodes_tagged_names
```

Expected: PASS.

- [ ] **Step 5: Write the failing `MetaCtx` test**

Append inside the `#[cfg(test)] mod tests` of `crates/leanr_meta/src/metactx.rs`:

```rust
    /// `is_coe_decl` reads the `Lean.Meta.coeDeclAttr` name set (M4b-3
    /// P4 task 2), the gate `expand_coe` consults per head
    /// (`Meta/Coe.lean:28-29`, `isCoeDecl`). Over `Synth0.olean`:
    /// `CoeT.coe` is tagged, `CoeT` (the class) and `Add.add` are not.
    #[test]
    fn is_coe_decl_reads_the_tag_set() {
        use crate::test_support::with_synth0_ctx;
        with_synth0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let mut name = |parts: &[&str]| {
                let mut id = None;
                for p in parts {
                    let s = ctx.scratch.intern_str(base, p).expect("intern");
                    id = Some(ctx.scratch.name_str(base, id, s).expect("name"));
                }
                id.expect("non-empty")
            };
            let coe_t_coe = name(&["CoeT", "coe"]);
            let coe_t = name(&["CoeT"]);
            let add_add = name(&["Add", "add"]);
            assert!(ctx.is_coe_decl(coe_t_coe));
            assert!(!ctx.is_coe_decl(coe_t));
            assert!(!ctx.is_coe_decl(add_add));
        });
    }
```

`with_synth0_ctx` does not exist yet — add it to
`crates/leanr_meta/src/test_support.rs` now, as a copy of
`with_instances_ctx` (`:199-234`) reading `fixture_path("meta/Synth0.olean")`
with the `expect` messages renamed, and with `coe_decls: &coe_decls`
added to its `EnvExtensions` literal (`let coe_decls = md.coe_decls;`).
Do the same to `with_instances_ctx`, `with_prelude0_ctx` and every other
`EnvExtensions` literal in that file. Task 5's unit tests reuse this
helper.

- [ ] **Step 6: Run it to verify it fails**

```bash
cargo test -p leanr_meta is_coe_decl_reads_the_tag_set
```

Expected: compile error, `no field coe_decls` / `no method is_coe_decl`.

- [ ] **Step 7: Thread the field**

In `crates/leanr_meta/src/metactx.rs`:

```rust
// in `pub struct EnvExtensions<'a>`, after `classes`:
    /// Decoded `Lean.Meta.coeDeclAttr` entries (M4b-3 P4 task 2) — the
    /// `@[coe_decl]` name set `MetaCtx::is_coe_decl` answers from.
    pub coe_decls: &'a [NameId],

// in `pub struct MetaCtx<'e>`, after the `classes: ClassTable` field:
    /// The `@[coe_decl]` name set (`Meta/Coe.lean:21-29`), built once
    /// from `EnvExtensions::coe_decls`. Read by `coe.rs::expand_coe`.
    pub(crate) coe_decls: HashSet<NameId>,

// in `MetaCtx::new`, next to `let classes = ClassTable::build(exts.classes);`:
        let coe_decls: HashSet<NameId> = exts.coe_decls.iter().copied().collect();
// ...and `coe_decls,` in the struct literal `new` returns.

// a new accessor beside `has_out_params` (`:863`):
    /// oracle: `isCoeDecl` (`Meta/Coe.lean:28-29`) — `coeDeclAttr.hasTag
    /// env declName`. `pub` because `leanr_elab`'s tests assert the gate
    /// directly; the production reader is `coe.rs::expand_coe`.
    pub fn is_coe_decl(&self, name: NameId) -> bool {
        self.coe_decls.contains(&name)
    }
```

Add `use std::collections::HashSet;` if the file lacks it. Then fix every
explicit `EnvExtensions { .. }` literal in the list under **Files** by
adding `coe_decls: &coe_decls,` (test files) or `coe_decls,` (where a
parameter of that name is in scope), with `coe_decls` sourced from the
`ModuleData` the site already decodes:

- both `Replayed` structs gain `pub coe_decls: Vec<NameId>`, filled from
  `md.coe_decls` in `replay_fixture_in`; every `let Replayed { .. } =`
  destructuring gains `coe_decls`;
- `synth_sweep.rs`'s closure loop (`:598-612`) gains
  `let mut coe_decls: Vec<NameId> = Vec::new();` and
  `coe_decls.extend(md.coe_decls);`, and the helper at `:345-372` gains a
  `coe_decls: &[NameId]` parameter threaded from `:748`;
- `whnf.rs:3063` and `:3569` are `#[cfg(test)]` literals over fixtures
  that tag nothing: `coe_decls: &[]`.

- [ ] **Step 8: Build the workspace and run the test**

```bash
cargo build --workspace --all-targets
cargo test -p leanr_meta is_coe_decl_reads_the_tag_set
```

Expected: no remaining `missing field coe_decls` errors; PASS.

- [ ] **Step 9: Run both hermetic gates**

```bash
mise run meta:fast
cargo test -p leanr_elab --test oracle_elab
```

Expected: PASS, 107 elab records and 24 compared synth records
byte-identical (this task changes no behaviour).

- [ ] **Step 10: Commit**

```bash
mise run ci
git add -A crates/leanr_olean crates/leanr_meta crates/leanr_elab
git commit -F - <<'MSG'
M4b-3 P4 task 2: decode Lean.Meta.coeDeclAttr, thread coe_decls to MetaCtx

The tag attribute's extension is named after its builtin_initialize'd
constant (registerTagAttribute's ref := decl_name%), exporting a bare
sorted Array Name; empty extensions are not exported, so absent-means-
empty was already right. ModuleData.coe_decls, EnvExtensions.coe_decls,
MetaCtx::is_coe_decl; every construction site threaded. No behaviour
change: both corpora byte-identical.

Claude-Session: https://claude.ai/code/session_01P6daLFfQsqbKWFUWVvJqZs
MSG
```

---
### Task 3: `LOption` and `try_synth_instance` move into `leanr_meta`

The oracle's `trySynthInstance` (`SynthInstance.lean:1014-1017`) is
Meta-level; `coe.rs` (Task 5) calls it three times. leanr's only
three-valued answer lives in `leanr_elab`'s ladder with the positional
stuck pre-test. Both move down VERBATIM (A5 item 3), the ladder calls the
moved function, and the private `LOptionExpr` is deleted. Behaviour is
unchanged, which the 107 elab records prove.

**Files:**
- Modify: `crates/leanr_meta/src/synth.rs` (append after `synth_instance`, `:1644-1646`)
- Modify: `crates/leanr_meta/src/lib.rs:35` (re-export)
- Modify: `crates/leanr_elab/src/synthetic/ladder.rs:32-46` (delete `LOptionExpr`), `:48-237` (delete `try_synth_instance` + `has_mvar_outside_out_params`, leave a pointer), `:370-373` (the caller)
- Test: `crates/leanr_meta/src/synth.rs` (`#[cfg(test)] mod tests`)

**Interfaces:**
- Produces: `pub enum LOption<T> { Some(T), None, Undef }` (re-exported as `leanr_meta::LOption`);
  `MetaCtx::try_synth_instance(&mut self, ty: ExprId) -> Result<LOption<ExprId>, MetaError>` (`pub`);
  `MetaCtx::has_mvar_outside_out_params(&self, ty: ExprId) -> bool` (`pub(crate)`).
- Consumed by: Task 5 (`coerce_simple`, `coerce_to_function`, `coerce_to_sort`) and the ladder.

- [ ] **Step 1: Write the failing test**

Append inside `synth.rs`'s `#[cfg(test)] mod tests`:

```rust
    /// `try_synth_instance` (M4b-3 P4 task 3) — the oracle's
    /// `trySynthInstance` (`SynthInstance.lean:1014-1017`) behind the
    /// positional stuck pre-test that moved here from
    /// `leanr_elab::synthetic::ladder` (design spec § Amendment 5 item
    /// 3). Four shapes over `Instances.olean`: a ground goal answers
    /// `Some`; an mvar in an OUTPUT-parameter position still reaches the
    /// real search and is assigned by it (`Op N N ?c`, P2b-i); an mvar in
    /// a NON-output position postpones (`Get N ?i ?e` — the `GetElem`
    /// worked example depends on this); a class with no instance answers
    /// `None`, not `Undef`.
    #[test]
    fn try_synth_instance_is_three_valued_and_positional() {
        use crate::synth::LOption;
        use crate::test_support::{const_named, with_instances_ctx};
        with_instances_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let one = ctx.scratch.level_succ(base, zero).expect("level");
            let type0 = ctx.scratch.expr_sort(base, one).expect("Type");
            let n = const_named(ctx, "N");
            let lv0 = ctx.scratch.intern_level_list(base, &[zero]).expect("levels");
            let lv000 = ctx.scratch.intern_level_list(base, &[zero, zero, zero]).expect("levels");
            let mut konst = |ctx: &mut MetaCtx, s: &str, ls| {
                let str_id = ctx.scratch.intern_str(base, s).expect("intern");
                let name = ctx.scratch.name_str(base, None, str_id).expect("name");
                ctx.scratch.expr_const(base, Some(name), ls).expect("const")
            };
            let mut app = |ctx: &mut MetaCtx, f: ExprId, args: &[ExprId]| {
                let mut r = f;
                for a in args {
                    r = ctx.scratch.expr_app(base, r, *a).expect("app");
                }
                r
            };

            // ground: `Add N`
            let add = konst(ctx, "Add", lv0);
            let goal = app(ctx, add, &[n]);
            assert!(matches!(ctx.try_synth_instance(goal).expect("ok"), LOption::Some(_)));

            // outParam position: `Op N N ?c` — Some, and `?c := N`
            let op = konst(ctx, "Op", lv0);
            let (c, c_id) = ctx.mk_aux_mvar(type0).expect("mvar");
            let goal = app(ctx, op, &[n, n, c]);
            assert!(matches!(ctx.try_synth_instance(goal).expect("ok"), LOption::Some(_)));
            assert!(ctx.mctx.is_assigned(c_id), "assignOutParams assigns the caller's mvar");

            // non-output position: `Get N ?i ?e` — Undef
            let get = konst(ctx, "Get", lv000);
            let (i, _) = ctx.mk_aux_mvar(type0).expect("mvar");
            let (e, _) = ctx.mk_aux_mvar(type0).expect("mvar");
            let goal = app(ctx, get, &[n, i, e]);
            assert!(matches!(ctx.try_synth_instance(goal).expect("ok"), LOption::Undef));

            // no instance at all: `NoInst N` — None
            let no_inst = konst(ctx, "NoInst", lv0);
            let goal = app(ctx, no_inst, &[n]);
            assert!(matches!(ctx.try_synth_instance(goal).expect("ok"), LOption::None));
        });
    }
```

- [ ] **Step 2: Run it to verify it fails**

```bash
cargo test -p leanr_meta try_synth_instance_is_three_valued_and_positional
```

Expected: compile error, `no method named try_synth_instance` / unresolved `LOption`.

- [ ] **Step 3: Add `LOption` and the two methods to `synth.rs`**

Directly after `pub fn synth_instance` (`:1644-1646`):

```rust
/// oracle: `Lean.LOption` as `trySynthInstance` returns it
/// (`SynthInstance.lean:1010-1017`) — `.some` is an answer, `.none` a
/// completed search with no answer, and `.undef` "instance cannot be
/// synthesized right now because `type` contains metavariables".
///
/// Three-valued, not `Option`: reporting `.undef` as `.none` turns every
/// postponable typeclass goal into a hard synthesis failure, and
/// reporting it as `.some` — which is what happens when nothing detects
/// the stuck condition at all — answers the goal by guessing a candidate
/// on the caller's behalf. Moved here from `leanr_elab`'s ladder in
/// M4b-3 P4 (design spec § Amendment 5 item 3) because the oracle's
/// `trySynthInstance` is Meta-level and `coe.rs` needs it.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LOption<T> {
    Some(T),
    None,
    Undef,
}

impl<'e> MetaCtx<'e> {
    /// oracle: `Lean.Meta.trySynthInstance` (`SynthInstance.lean:1014-1017`)
    /// — `synthInstance?` with `isDefEqStuckExceptionId` caught and
    /// reported as `.undef`.
    ///
    /// [MOVE the whole doc comment of `TermElabM::try_synth_instance`
    /// here VERBATIM — `crates/leanr_elab/src/synthetic/ladder.rs:48-170`
    /// before this task: "Why this is not just `synth_instance` with the
    /// error mapped", the three residues with their owners, the
    /// "Closed by M4b-3 P2b-ii" note, and the `IsDefEqStuck` arm's
    /// "should be reading once `leanr_meta` grows the depth model"
    /// end state. Amend its first line to say the function now lives
    /// where the depth model will.]
    ///
    /// `ty` is `instantiate_mvars`-ed here (the oracle's own
    /// `let type ← instantiateMVars type`, `:967`), so the pre-test's
    /// `has_expr_mvar` reads "mentions an UNASSIGNED expr mvar".
    pub fn try_synth_instance(&mut self, ty: ExprId) -> Result<LOption<ExprId>, MetaError> {
        let ty = self.instantiate_mvars(ty)?;
        if self.has_mvar_outside_out_params(ty) {
            return Ok(LOption::Undef);
        }
        match self.synth_instance(ty) {
            Ok(Some(val)) => Ok(LOption::Some(val)),
            Ok(None) => Ok(LOption::None),
            Err(MetaError::IsDefEqStuck(_)) => Ok(LOption::Undef),
            Err(e) => Err(e),
        }
    }

    /// The stuck pre-test, POSITIONAL since M4b-3 P2b-ii.
    ///
    /// [MOVE the doc comment of `TermElabM::has_mvar_outside_out_params`
    /// here VERBATIM — `ladder.rs:181-206` before this task.]
    pub(crate) fn has_mvar_outside_out_params(&self, ty: ExprId) -> bool {
        if !self.data(ty).has_expr_mvar() {
            return false;
        }
        let head = self.get_app_fn(ty);
        let args = self.get_app_args(ty);
        let Node::Const {
            name: Some(class), ..
        } = self.node(head)
        else {
            return true;
        };
        let Some(out_positions) = self.get_out_param_positions(class) else {
            return true;
        };
        args.iter()
            .enumerate()
            .any(|(i, arg)| !out_positions.contains(&i) && self.data(*arg).has_expr_mvar())
    }
}
```

The two bracketed MOVE instructions are literal: cut those doc blocks
out of `ladder.rs` and paste them here; do not paraphrase them. In
`crates/leanr_meta/src/lib.rs:35` extend the `metactx` re-export line's
neighbour: `pub use synth::LOption;`.

- [ ] **Step 4: Run the test to verify it passes**

```bash
cargo test -p leanr_meta try_synth_instance_is_three_valued_and_positional
```

Expected: PASS.

- [ ] **Step 5: Rewire the ladder**

In `crates/leanr_elab/src/synthetic/ladder.rs`:

- delete `enum LOptionExpr` and its doc (`:32-46`);
- delete `fn try_synth_instance` and `fn has_mvar_outside_out_params`
  with their docs (`:48-237`), leaving in their place:

```rust
    // `try_synth_instance` and its positional stuck pre-test moved to
    // `leanr_meta::MetaCtx::try_synth_instance` in M4b-3 P4 (design spec
    // § Amendment 5 item 3): the oracle's `trySynthInstance` is
    // Meta-level and `leanr_meta::coe` needs the same three-valued
    // answer. The residue documentation moved with it.
```

- at the caller (`:370-373` before the deletion) replace
  `self.try_synth_instance(ty)?` / `LOptionExpr::*` with
  `self.mctx.try_synth_instance(ty)?` / `leanr_meta::LOption::*` (add
  `use leanr_meta::LOption;` at the top).

- [ ] **Step 6: Run the elab tier**

```bash
cargo test -p leanr_elab
```

Expected: PASS — in particular `tests/synthetic_smoke.rs`'s
`non_out_param_position_mvar_still_postpones` and the three
`outParam/*` corpus records, which exercise the moved pre-test through
the ladder, and `oracle_elab` at 107 records byte-identical.

- [ ] **Step 7: Commit**

```bash
mise run ci
git add crates/leanr_meta/src/synth.rs crates/leanr_meta/src/lib.rs crates/leanr_elab/src/synthetic/ladder.rs
git commit -F - <<'MSG'
M4b-3 P4 task 3: try_synth_instance and LOption move into leanr_meta

SynthInstance.lean:1014-1017 behind the positional stuck pre-test,
moved verbatim from ladder.rs (docs and residues included); the ladder
now calls MetaCtx::try_synth_instance. Additive in leanr_meta, no
behaviour change: 107 elab records byte-identical.

Claude-Session: https://claude.ai/code/session_01P6daLFfQsqbKWFUWVvJqZs
MSG
```

---

### Task 4: `transform.rs`, `with_transparency`, `whnf_r`, `mk_arrow`, `CoeExpansionMismatch`

The traversal `expandCoe` runs on (`Meta/Transform.lean:97-187`, `pre`
only, default flags — A5 item 4) plus the three small helpers `coe.rs`
composes from and the one error variant its post-expansion checks raise
(A5 item 7).

**Files:**
- Create: `crates/leanr_meta/src/transform.rs`
- Modify: `crates/leanr_meta/src/lib.rs` (`mod transform;` + `pub use transform::TransformStep;`)
- Modify: `crates/leanr_meta/src/metactx.rs` (after `set_transparency`, `:401-403`: `with_transparency`, `mk_arrow`)
- Modify: `crates/leanr_meta/src/whnf.rs` (after `whnf_default`, `:1834-1840`: `whnf_r`)
- Modify: `crates/leanr_meta/src/error.rs` (`CoeExpansionMismatch`)
- Test: `crates/leanr_meta/src/transform.rs` (`#[cfg(test)]`), `crates/leanr_meta/src/metactx.rs` tests

**Interfaces:**
- Produces: `pub enum TransformStep { Done(ExprId), Visit(ExprId), Continue(Option<ExprId>) }`;
  `MetaCtx::transform(&mut self, input: ExprId, pre: &mut dyn FnMut(&mut MetaCtx<'e>, ExprId) -> Result<TransformStep, MetaError>) -> Result<ExprId, MetaError>` (`pub`);
  `MetaCtx::with_transparency<R>(&mut self, t: TransparencyMode, f: impl FnOnce(&mut Self) -> R) -> R` (`pub`);
  `MetaCtx::whnf_r(&mut self, e: ExprId) -> Result<ExprId, MetaError>` (`pub(crate)`);
  `MetaCtx::mk_arrow(&mut self, dom: ExprId, cod: ExprId) -> Result<ExprId, MetaError>` (`pub(crate)`);
  `MetaError::CoeExpansionMismatch(String)`.

- [ ] **Step 1: Write the failing `transform` tests**

Create `crates/leanr_meta/src/transform.rs` with ONLY the test module
for now (the implementation comes in Step 3):

```rust
//! oracle: `Lean/Meta/Transform.lean` (v4.33.0-rc1) — the generic
//! `pre`/`post` traversal, ported for `coe.rs::expand_coe` (M4b-3 P4).
//!
//! Scope (design spec § Amendment 5 item 4): `Meta.transform`
//! (`:179-187`) over `transformWithCache` (`:97-176`) with `post` fixed at
//! its default (`fun e => .done e`) and every flag at its default
//! (`usedLetOnly := false`, `skipConstInApp := false`; `transform` does
//! not expose `skipInstances`). `betaReduce`, `zetaReduce`,
//! `unfoldDeclsFrom` and the rest of that file have no consumer in M4b-3
//! and are not ported. The cache (`checkCache` on `ExprStructEq`,
//! `:110`) is a map keyed on `ExprId`, which hash-consing makes
//! structural for free.

#[cfg(test)]
mod tests {
    use super::TransformStep;
    use crate::test_support::{const_dotted, render_expr, with_synth0_ctx};
    use crate::MetaCtx;
    use leanr_kernel::bank::ExprId;
    use leanr_kernel::BinderInfo;

    fn app(ctx: &mut MetaCtx, f: ExprId, a: ExprId) -> ExprId {
        ctx.scratch
            .expr_app(Some(ctx.view.store), f, a)
            .expect("app")
    }

    /// `pre` that never rewrites returns the SAME hash-consed id, binder
    /// telescopes included — `fun (x : N) => N.succ x` is opened with a
    /// real fvar, re-abstracted, and comes back identical.
    #[test]
    fn transform_is_the_identity_when_pre_continues() {
        with_synth0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let n = const_dotted(ctx, "N", "zero");
            let n_ty = ctx.infer_type(n).expect("N");
            let succ = const_dotted(ctx, "N", "succ");
            let bvar0 = ctx.scratch.expr_bvar(base, 0).expect("bvar");
            let body = app(ctx, succ, bvar0);
            let x = ctx.scratch.intern_str(base, "x").expect("intern");
            let x = ctx.scratch.name_str(base, None, x).expect("name");
            let lam = ctx
                .scratch
                .expr_lam(base, Some(x), n_ty, body, BinderInfo::Default)
                .expect("lam");
            let out = ctx
                .transform(lam, &mut |_, _| Ok(TransformStep::Continue(None)))
                .expect("transform");
            assert_eq!(out, lam, "{}", render_expr(ctx, out));
        });
    }

    /// `.done e'` replaces WITHOUT revisiting; `.visit e'` runs `pre`
    /// again on the replacement (`Transform.lean:162-163`).
    #[test]
    fn done_replaces_and_visit_reenters_pre() {
        with_synth0_ctx(|ctx| {
            let zero = const_dotted(ctx, "N", "zero");
            let succ = const_dotted(ctx, "N", "succ");
            let one = app(ctx, succ, zero);
            let two = app(ctx, succ, one);

            let got = ctx
                .transform(zero, &mut |_, e| {
                    Ok(if e == zero {
                        TransformStep::Done(one)
                    } else if e == one {
                        TransformStep::Done(two)
                    } else {
                        TransformStep::Continue(None)
                    })
                })
                .expect("transform");
            assert_eq!(got, one, "done: no re-entry");

            let got = ctx
                .transform(zero, &mut |_, e| {
                    Ok(if e == zero {
                        TransformStep::Visit(one)
                    } else if e == one {
                        TransformStep::Done(two)
                    } else {
                        TransformStep::Continue(None)
                    })
                })
                .expect("transform");
            assert_eq!(got, two, "visit: pre runs again on the replacement");
        });
    }

    /// `.continue` descends: a rewrite inside an argument, under a
    /// binder, and inside a `let` value are all reached, and the
    /// results are rebuilt with the same constructors.
    #[test]
    fn continue_descends_into_app_lambda_and_let() {
        with_synth0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = const_dotted(ctx, "N", "zero");
            let n_ty = ctx.infer_type(zero).expect("N");
            let succ = const_dotted(ctx, "N", "succ");
            let one = app(ctx, succ, zero);
            let x = ctx.scratch.intern_str(base, "x").expect("intern");
            let x = ctx.scratch.name_str(base, None, x).expect("name");
            // fun (x : N) => let y := N.zero; N.succ y
            let bvar0 = ctx.scratch.expr_bvar(base, 0).expect("bvar");
            let let_body = app(ctx, succ, bvar0);
            let let_e = ctx
                .scratch
                .expr_let(base, Some(x), n_ty, zero, let_body, false)
                .expect("let");
            let lam = ctx
                .scratch
                .expr_lam(base, Some(x), n_ty, let_e, BinderInfo::Default)
                .expect("lam");
            let got = ctx
                .transform(lam, &mut |_, e| {
                    Ok(if e == zero {
                        TransformStep::Done(one)
                    } else {
                        TransformStep::Continue(None)
                    })
                })
                .expect("transform");
            // expected: fun (x : N) => let y := N.succ N.zero; N.succ y
            let want_let = ctx
                .scratch
                .expr_let(base, Some(x), n_ty, one, let_body, false)
                .expect("let");
            let want = ctx
                .scratch
                .expr_lam(base, Some(x), n_ty, want_let, BinderInfo::Default)
                .expect("lam");
            assert_eq!(render_expr(ctx, got), render_expr(ctx, want));
        });
    }

    /// The cache: a shared subterm is visited ONCE (`checkCache`,
    /// `:110`). `N.succ` applied to the same `N.zero` twice — an
    /// ill-typed but structurally fine term; `transform` never infers
    /// types.
    #[test]
    fn shared_subterms_are_visited_once() {
        with_synth0_ctx(|ctx| {
            let zero = const_dotted(ctx, "N", "zero");
            let succ = const_dotted(ctx, "N", "succ");
            let e = app(ctx, succ, zero);
            let e = app(ctx, e, zero);
            let mut visits_of_zero = 0usize;
            ctx.transform(e, &mut |_, x| {
                if x == zero {
                    visits_of_zero += 1;
                }
                Ok(TransformStep::Continue(None))
            })
            .expect("transform");
            assert_eq!(visits_of_zero, 1);
        });
    }
}
```

`expr_bvar` — if `Store` names its bvar constructor differently, use the
name `terms.rs` exports for `Node::BVar` (grep `pub fn expr_bvar`). If
`const_dotted` is not `pub(crate)`, make it so.

- [ ] **Step 2: Run them to verify they fail**

```bash
cargo test -p leanr_meta transform
```

Expected: compile error (`mod transform` not declared / `TransformStep`
missing). Add `mod transform;` and `pub use transform::TransformStep;` to
`lib.rs` first if the module is not found; the tests then fail on the
missing type.

- [ ] **Step 3: Implement `transform.rs`**

Above the test module:

```rust
use std::collections::HashMap;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;
use leanr_kernel::{instantiate_rev, Nat};

use crate::{MetaCtx, MetaError};

/// oracle: `inductive TransformStep` (`Transform.lean:13-26`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TransformStep {
    /// Return expression without visiting any subexpressions.
    Done(ExprId),
    /// Visit the given expression instead; it is passed to `pre` again.
    Visit(ExprId),
    /// Continue with the given expression (default: the current one) —
    /// for `pre`, visit its children.
    Continue(Option<ExprId>),
}

/// The `pre` callback: `Expr → m TransformStep`.
pub type Pre<'a, 'e> = &'a mut dyn FnMut(&mut MetaCtx<'e>, ExprId) -> Result<TransformStep, MetaError>;

type Cache = HashMap<ExprId, ExprId>;

impl<'e> MetaCtx<'e> {
    /// oracle: `Meta.transform` (`Transform.lean:179-187`) with `post`
    /// at its default and `usedLetOnly := false`, `skipConstInApp :=
    /// false` — the only configuration M4b-3 has a consumer for
    /// (`expandCoe`, `Coe.lean:46`). Terms handed to `pre` never contain
    /// loose bound variables: binders are opened with real local
    /// declarations, so any `MetaM` method is safe inside `pre`.
    pub fn transform(&mut self, input: ExprId, pre: Pre<'_, 'e>) -> Result<ExprId, MetaError> {
        let mut cache: Cache = HashMap::new();
        self.transform_visit(input, pre, &mut cache)
    }

    /// oracle: `visit` (`:109-172`) — `checkCache`, then `pre`, then
    /// the `TransformStep` dispatch. `visitPost` collapses to the
    /// identity under the default `post`.
    fn transform_visit(&mut self, e: ExprId, pre: Pre<'_, 'e>, cache: &mut Cache) -> Result<ExprId, MetaError> {
        if let Some(&r) = cache.get(&e) {
            return Ok(r);
        }
        self.step()?;
        let r = match pre(self, e)? {
            TransformStep::Done(r) => r,
            TransformStep::Visit(e2) => self.transform_visit(e2, pre, cache)?,
            TransformStep::Continue(e2) => {
                let e = e2.unwrap_or(e);
                self.transform_children(e, pre, cache)?
            }
        };
        cache.insert(e, r);
        Ok(r)
    }

    /// oracle: the `.continue` arm's `match e` (`:164-172`).
    fn transform_children(&mut self, e: ExprId, pre: Pre<'_, 'e>, cache: &mut Cache) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        match self.node(e) {
            Node::Forall { .. } => {
                let cp = self.lctx_checkpoint();
                let r = self.transform_forall(e, pre, cache);
                self.lctx_restore(cp);
                r
            }
            Node::Lam { .. } => {
                let cp = self.lctx_checkpoint();
                let r = self.transform_lambda(e, pre, cache);
                self.lctx_restore(cp);
                r
            }
            Node::LetE { .. } => {
                let cp = self.lctx_checkpoint();
                let r = self.transform_let(e, pre, cache);
                self.lctx_restore(cp);
                r
            }
            // oracle: `visitApp` (`:135-149`) without the `skipInstances`
            // branch — `e.withApp fun f args => mkAppN (← visit f) (← args.mapM visit)`.
            Node::App { .. } => {
                let f = self.get_app_fn(e);
                let args = self.get_app_args(e);
                let mut r = self.transform_visit(f, pre, cache)?;
                for a in args {
                    let a2 = self.transform_visit(a, pre, cache)?;
                    r = self.scratch.expr_app(base, r, a2)?;
                }
                Ok(r)
            }
            Node::MData { data, expr } => {
                let b = self.transform_visit(expr, pre, cache)?;
                Ok(self.scratch.expr_mdata(base, data, b)?)
            }
            Node::Proj { type_name, idx, structure } => {
                let b = self.transform_visit(structure, pre, cache)?;
                Ok(self.scratch.expr_proj(base, type_name, &Nat::from(idx), b)?)
            }
            Node::ProjBig { type_name, idx, structure } => {
                let n = self.scratch.nat_at(base, idx).clone();
                let b = self.transform_visit(structure, pre, cache)?;
                Ok(self.scratch.expr_proj(base, type_name, &n, b)?)
            }
            _ => Ok(e),
        }
    }

    /// oracle: `visitLambda` (`:117-122`) — open every leading `lam`
    /// with a local decl (visiting each domain first), visit the body,
    /// `mkLambdaFVars`. The caller checkpoints/restores the lctx.
    fn transform_lambda(&mut self, e: ExprId, pre: Pre<'_, 'e>, cache: &mut Cache) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        let mut fvars: Vec<ExprId> = Vec::new();
        let mut cur = e;
        loop {
            match self.node(cur) {
                Node::Lam { binder_name, binder_type, body, binder_info } => {
                    let d = instantiate_rev(self.scratch, base, binder_type, &fvars, &mut self.guard)?;
                    let d = self.transform_visit(d, pre, cache)?;
                    let x = self.push_local_decl(binder_name, d, binder_info)?;
                    fvars.push(x);
                    cur = body;
                }
                _ => {
                    let b = instantiate_rev(self.scratch, base, cur, &fvars, &mut self.guard)?;
                    let b = self.transform_visit(b, pre, cache)?;
                    return self.mk_lambda(&fvars, b);
                }
            }
        }
    }

    /// oracle: `visitForall` (`:123-128`) — same shape, `mkForallFVars`.
    fn transform_forall(&mut self, e: ExprId, pre: Pre<'_, 'e>, cache: &mut Cache) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        let mut fvars: Vec<ExprId> = Vec::new();
        let mut cur = e;
        loop {
            match self.node(cur) {
                Node::Forall { binder_name, binder_type, body, binder_info } => {
                    let d = instantiate_rev(self.scratch, base, binder_type, &fvars, &mut self.guard)?;
                    let d = self.transform_visit(d, pre, cache)?;
                    let x = self.push_local_decl(binder_name, d, binder_info)?;
                    fvars.push(x);
                    cur = body;
                }
                _ => {
                    let b = instantiate_rev(self.scratch, base, cur, &fvars, &mut self.guard)?;
                    let b = self.transform_visit(b, pre, cache)?;
                    return self.mk_forall(&fvars, b);
                }
            }
        }
    }

    /// oracle: `visitLet` (`:129-134`) — open every leading `letE` with
    /// a let-decl (visiting type and value first), visit the body, then
    /// `mkLetFVars (usedLetOnly := false)`, i.e. every let is rebuilt
    /// innermost-first.
    fn transform_let(&mut self, e: ExprId, pre: Pre<'_, 'e>, cache: &mut Cache) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        let mut fvars: Vec<ExprId> = Vec::new();
        let mut lets: Vec<(ExprId, bool)> = Vec::new();
        let mut cur = e;
        loop {
            match self.node(cur) {
                Node::LetE { decl_name, ty, value, body, non_dep } => {
                    let t = instantiate_rev(self.scratch, base, ty, &fvars, &mut self.guard)?;
                    let t = self.transform_visit(t, pre, cache)?;
                    let v = instantiate_rev(self.scratch, base, value, &fvars, &mut self.guard)?;
                    let v = self.transform_visit(v, pre, cache)?;
                    let x = self.push_let_decl(decl_name, t, v)?;
                    fvars.push(x);
                    lets.push((x, non_dep));
                    cur = body;
                }
                _ => {
                    let b = instantiate_rev(self.scratch, base, cur, &fvars, &mut self.guard)?;
                    let mut b = self.transform_visit(b, pre, cache)?;
                    for (x, non_dep) in lets.iter().rev() {
                        b = self.mk_let_expr(*x, b, *non_dep)?;
                    }
                    return Ok(b);
                }
            }
        }
    }
}
```

If `MetaCtx::step` is not reachable from this module (it is `fn step`
in `metactx.rs`), widen it to `pub(crate)`; do not add a new counter.

- [ ] **Step 4: Run the tests to verify they pass**

```bash
cargo test -p leanr_meta transform
```

Expected: 4 PASS. If `transform_is_the_identity_when_pre_continues`
fails on the lambda round-trip, the mismatch is the binder NAME
`mk_lambda` restores from the local decl vs the one `expr_lam` was given
— compare `render_expr` output and fix the test to build the lambda from
`push_local_decl` + `mk_lambda` in the first place rather than weakening
the assertion.

- [ ] **Step 5: Add the three helpers and the error variant, with tests**

`crates/leanr_meta/src/metactx.rs`, after `set_transparency` (`:401-403`):

```rust
    /// oracle: `withTransparency` as `withDefault` / `withReducible` /
    /// `withReducibleAndInstances` use it (`Basic.lean:1278-1292`) —
    /// save, set, run, restore. `pub` so `leanr_elab`'s ladder can run
    /// the `.coe` arm's `withDefault isDefEq` (`SyntheticMVars.lean:546`).
    ///
    /// Plain save/run/restore with no drop guard, the same posture as
    /// `with_assignable_synthetic_opaque` below and for the same reason
    /// (its doc, design spec § Follow-ups item 4): every caller is
    /// `Result`-based and catches nothing, so an unwinding caller cannot
    /// observe the un-restored flag.
    pub fn with_transparency<R>(&mut self, t: TransparencyMode, f: impl FnOnce(&mut Self) -> R) -> R {
        let saved = self.cfg.transparency;
        self.cfg.transparency = t;
        let r = f(self);
        self.cfg.transparency = saved;
        r
    }

    /// oracle: `mkArrow` (`Lean/Meta/Basic.lean`, `mkForall _ .default d b`
    /// with a fresh user name) — a NON-dependent `forallE`. The binder
    /// name is `None`: the only consumer is the TYPE of `coerceToFunction?`'s
    /// `?γ` (`Coe.lean:105`), which is never emitted, and the canonical
    /// encoder erases binder names anyway.
    pub(crate) fn mk_arrow(&mut self, dom: ExprId, cod: ExprId) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        Ok(self
            .scratch
            .expr_forall(base, None, dom, cod, BinderInfo::Default)?)
    }
```

`crates/leanr_meta/src/whnf.rs`, after `whnf_default` (`:1834-1840`):

```rust
    /// oracle: `whnfR` (`Basic.lean:2113-2114`) — `withTransparency
    /// .reducible <| whnf e`. Composed here rather than exported: its
    /// only consumers are in-crate (`coe.rs`'s `isTypeApp?` and
    /// `coerceCollectingNames?`'s `whnfR expectedType`).
    pub(crate) fn whnf_r(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        self.with_transparency(TransparencyMode::Reducible, |ctx| ctx.whnf(e))
    }
```

`crates/leanr_meta/src/error.rs`, in `pub enum MetaError`:

```rust
    /// oracle: the three `throwError`s in `Meta/Coe.lean` that fire AFTER
    /// a coercion instance was found and expanded but the expansion has
    /// the wrong shape — "coerced expression has wrong type" (`:86-87`),
    /// "result is still not a function" (`:108-110`), "result is still
    /// not a type" (`:122-124`). Hard errors in the oracle too (they are
    /// not `.none`/`.undef`), so they are a variant, not an `LOption`
    /// arm. `leanr_elab` surfaces it through `ElabError::Meta`.
    CoeExpansionMismatch(String),
```

(and an arm in `MetaError`'s `Display` impl if the file has one).

Test, appended inside `metactx.rs`'s `#[cfg(test)] mod tests`:

```rust
    /// `with_transparency` restores on the normal path and nests.
    #[test]
    fn with_transparency_restores_the_ambient_mode() {
        use crate::test_support::with_prelude0_ctx;
        use crate::TransparencyMode as T;
        with_prelude0_ctx(|ctx| {
            assert_eq!(ctx.cfg().transparency, T::Default);
            ctx.with_transparency(T::Instances, |ctx| {
                assert_eq!(ctx.cfg().transparency, T::Instances);
                ctx.with_transparency(T::Reducible, |ctx| {
                    assert_eq!(ctx.cfg().transparency, T::Reducible);
                });
                assert_eq!(ctx.cfg().transparency, T::Instances);
            });
            assert_eq!(ctx.cfg().transparency, T::Default);
        });
    }
```

- [ ] **Step 6: Run the crate's tests**

```bash
cargo test -p leanr_meta
```

Expected: PASS (including `oracle_fast`/`oracle_synth`, untouched).

- [ ] **Step 7: Commit**

```bash
mise run ci
git add crates/leanr_meta/src/transform.rs crates/leanr_meta/src/lib.rs crates/leanr_meta/src/metactx.rs crates/leanr_meta/src/whnf.rs crates/leanr_meta/src/error.rs crates/leanr_meta/src/test_support.rs
git commit -F - <<'MSG'
M4b-3 P4 task 4: transform.rs, with_transparency, whnf_r, mk_arrow

Meta/Transform.lean:97-187 ported for expandCoe's configuration only
(pre, default flags): cached visit, .visit re-entry, app/mdata/proj
arms, and the three binder telescopes over real local decls. Plus the
scoped transparency helper, whnfR, a non-dependent arrow constructor,
and MetaError::CoeExpansionMismatch for Coe.lean's post-expansion
throws. All additive.

Claude-Session: https://claude.ai/code/session_01P6daLFfQsqbKWFUWVvJqZs
MSG
```

---

### Task 5: `coe.rs` — `expand_coe`, `coerce_simple`, `coerce_to_function`, `coerce_to_sort`, the guard, `coerce`

`Lean/Meta/Coe.lean` 1:1 (A5 items 1, 5, 6, 7), verified over the
`Synth0` environment Task 1 built. The guard's positive test needs an
environment that declares `Monad`; `Instances.lean` (a unit-test-only
fixture with no corpus) gets an existence-only axiom for it.

**Files:**
- Create: `crates/leanr_meta/src/coe.rs`
- Modify: `crates/leanr_meta/src/lib.rs` (`mod coe;`)
- Modify: `tests/fixtures/Instances.lean` (append), regenerate `tests/fixtures/Instances.olean`
- Test: `crates/leanr_meta/src/coe.rs` (`#[cfg(test)]`)

**Interfaces:**
- Consumes: `try_synth_instance` / `LOption` (Task 3), `transform` / `TransformStep`, `with_transparency`, `whnf_r`, `mk_arrow`, `CoeExpansionMismatch` (Task 4), `is_coe_decl` (Task 2), the crate-private `unfold_definition`, `head_beta`, `get_level`, `fresh_level_mvar`, `mk_aux_mvar`.
- Produces (all `pub` on `MetaCtx`): `expand_coe(&mut self, e: ExprId) -> Result<ExprId, MetaError>`;
  `coerce_simple(&mut self, e: ExprId, expected: ExprId) -> Result<LOption<ExprId>, MetaError>`;
  `coerce_to_function(&mut self, e: ExprId) -> Result<Option<ExprId>, MetaError>`;
  `coerce_to_sort(&mut self, e: ExprId) -> Result<Option<ExprId>, MetaError>`;
  `coerce(&mut self, e: ExprId, expected: ExprId) -> Result<LOption<ExprId>, MetaError>` — `Err(MetaError::Unsupported("monad-lift coercion requires the do-notation slice"))` on the guarded shape.

- [ ] **Step 1: Add the `Monad` axiom to `Instances.lean` and regenerate**

Append to `tests/fixtures/Instances.lean`:

```lean
-- === M4b-3 P4: the monad-lift shape guard's positive environment ===
--
-- `coerce`'s guard (design spec § Amendment 5 item 6) fires only when
-- BOTH types reduce to type applications AND the environment contains
-- `Monad` or `MonadLiftT` — the only shape on which the oracle's
-- `coerceMonadLift?` (`Meta/Coe.lean:201-257`) can return `some`. This
-- axiom is EXISTENCE-ONLY (nothing reads its type) so that
-- `coe.rs`'s unit test can drive the guard over this fixture, while the
-- two corpus fixtures (`Synth0`, `Elab0`) stay `Monad`-free and never
-- reach it. No corpus record is dumped from this file.
axiom Monad : (Type → Type) → Type
```

```bash
mise run fixtures:regen 2>&1 | grep -i 'error\|failed' ; git status --short
```

Expected: only `Instances.lean` and `Instances.olean` changed.

- [ ] **Step 2: Write the failing tests**

Create `crates/leanr_meta/src/coe.rs` with the test module:

```rust
//! oracle: `Lean/Meta/Coe.lean` (v4.33.0-rc1), 1:1 — `expandCoe`
//! (`:44-70`), `coerceSimpleRecordingNames?`/`coerceSimple?` (`:78-98`),
//! `coerceToFunction?` (`:100-112`), `coerceToSort?` (`:114-126`),
//! `isTypeApp?` (`:128-132`), `coerceCollectingNames?`/`coerce?`
//! (`:259-278`). `coerceMonadLift?` (`:201-257`) is a shape GUARD, not a
//! port — design spec § Amendment 5 item 6 and `monad_lift_guard` below.
//!
//! Dropped, deliberately, because they have no term impact (§ Amendment
//! 5 item 5): the applied-instance name list (`StateT` over `List Name`,
//! consumed only by the `CoeExpansionTrace` info leaf), `pushInfoLeaf`,
//! and `recordExtraModUseFromDecl` (`recProjTarget`'s only purpose).
//!
//! What `expandCoe` actually reduces: `CoeT.coe` and its siblings are
//! class projections, kept NON-reducible by the oracle (`WHNF.lean:810-811`),
//! so under `.instances` `unfoldDefinition?`'s `matchConstAux` fails and
//! its continuation `unfoldProjInstWhenInstances?` (`:814-818`) →
//! `unfoldProjInst?` (`:793-806`) does the work: delta-beta the projection
//! at default transparency, then reduce `inst.1` against the instance's
//! constructor at `.instances`. `whnf.rs::unfold_definition_app` already
//! routes both failure sub-conditions to `unfold_proj_inst` (M4a plan 4
//! task B6), so `expand_coe` needs no `whnf.rs` change.

#[cfg(test)]
mod tests {
    use crate::synth::LOption;
    use crate::test_support::{const_dotted, const_named, render_expr, with_instances_ctx, with_synth0_ctx};
    use crate::{MetaCtx, MetaError};
    use leanr_kernel::bank::ExprId;

    fn app(ctx: &mut MetaCtx, f: ExprId, args: &[ExprId]) -> ExprId {
        let base = Some(ctx.view.store);
        let mut r = f;
        for a in args {
            r = ctx.scratch.expr_app(base, r, *a).expect("app");
        }
        r
    }

    /// `(N.zero : M)` — one `Coe` step: the instance is found through
    /// `CoeT ← CoeHTCT ← CoeHTC ← CoeOTC ← CoeTC ← Coe`, and `expand_coe`
    /// unfolds every projection down to the instance's own function.
    #[test]
    fn coerce_simple_expands_one_step_to_the_instance_function() {
        with_synth0_ctx(|ctx| {
            let zero = const_dotted(ctx, "N", "zero");
            let m = const_named(ctx, "M");
            let of_n = const_dotted(ctx, "M", "ofN");
            let want = app(ctx, of_n, &[zero]);
            match ctx.coerce_simple(zero, m).expect("coerce") {
                LOption::Some(got) => assert_eq!(render_expr(ctx, got), render_expr(ctx, want)),
                other => panic!("expected Some, got {other:?}"),
            }
        });
    }

    /// `(N.zero : Big)` — two steps through `CoeTC`'s transitive
    /// instance (`[Coe β γ] [CoeTC α β] : CoeTC α γ`, `β := M` found by
    /// the search). Kill: stub `expand_coe` to the identity and the
    /// result carries `CoeT.coe`.
    #[test]
    fn coerce_simple_expands_two_steps() {
        with_synth0_ctx(|ctx| {
            let zero = const_dotted(ctx, "N", "zero");
            let big = const_named(ctx, "Big");
            let of_n = const_dotted(ctx, "M", "ofN");
            let of_m = const_dotted(ctx, "Big", "ofM");
            let inner = app(ctx, of_n, &[zero]);
            let want = app(ctx, of_m, &[inner]);
            match ctx.coerce_simple(zero, big).expect("coerce") {
                LOption::Some(got) => assert_eq!(render_expr(ctx, got), render_expr(ctx, want)),
                other => panic!("expected Some, got {other:?}"),
            }
        });
    }

    /// `(N.zero : N)` — the reflexive `instance : CoeT α a α` (declared
    /// last, tried first) whose `coe := a`; the expansion IS `N.zero`.
    #[test]
    fn coerce_simple_reflexive_expands_to_the_term_itself() {
        with_synth0_ctx(|ctx| {
            let zero = const_dotted(ctx, "N", "zero");
            let n = const_named(ctx, "N");
            assert!(matches!(ctx.coerce_simple(zero, n).expect("coerce"), LOption::Some(got) if got == zero));
        });
    }

    /// `(N.zero : NoBase)` — no path through the diamond; `.none`, and
    /// the search TERMINATES (the reflexive/transitive instances are
    /// what a non-tabled resolver would loop on).
    #[test]
    fn coerce_simple_answers_none_when_no_chain_exists() {
        with_synth0_ctx(|ctx| {
            let zero = const_dotted(ctx, "N", "zero");
            let no_base = const_named(ctx, "NoBase");
            assert!(matches!(ctx.coerce_simple(zero, no_base).expect("coerce"), LOption::None));
        });
    }

    /// `coerceToFunction?` on `FnN.mk N.succ : FnN` — `CoeFun FnN ?γ`
    /// assigns the outParam, and the expansion is `FnN.f (FnN.mk N.succ)`,
    /// whose type reduces to a `forall`.
    #[test]
    fn coerce_to_function_expands_the_coe_fun_instance() {
        with_synth0_ctx(|ctx| {
            let succ = const_dotted(ctx, "N", "succ");
            let mk = const_dotted(ctx, "FnN", "mk");
            let g = app(ctx, mk, &[succ]);
            let f = const_dotted(ctx, "FnN", "f");
            let want = app(ctx, f, &[g]);
            let got = ctx.coerce_to_function(g).expect("coerce").expect("some");
            assert_eq!(render_expr(ctx, got), render_expr(ctx, want));
        });
    }

    /// `coerceToFunction?` on something with no `CoeFun` instance is
    /// `none`, not an error.
    #[test]
    fn coerce_to_function_is_none_without_an_instance() {
        with_synth0_ctx(|ctx| {
            let zero = const_dotted(ctx, "N", "zero");
            assert!(ctx.coerce_to_function(zero).expect("coerce").is_none());
        });
    }

    /// `coerceToSort?` on `SortN.mk N : SortN` — `CoeSort SortN ?β`
    /// assigns the outParam; the expansion `SortN.ty (SortN.mk N)` has a
    /// `Sort` type.
    #[test]
    fn coerce_to_sort_expands_the_coe_sort_instance() {
        with_synth0_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let mk = const_dotted(ctx, "SortN", "mk");
            let s = app(ctx, mk, &[n]);
            let ty = const_dotted(ctx, "SortN", "ty");
            let want = app(ctx, ty, &[s]);
            let got = ctx.coerce_to_sort(s).expect("coerce").expect("some");
            assert_eq!(render_expr(ctx, got), render_expr(ctx, want));
        });
    }

    /// `coerce` dispatch order (`Coe.lean:259-266`): with a `forall`
    /// expected type, `CoeFun` is tried BEFORE `CoeT` and wins when its
    /// result's type is defeq to the expected type.
    #[test]
    fn coerce_prefers_coe_fun_under_a_forall_expected_type() {
        with_synth0_ctx(|ctx| {
            let succ = const_dotted(ctx, "N", "succ");
            let mk = const_dotted(ctx, "FnN", "mk");
            let g = app(ctx, mk, &[succ]);
            let expected = ctx.infer_type(succ).expect("N -> N");
            let f = const_dotted(ctx, "FnN", "f");
            let want = app(ctx, f, &[g]);
            match ctx.coerce(g, expected).expect("coerce") {
                LOption::Some(got) => assert_eq!(render_expr(ctx, got), render_expr(ctx, want)),
                other => panic!("expected Some, got {other:?}"),
            }
        });
    }

    /// `expand_coe` on an untagged head is the identity.
    #[test]
    fn expand_coe_leaves_untagged_heads_alone() {
        with_synth0_ctx(|ctx| {
            let zero = const_dotted(ctx, "N", "zero");
            let succ = const_dotted(ctx, "N", "succ");
            let e = app(ctx, succ, &[zero]);
            assert_eq!(ctx.expand_coe(e).expect("expand"), e);
        });
    }

    /// The monad-lift guard (design spec § Amendment 5 item 6). Over
    /// `Instances.olean`, which declares `Monad`: two type applications
    /// (`Prod N N` vs `Prod N NoBase`) hit the seam. Over `Synth0.olean`,
    /// which does not: the same shape falls through to `coerce_simple`
    /// and answers `.none`, exactly as the oracle's `coerceMonadLift?`
    /// returns `none` in an environment without `Monad`/`MonadLiftT`.
    #[test]
    fn monad_lift_guard_fires_only_when_the_env_declares_monad() {
        fn prod_shape(ctx: &mut MetaCtx) -> (ExprId, ExprId) {
            let base = Some(ctx.view.store);
            let zero_l = ctx.scratch.level_zero(base).expect("level");
            let ls = ctx.scratch.intern_level_list(base, &[zero_l, zero_l]).expect("levels");
            let n = const_named(ctx, "N");
            let no_base = const_named(ctx, "NoBase");
            let zero = const_dotted(ctx, "N", "zero");
            let mk_str = ctx.scratch.intern_str(base, "Prod").expect("intern");
            let prod = ctx.scratch.name_str(base, None, mk_str).expect("name");
            let mk_s = ctx.scratch.intern_str(base, "mk").expect("intern");
            let prod_mk = ctx.scratch.name_str(base, Some(prod), mk_s).expect("name");
            let prod_c = ctx.scratch.expr_const(base, Some(prod), ls).expect("const");
            let prod_mk_c = ctx.scratch.expr_const(base, Some(prod_mk), ls).expect("const");
            let e = app(ctx, prod_mk_c, &[n, n, zero, zero]);
            let expected = app(ctx, prod_c, &[n, no_base]);
            (e, expected)
        }
        with_instances_ctx(|ctx| {
            let (e, expected) = prod_shape(ctx);
            match ctx.coerce(e, expected) {
                Err(MetaError::Unsupported(m)) => assert!(m.contains("do-notation"), "{m}"),
                other => panic!("expected the monad-lift seam, got {other:?}"),
            }
        });
        with_synth0_ctx(|ctx| {
            let (e, expected) = prod_shape(ctx);
            assert!(matches!(ctx.coerce(e, expected).expect("coerce"), LOption::None));
        });
    }
}
```

`Prod` in both fixtures is `structure Prod (α : Type u) (β : Type v)`
with `N : Type`, so `Prod.{0,0}`; if `Instances.lean`'s `Prod` differs,
read its declaration and adjust the level list.

- [ ] **Step 3: Run them to verify they fail**

```bash
cargo test -p leanr_meta coe::
```

Expected: compile errors on the missing methods (add `mod coe;` to
`lib.rs` first if needed).

- [ ] **Step 4: Implement `coe.rs`**

Above the test module:

```rust
use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId, NameId};

use crate::synth::LOption;
use crate::transform::TransformStep;
use crate::{MetaCtx, MetaError, TransparencyMode};

impl<'e> MetaCtx<'e> {
    fn name_of(&mut self, parts: &[&str]) -> Result<NameId, MetaError> {
        let base = Some(self.view.store);
        let mut id: Option<NameId> = None;
        for p in parts {
            let s = self.scratch.intern_str(base, p)?;
            id = Some(self.scratch.name_str(base, id, s)?);
        }
        Ok(id.expect("name_of: non-empty"))
    }

    fn const_with_levels(&mut self, parts: &[&str], levels: &[LevelId]) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        let n = self.name_of(parts)?;
        let ls = self.scratch.intern_level_list(base, levels)?;
        Ok(self.scratch.expr_const(base, Some(n), ls)?)
    }

    fn mk_app_n(&mut self, f: ExprId, args: &[ExprId]) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        let mut r = f;
        for a in args {
            r = self.scratch.expr_app(base, r, *a)?;
        }
        Ok(r)
    }

    /// oracle: `expandCoe` (`Coe.lean:44-70`) — under
    /// `withReducibleAndInstances`, `transform` with a `pre` that, on an
    /// application whose head is a `@[coe_decl]` constant, unfolds it
    /// (`unfoldDefinition?`, `:56` — see the module doc for what that
    /// actually reduces on a class projection), `headBeta`s, and
    /// `.visit`s the result so `pre` runs on it again (`:66`); every
    /// other node `.continue`s (`:67`).
    pub fn expand_coe(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        self.with_transparency(TransparencyMode::Instances, |ctx| {
            ctx.transform(e, &mut |ctx, e| {
                let f = ctx.get_app_fn(e);
                if let Node::Const { name: Some(decl), .. } = ctx.node(f) {
                    if ctx.is_coe_decl(decl) {
                        if let Some(e2) = ctx.unfold_definition(e)? {
                            let e2 = ctx.head_beta(e2)?;
                            return Ok(TransformStep::Visit(e2));
                        }
                    }
                }
                Ok(TransformStep::Continue(None))
            })
        })
    }

    /// oracle: `coerceSimpleRecordingNames?` + `coerceSimple?`
    /// (`Coe.lean:78-98`) — synthesize `CoeT.{u,v} eType e expected`,
    /// build `CoeT.coe.{u,v} eType e expected inst`, `expandCoe`, and
    /// VERIFY the result's type is defeq to `expected` (`:86-87`): a
    /// mismatch is a hard error, not a silent pass.
    pub fn coerce_simple(&mut self, e: ExprId, expected: ExprId) -> Result<LOption<ExprId>, MetaError> {
        let e_type = self.infer_type(e)?;
        let u = self.get_level(e_type)?;
        let v = self.get_level(expected)?;
        let coe_t = self.const_with_levels(&["CoeT"], &[u, v])?;
        let goal = self.mk_app_n(coe_t, &[e_type, e, expected])?;
        match self.try_synth_instance(goal)? {
            LOption::Some(inst) => {
                let coe_t_coe = self.const_with_levels(&["CoeT", "coe"], &[u, v])?;
                let app = self.mk_app_n(coe_t_coe, &[e_type, e, expected, inst])?;
                let result = self.expand_coe(app)?;
                let r_type = self.infer_type(result)?;
                if !self.is_def_eq(r_type, expected)? {
                    return Err(MetaError::CoeExpansionMismatch(
                        "could not coerce: coerced expression has wrong type (Coe.lean:86-87)".into(),
                    ));
                }
                Ok(LOption::Some(result))
            }
            LOption::Undef => Ok(LOption::Undef),
            LOption::None => Ok(LOption::None),
        }
    }

    /// oracle: `coerceToFunction?` (`Coe.lean:100-112`) — `α ← inferType`,
    /// `u ← getLevel α`, `v` a fresh level mvar, `?γ : α → Sort v` a fresh
    /// expr mvar (the class's `outParam`, which the search assigns —
    /// P2b-i's `assignOutParams`), `trySynthInstance (CoeFun.{u,v} α ?γ)`
    /// with BOTH `.none` and `.undef` mapped to `none` (`:106`), expand
    /// `CoeFun.coe.{u,v} α ?γ inst e`, and require the result's type to
    /// `whnf` to a `forall` (`:108-110`).
    pub fn coerce_to_function(&mut self, e: ExprId) -> Result<Option<ExprId>, MetaError> {
        let base = Some(self.view.store);
        let alpha = self.infer_type(e)?;
        let u = self.get_level(alpha)?;
        let (_, v) = self.fresh_level_mvar()?;
        let sort_v = self.scratch.expr_sort(base, v)?;
        let gamma_ty = self.mk_arrow(alpha, sort_v)?;
        let (gamma, _) = self.mk_aux_mvar(gamma_ty)?;
        let coe_fun = self.const_with_levels(&["CoeFun"], &[u, v])?;
        let goal = self.mk_app_n(coe_fun, &[alpha, gamma])?;
        let LOption::Some(inst) = self.try_synth_instance(goal)? else {
            return Ok(None);
        };
        let coe = self.const_with_levels(&["CoeFun", "coe"], &[u, v])?;
        let app = self.mk_app_n(coe, &[alpha, gamma, inst, e])?;
        let expanded = self.expand_coe(app)?;
        let t = self.infer_type(expanded)?;
        let w = self.whnf(t)?;
        if !matches!(self.node(w), Node::Forall { .. }) {
            return Err(MetaError::CoeExpansionMismatch(
                "failed to coerce to a function: after applying CoeFun.coe the result is still not a function (Coe.lean:108-110)".into(),
            ));
        }
        Ok(Some(expanded))
    }

    /// oracle: `coerceToSort?` (`Coe.lean:114-126`) — the `CoeSort` twin:
    /// `?β : Sort v`, `CoeSort.{u,v} α ?β`, expand `CoeSort.coe.{u,v} α ?β
    /// inst e`, require a `Sort` (`:122-124`).
    pub fn coerce_to_sort(&mut self, e: ExprId) -> Result<Option<ExprId>, MetaError> {
        let base = Some(self.view.store);
        let alpha = self.infer_type(e)?;
        let u = self.get_level(alpha)?;
        let (_, v) = self.fresh_level_mvar()?;
        let sort_v = self.scratch.expr_sort(base, v)?;
        let (beta, _) = self.mk_aux_mvar(sort_v)?;
        let coe_sort = self.const_with_levels(&["CoeSort"], &[u, v])?;
        let goal = self.mk_app_n(coe_sort, &[alpha, beta])?;
        let LOption::Some(inst) = self.try_synth_instance(goal)? else {
            return Ok(None);
        };
        let coe = self.const_with_levels(&["CoeSort", "coe"], &[u, v])?;
        let app = self.mk_app_n(coe, &[alpha, beta, inst, e])?;
        let expanded = self.expand_coe(app)?;
        let t = self.infer_type(expanded)?;
        let w = self.whnf(t)?;
        if !matches!(self.node(w), Node::Sort { .. }) {
            return Err(MetaError::CoeExpansionMismatch(
                "failed to coerce to a type: after applying CoeSort.coe the result is still not a type (Coe.lean:122-124)".into(),
            ));
        }
        Ok(Some(expanded))
    }

    /// oracle: `isTypeApp?` (`Coe.lean:128-132`) — `withReducible whnf`,
    /// then `some (m, α)` on an `.app m α` with both halves
    /// `instantiateMVars`-ed.
    pub(crate) fn is_type_app(&mut self, ty: ExprId) -> Result<Option<(ExprId, ExprId)>, MetaError> {
        let w = self.whnf_r(ty)?;
        match self.node(w) {
            Node::App { f, arg } => {
                let f = self.instantiate_mvars(f)?;
                let a = self.instantiate_mvars(arg)?;
                Ok(Some((f, a)))
            }
            _ => Ok(None),
        }
    }

    /// The monad-lift shape guard (design spec § Amendment 5 item 6) —
    /// NOT a port of `coerceMonadLift?` (`Coe.lean:201-257`), which is
    /// the do-notation slice's.
    ///
    /// The oracle tries it FIRST (`:260`), so silently skipping it would
    /// let a term the oracle coerces via `coeM`/`liftM`/`liftCoeM` fall
    /// through to `CoeT` and emit a different term. But it can only
    /// return `some` when (a) both `expectedType` and `eType` are
    /// `isTypeApp?` (`:204-205`) AND (b) either `isMonad? n` answers
    /// `some` — `trySynthInstance (Monad n)` inside a `try … catch _ =>
    /// none` (`AppBuilder.lean:701-709`) — or `autoLift`'s `MonadLiftT m n`
    /// synthesis inside another `try … catch _ => return none`
    /// (`:214-245`) does. Without `Monad` and `MonadLiftT` in the
    /// environment both are `none` on every input, and the oracle
    /// proceeds to `coerceToFunction?`/`coerceSimpleRecordingNames?`.
    /// So the guard is exactly (a) ∧ (env contains `Monad` ∨ `MonadLiftT`),
    /// and on every other shape leanr proceeds as the oracle does.
    ///
    /// Known residual, owner do-notation slice: on the `autoLift` branch
    /// the oracle runs `isLevelDefEq` (`:224`) BEFORE the `MonadLiftT`
    /// synthesis fails, and that level assignment is not rolled back.
    /// With concrete-universe type constructors — every shape the
    /// fixtures can express — it assigns nothing.
    fn monad_lift_guard(&mut self, e: ExprId, expected: ExprId) -> Result<(), MetaError> {
        let expected = self.instantiate_mvars(expected)?;
        let e_type = self.infer_type(e)?;
        let e_type = self.instantiate_mvars(e_type)?;
        if self.is_type_app(expected)?.is_none() {
            return Ok(());
        }
        if self.is_type_app(e_type)?.is_none() {
            return Ok(());
        }
        let monad = self.name_of(&["Monad"])?;
        let lift = self.name_of(&["MonadLiftT"])?;
        if self.view.get(monad).is_some() || self.view.get(lift).is_some() {
            return Err(MetaError::Unsupported(
                "monad-lift coercion requires the do-notation slice".into(),
            ));
        }
        Ok(())
    }

    /// oracle: `coerceCollectingNames?` + `coerce?` (`Coe.lean:259-278`),
    /// preserving the dispatch order — monad lift (the guard), then
    /// `CoeFun` when `whnfR expectedType` is a `forall` and the coerced
    /// function's type is defeq to it (`:262-265`), then `CoeT`.
    pub fn coerce(&mut self, e: ExprId, expected: ExprId) -> Result<LOption<ExprId>, MetaError> {
        self.monad_lift_guard(e, expected)?;
        let w = self.whnf_r(expected)?;
        if matches!(self.node(w), Node::Forall { .. }) {
            if let Some(f) = self.coerce_to_function(e)? {
                let f_type = self.infer_type(f)?;
                if self.is_def_eq(f_type, expected)? {
                    return Ok(LOption::Some(f));
                }
            }
        }
        self.coerce_simple(e, expected)
    }
}
```

`EnvView::get` is the constant lookup the crate already uses
(`self.view.get(name)`); if the method is named differently in
`leanr_kernel::EnvView`, use the one `synth.rs` calls to look up an
instance constant.

- [ ] **Step 5: Run the tests to verify they pass**

```bash
cargo test -p leanr_meta coe::
```

Expected: 10 PASS. Diagnosing the likely failures, in order:
`coerce_simple_*` returning a term containing `CoeT.coe` means
`expand_coe`'s transparency is not `Instances` at the `unfold_definition`
call (check `with_transparency` wraps the whole `transform`); a term
containing a `.proj` node means `unfold_proj_inst` was not reached
(check `unfold_definition_app`'s two `failK` call sites); an `Undef` on
`coerce_to_function` means `?γ` was minted at an unassignable kind or
the `CoeFun` outParam position was not exempted (Task 3's pre-test reads
`get_out_param_positions`, which `Synth0.olean` provides for `CoeFun`
since Task 1).

- [ ] **Step 6: Measure the discriminators**

Apply each mutation, run `cargo test -p leanr_meta coe::`, confirm the
named test goes RED, revert:

- `expand_coe` returns `Ok(e)` unchanged → `coerce_simple_expands_one_step_to_the_instance_function`, `_two_steps`, `coerce_to_function_expands_the_coe_fun_instance`, `coerce_to_sort_expands_the_coe_sort_instance` (the `CoeExpansionMismatch` on the last two: the unexpanded `CoeFun.coe … g`'s type is `?γ g`, which does not `whnf` to a `forall`).
- `coerce` skips the `whnf_r`-is-forall branch → `coerce_prefers_coe_fun_under_a_forall_expected_type` (falls to `coerce_simple`, which answers `None` for `FnN` → `N → N`).
- `monad_lift_guard` drops the env check → `monad_lift_guard_fires_only_when_the_env_declares_monad` (the `Synth0` half).

Record the three outcomes in the commit message.

- [ ] **Step 7: Run the whole meta tier and commit**

```bash
mise run meta:fast
mise run ci
git add crates/leanr_meta/src/coe.rs crates/leanr_meta/src/lib.rs tests/fixtures/Instances.lean tests/fixtures/Instances.olean
git commit -F - <<'MSG'
M4b-3 P4 task 5: coe.rs — expand_coe, coerce_simple, coerce_to_function, coerce_to_sort, coerce

Meta/Coe.lean 1:1 over Synth0's chain: expansion unfolds class
projections through unfold_proj_inst at Instances transparency down to
the instance function; the three post-expansion checks raise
CoeExpansionMismatch; coerce keeps the oracle's monad-lift -> CoeFun ->
CoeT order with the lift as the corrected shape guard (env declares
Monad/MonadLiftT AND both types are type apps). Instances.lean gains an
existence-only Monad axiom for the guard's positive test.

Mutations measured: <fill in from step 6>.

Claude-Session: https://claude.ai/code/session_01P6daLFfQsqbKWFUWVvJqZs
MSG
```

---
### Task 6: the chain lands in `Elab0.lean` — a pure regression gate

The elaborator fixture gains `semiOutParam`, the verbatim chain, `Int`,
`Big`, `NatAlias`, `Wrapper`, `Fn`, `Carrier` and their instances, with
NO new queries. Every one of the 107 committed records must come back
byte-identical: no committed record mentions a `Coe*` class, instances
are indexed by class, so no existing goal gains a candidate (A5 item
11). Landing the fixture separately from the mechanisms (Tasks 7–9) is
what keeps every intermediate commit green.

**Files:**
- Modify: `tests/fixtures/elab/Elab0.lean` (append after `axiom Lean.Internal.coeM : Type`, `:452`)
- Regenerated: `tests/fixtures/elab/Elab0.olean` (and `elab-queries.jsonl`, which must NOT change)

**Interfaces:**
- Produces: fixture constants `semiOutParam`, the chain, `Int`
  (`Int.ofNat`, `Int.negSucc`), `Big` (`Big.ofInt`), `instCoeNatInt`,
  `instCoeIntBig`, `takesInt`, `NatAlias`, `Wrapper` (`Wrapper.mk`,
  `Wrapper.val`), `instCoeNatWrapper`, `pairW`, `Fn` (`Fn.mk`, `Fn.f`),
  `instCoeFunFn`, `Carrier` (`Carrier.mk`, `Carrier.ty`),
  `instCoeSortCarrier`. Tasks 7–9's records and smoke tests use them.

- [ ] **Step 1: Append the fixture block**

```lean
-- === M4b-3 P4: coercions (design spec § P4, § Amendment 5 item 9) ===
--
-- `semiOutParam` at the ROOT namespace, verbatim from
-- `Init/Prelude.lean:725` — the `outParam` reasoning above applies:
-- `Coe`'s first parameter is `semiOutParam (Sort u)` and only the root
-- name is the real gadget. Inert here beyond being reducible.
@[reducible] def semiOutParam (α : Sort u) : Sort u := α

-- The chain, VERBATIM from `Init/Coe.lean:131-287` of the pin (doc
-- comments dropped, nothing else changed), the same block
-- `tests/fixtures/meta/Synth0.lean` carries — proved out at the
-- synthesis tier first (M4b-3 P4 task 1), where the resolver's path
-- through the reflexive/transitive diamond is observable; here
-- `expandCoe` unfolds the instance away and the records pin the
-- resulting FUNCTION (`Int.ofNat n`).
class Coe (α : semiOutParam (Sort u)) (β : Sort v) where
  coe : α → β
attribute [coe_decl] Coe.coe

class CoeTC (α : Sort u) (β : Sort v) where
  coe : α → β
attribute [coe_decl] CoeTC.coe
instance [Coe β γ] [CoeTC α β] : CoeTC α γ where coe a := Coe.coe (CoeTC.coe a : β)
instance [Coe α β] : CoeTC α β where coe a := Coe.coe a
instance : CoeTC α α where coe a := a

class CoeOut (α : Sort u) (β : semiOutParam (Sort v)) where
  coe : α → β
attribute [coe_decl] CoeOut.coe

class CoeOTC (α : Sort u) (β : Sort v) where
  coe : α → β
attribute [coe_decl] CoeOTC.coe
instance [CoeOut α β] [CoeOTC β γ] : CoeOTC α γ where coe a := CoeOTC.coe (CoeOut.coe a : β)
instance [CoeTC α β] : CoeOTC α β where coe a := CoeTC.coe a
instance : CoeOTC α α where coe a := a

class CoeHead (α : Sort u) (β : semiOutParam (Sort v)) where
  coe : α → β
attribute [coe_decl] CoeHead.coe

class CoeHTC (α : Sort u) (β : Sort v) where
  coe : α → β
attribute [coe_decl] CoeHTC.coe
instance [CoeHead α β] [CoeOTC β γ] : CoeHTC α γ where coe a := CoeOTC.coe (CoeHead.coe a : β)
instance [CoeOTC α β] : CoeHTC α β where coe a := CoeOTC.coe a
instance : CoeHTC α α where coe a := a

class CoeTail (α : semiOutParam (Sort u)) (β : Sort v) where
  coe : α → β
attribute [coe_decl] CoeTail.coe

class CoeHTCT (α : Sort u) (β : Sort v) where
  coe : α → β
attribute [coe_decl] CoeHTCT.coe
instance [CoeTail β γ] [CoeHTC α β] : CoeHTCT α γ where coe a := CoeTail.coe (CoeHTC.coe a : β)
instance [CoeHTC α β] : CoeHTCT α β where coe a := CoeHTC.coe a
instance : CoeHTCT α α where coe a := a

class CoeDep (α : Sort u) (_ : α) (β : Sort v) where
  coe : β
attribute [coe_decl] CoeDep.coe

class CoeT (α : Sort u) (_ : α) (β : Sort v) where
  coe : β
attribute [coe_decl] CoeT.coe
instance [CoeHTCT α β] : CoeT α a β where coe := CoeHTCT.coe a
instance [CoeDep α a β] : CoeT α a β where coe := CoeDep.coe a
instance : CoeT α a α where coe := a

class CoeFun (α : Sort u) (γ : outParam (α → Sort v)) where
  coe : (f : α) → γ f
attribute [coe_decl] CoeFun.coe
instance [CoeFun α fun _ => β] : CoeOut α β where coe a := CoeFun.coe a

class CoeSort (α : Sort u) (β : outParam (Sort v)) where
  coe : α → β
attribute [coe_decl] CoeSort.coe
instance [CoeSort α β] : CoeOut α β where coe a := CoeSort.coe a

-- `Int`, verbatim from `Init/Data/Int/Basic.lean:46-49` minus its
-- `extern` attributes, and the oracle's own worked example of a
-- coercion (`Init/Coe.lean:32`: `instance : Coe Nat Int := ⟨Int.ofNat⟩`).
-- `Big` is a second step so `(n : Big)` needs `CoeTC`'s transitive
-- instance. `genCtorIdx false` for the same reason `Nat`/`List`/`Bool`
-- above carry it.
set_option genCtorIdx false in
inductive Int : Type where
  | ofNat : Nat → Int
  | negSucc : Nat → Int

set_option genCtorIdx false in
inductive Big : Type where
  | ofInt : Int → Big

instance instCoeNatInt : Coe Nat Int := ⟨Int.ofNat⟩
instance instCoeIntBig : Coe Int Big := ⟨Big.ofInt⟩

-- `takesInt` — an ARGUMENT-position coercion (`ensureArgType`,
-- `App.lean:54-62`), distinct from the ascription site.
def takesInt (x : Int) : Int := x

-- `NatAlias` — a SEMIREDUCIBLE alias (a plain `def`), for the `.coe`
-- ladder arm's first branch (`SyntheticMVars.lean:546-551`): `Nat` and
-- `NatAlias` are defeq under `withDefault` but NOT at `.instances`, so
-- the arm assigns `e` itself where a `CoeT Nat e NatAlias` search would
-- answer `.none` (the reflexive instance cannot unfold the alias).
-- Consumed by a smoke test only (design spec § Amendment 5 item 10).
def NatAlias : Type := Nat

-- `Wrapper`/`pairW` — the POSTPONED-then-resumed coercion. In
-- `pairW n Nat.zero`, `n : Nat` meets expected type `Wrapper ?a` while
-- `?a` is unassigned: `CoeT Nat n (Wrapper ?a)` is `.undef` (the search
-- would have to assign the read-only `?a`), so `mkCoe` registers a
-- `.coe` mvar; the second argument assigns `?a := Nat`; the fixpoint's
-- `.coe` arm then coerces. Without the arm, the record is a seam error.
structure Wrapper (a : Type) where
  val : a

instance instCoeNatWrapper : Coe Nat (Wrapper Nat) := ⟨Wrapper.mk⟩

def pairW {a : Type} (x : Wrapper a) (y : a) : Wrapper a := x

-- `Fn` — a `CoeFun` carrier for `synthesizePendingAndNormalizeFunType`'s
-- `coerceToFunction? s.f` (`App.lean:378-380`): `g Nat.zero` with
-- `g : Fn` is not a function application until `Fn.f g` is.
structure Fn where
  f : Nat → Nat

instance instCoeFunFn : CoeFun Fn (fun _ => Nat → Nat) := ⟨Fn.f⟩

-- `Carrier` — a `CoeSort` carrier for `ensureType`
-- (`TermElabM.lean:1935-1949`): a binder domain `(x : c)` with
-- `c : Carrier` is a type only after `Carrier.ty c`.
structure Carrier where
  ty : Type

instance instCoeSortCarrier : CoeSort Carrier Type := ⟨Carrier.ty⟩
```

- [ ] **Step 2: Regenerate and check the corpus did not move**

```bash
mise run fixtures:regen 2>&1 | tee /tmp/claude-1000/-workspace/dac4073b-f7e4-4765-a43e-af6f8b0b6a69/scratchpad/regen-task6.log
grep -n 'failed\|error' /tmp/claude-1000/-workspace/dac4073b-f7e4-4765-a43e-af6f8b0b6a69/scratchpad/regen-task6.log
git status --short
git diff --stat tests/fixtures/elab/elab-queries.jsonl
```

Expected: `Elab0.lean` compiles; `git status` lists ONLY `Elab0.lean`
and `Elab0.olean`; `elab-queries.jsonl` has NO diff (107 records
byte-identical on the oracle side). A record that moved on the oracle
side means a fixture declaration changed an existing elaboration
(e.g. an instance now resolves differently) — find which and rename or
remove the culprit; do not re-baseline.

- [ ] **Step 3: Run the elab tier**

```bash
cargo test -p leanr_elab
```

Expected: PASS — `oracle_elab` replays 107 records identically over the
larger environment; `seam_audit.rs`'s fixture scans (which name only
`elab_as_elim`/`elab_without_expected_type`) are unaffected by
`attribute [coe_decl]`.

- [ ] **Step 4: Commit**

```bash
mise run ci
git add tests/fixtures/elab/Elab0.lean tests/fixtures/elab/Elab0.olean
git commit -F - <<'MSG'
M4b-3 P4 task 6: the coercion chain in Elab0.lean (no new records)

semiOutParam, the verbatim Init/Coe.lean:131-287 chain, Int, Big,
NatAlias, Wrapper/pairW, Fn, Carrier and their instances. A pure
regression gate: all 107 committed records byte-identical on both
sides; the mechanisms and their records land in tasks 7-9.

Claude-Session: https://claude.ai/code/session_01P6daLFfQsqbKWFUWVvJqZs
MSG
```

---

### Task 7: `mk_coe`, `ensure_has_type`, the `.coe` ladder arm, and the first four records

`TermElabM.lean:1294-1322` (`mkCoe`) and `:1334-1340` (`ensureHasType`)
in a new `leanr_elab/src/coe.rs`; the ladder's `Coe` arm
(`SyntheticMVars.lean:545-560`) and the reporter's (`:304-310`); the
three open-coded mismatch sites rewired (A5 items 7–8). Records:
`coe/natToInt`, `coe/twoStep`, `coe/argPosition`,
`coe/postponedThenResumed`.

**Files:**
- Create: `crates/leanr_elab/src/coe.rs`
- Modify: `crates/leanr_elab/src/lib.rs` (`pub mod coe;`), `src/error.rs` (`StuckCoercion`), `src/elab.rs:293-307`, `src/builtin/ascription.rs:141-149`, `src/app/args.rs:863-885`, `src/synthetic/ladder.rs` (the `Coe` arm at `:322-324` after Task 3's renumbering), `src/synthetic/report.rs:97-99`
- Modify: `tests/fixtures/elab/dump_elab.lean` (`coeQueries` + the `main` concatenation), regenerate `elab-queries.jsonl`
- Modify: `crates/leanr_elab/tests/oracle_elab.rs:154` (`CORPUS_FLOOR` 107 → 111)
- Test: `crates/leanr_elab/tests/synthetic_smoke.rs`, `tests/app_smoke.rs`

**Interfaces:**
- Consumes: `MetaCtx::coerce`, `LOption`, `with_transparency`, `check_occurs`, `MetaError::{Unsupported, CoeExpansionMismatch}`; `TermElabM::mk_fresh_expr_mvar_of_kind`, `register_synthetic_mvar`, `SyntheticMVarKind::Coe { expected_type, e }`.
- Produces: `TermElabM::mk_coe(&mut self, stx: &SynElem, expected: ExprId, e: ExprId) -> Result<ExprId, ElabError>`;
  `TermElabM::ensure_has_type(&mut self, stx: &SynElem, expected: Option<ExprId>, e: ExprId) -> Result<ExprId, ElabError>`;
  `TermElabM::synthesize_coe_mvar(&mut self, mvar_id: MVarId, expected: ExprId, e: ExprId) -> Result<bool, ElabError>` (`pub(crate)`);
  `ElabError::StuckCoercion { expected: ExprId, got: ExprId }`.

- [ ] **Step 1: Add the four queries and regenerate**

In `tests/fixtures/elab/dump_elab.lean`, before `def emit`, add (with a
doc block in the style of `outParamQueries`'s):

```lean
/-- M4b-3 P4 (design spec § P4, § Amendment 5 items 9-10): coercion
insertion. Every coerced value is a `fun` binder — the dumper elaborates
closed terms only.
  * `coe/natToInt` — `(n : Int)` with `n : Nat`: `ensureHasType` →
    `mkCoe` → `CoeT Nat n Int` → `expandCoe` → `Int.ofNat n`. Dies if
    `expand_coe` is the identity (the term would carry `CoeT.coe`).
  * `coe/twoStep` — `(n : Big)`: solvable only through `CoeTC`'s
    transitive instance; emits `Big.ofInt (Int.ofNat n)`.
  * `coe/argPosition` — `takesInt n`: the `ensureArgType` site
    (`App.lean:54-62`), not the ascription site. Dies if `args.rs`'s
    rewire is reverted (`TypeMismatch`).
  * `coe/postponedThenResumed` — `pairW n Nat.zero`: `CoeT Nat n
    (Wrapper ?a)` is `.undef` at the first argument (`?a` unassigned),
    so `mkCoe` registers a `.coe` mvar; the second argument assigns
    `?a := Nat`; the entry point's fixpoint resumes the coercion
    (`SyntheticMVars.lean:552-560`). Dies if the ladder's `Coe` arm is
    reverted to its seam.
  * `coe/funApp` (task 8) — `g Nat.zero` with `g : Fn`:
    `coerceToFunction?` in `synthesizePendingAndNormalizeFunType`.
  * `coe/sortDomain` (task 9) — `fun (c : Carrier) (x : c) => x`:
    `ensureType` → `coerceToSort?` on the binder domain. -/
def coeQueries : List (String × String) :=
  [ ("coe/natToInt",             "fun (n : Nat) => (n : Int)")
  , ("coe/twoStep",              "fun (n : Nat) => (n : Big)")
  , ("coe/argPosition",          "fun (n : Nat) => takesInt n")
  , ("coe/postponedThenResumed", "fun (n : Nat) => pairW n Nat.zero")
  ]
```

and append `++ coeQueries` to `main`'s concatenation (`:610`).

```bash
mise run fixtures:regen-elab 2>&1 | grep -i 'failed\|error'
grep -c '' tests/fixtures/elab/elab-queries.jsonl        # 111
grep '"id":"coe/' tests/fixtures/elab/elab-queries.jsonl | cut -c1-200
```

Expected: 111 records, none dropped, the four `coe/*` records present.
Confirm by eye that `coe/natToInt`'s `exp` is a `lam` whose body is
`app(const Int.ofNat, bvar 0)` — NO `CoeT.coe`, NO `proj` — and that
`coe/postponedThenResumed`'s body is `pairW Nat (Wrapper.mk Nat n) Nat.zero`
(canonical form). A dropped query means the fixture candidate does not
survive the oracle (A5 item 9's rule): replace the candidate so the
REQUIREMENT it serves is met, and record what changed.

- [ ] **Step 2: Run the gate to verify the four new records fail**

```bash
cargo test -p leanr_elab --test oracle_elab
```

Expected: the four `coe/*` records fail — `coe/natToInt`, `coe/twoStep`,
`coe/argPosition` with `TypeMismatch`, `coe/postponedThenResumed` with
the ladder seam's `UnsupportedSyntax`. The 107 others pass.

- [ ] **Step 3: Write the failing smoke tests**

Append to `crates/leanr_elab/tests/synthetic_smoke.rs`:

```rust
/// The `.coe` ladder arm's FIRST branch (`SyntheticMVars.lean:546-551`,
/// M4b-3 P4): when the types have become defeq under `withDefault`
/// since the coercion was postponed, the mvar is assigned `e` ITSELF —
/// no synthesis, no expansion. `Nat` vs `NatAlias` (a semireducible
/// alias) is the discriminating shape: defeq at `Default`, NOT at
/// `Instances`, so the second branch's `CoeT Nat e NatAlias` search
/// would answer `.none` (design spec § Amendment 5 item 10). Kill:
/// drop the first branch and this mvar stays unassigned / the ladder
/// reports `StuckCoercion`.
#[test]
fn coe_arm_assigns_e_itself_when_types_became_defeq() {
    support::with_app_harness("Nat.zero", |app| {
        let kinds = support::any_kinds();
        let zero = support::fixture_const(app, "Nat.zero");
        let alias = support::fixture_const(app, "NatAlias");
        let (mv, id) = app
            .elab
            .mk_fresh_expr_mvar_of_kind(alias, leanr_meta::MVarKind::SyntheticOpaque)
            .expect("mvar");
        app.elab.register_synthetic_mvar(
            support::any_syn_elem(),
            id,
            leanr_elab::synthetic::state::SyntheticMVarKind::Coe {
                expected_type: alias,
                e: zero,
            },
        );
        app.elab
            .synthesize_synthetic_mvars_no_postponing(&kinds)
            .expect("the arm assigns without searching");
        let got = app.elab.mctx.instantiate_mvars(mv).expect("inst");
        assert_eq!(got, zero, "assigned to `e` itself, not to an expansion");
    });
}

/// The `.coe` arm's SECOND branch (`:552-560`) coerces once the
/// expected type is known, and the reporter's `.coe` arm (`:304-310`)
/// names a coercion that never became solvable. `pairW n` alone leaves
/// `?a` unassigned forever: `CoeT Nat n (Wrapper ?a)` is `.undef` at
/// registration AND at every retry, so the fixpoint ends with the
/// `.coe` mvar pending and the reporter raises `StuckCoercion` — the
/// oracle's `throwTypeMismatchError … "failed to create type class
/// instance for …"`. The dumper drops this query on the oracle side
/// (an error), which is why it is a smoke test and not a record.
#[test]
fn stuck_coercion_is_reported_by_the_coe_reporter_arm() {
    match support::elab_and_synthesize("fun (n : Nat) => pairW n") {
        Err(leanr_elab::ElabError::StuckCoercion { .. }) => {}
        other => panic!("expected StuckCoercion, got {other:?}"),
    }
}
```

If `SyntheticMVarKind` is not reachable at
`leanr_elab::synthetic::state::SyntheticMVarKind`, use the path
`synthetic_smoke.rs` already imports it from (grep `SyntheticMVarKind`
in that file).

- [ ] **Step 4: Run them to verify they fail**

```bash
cargo test -p leanr_elab --test synthetic_smoke coe_arm_assigns_e_itself_when_types_became_defeq stuck_coercion_is_reported_by_the_coe_reporter_arm
```

Expected: the first fails with the ladder seam's `UnsupportedSyntax`
("coercion synthetic mvars require coercion insertion — M4b-3 P4"); the
second fails on `no variant StuckCoercion`.

- [ ] **Step 5: Add the error variant and `coe.rs`**

`crates/leanr_elab/src/error.rs`, after `StuckSyntheticMVar`:

```rust
    /// oracle: the stuck reporter's `.coe` arm (`SyntheticMVars.lean:304-310`)
    /// — `throwTypeMismatchError header expectedType (← inferType e) e f?
    /// "failed to create type class instance for {mvar type}"`. A
    /// distinct variant from `TypeMismatch` (which `mkCoe`'s IMMEDIATE
    /// failure keeps, `TermElabM.lean:1317,1322`) so a test can tell
    /// "stuck" from "impossible". The mvar's type IS `expected`.
    StuckCoercion {
        expected: ExprId,
        got: ExprId,
    },
```

Create `crates/leanr_elab/src/coe.rs`:

```rust
//! oracle: `mkCoe` (`Lean/Elab/Term/TermElabM.lean:1294-1322`),
//! `ensureHasType` (`:1334-1340`), `ensureType` (`:1935-1949`, task 9)
//! and the `.coe` arm of `synthesizeSyntheticMVar`
//! (`Lean/Elab/SyntheticMVars.lean:545-560`) — the elaborator half of
//! M4b-3 P4. The Meta half is `leanr_meta::coe` (`Lean/Meta/Coe.lean`).
//!
//! Dropped, with no term impact: `withTraceNode`, `pushInfoLeaf`'s
//! `CoeExpansionTrace`, `withoutMacroStackAtErr`, and the
//! `errorMsgHeader?`/`mkErrorMsg?`/`mkImmedErrorMsg?`/`f?` message
//! payloads (leanr defers the prose layer, design spec § Amendment item 2).

use leanr_kernel::bank::ExprId;
use leanr_meta::{LOption, MVarId, MVarKind, MetaError, TransparencyMode};

use crate::dispatch::SynElem;
use crate::elab::TermElabM;
use crate::error::ElabError;
use crate::synthetic::state::SyntheticMVarKind;

impl<'e> TermElabM<'e> {
    /// oracle: `mkCoe` (`TermElabM.lean:1294-1322`) — `coerceCollectingNames?`;
    /// `.some eNew` is the answer (`:1301-1306`); `.none` is `failure`,
    /// caught into `throwTypeMismatchError` (`:1307`, `:1322`); `.undef`
    /// mints a `syntheticOpaque` mvar of the expected type and registers
    /// it as `.coe` (`:1308-1311`). A `MetaM` error inside the coercion
    /// (`Coe.lean`'s post-expansion throws, `MetaError::CoeExpansionMismatch`)
    /// is caught into the same `throwTypeMismatchError` (`:1313-1317`),
    /// so it lands as `TypeMismatch` here too. The monad-lift guard's
    /// `MetaError::Unsupported` is NOT caught: it is a named seam and
    /// surfaces as `UnsupportedSyntax` (design spec § Amendment 5 item 6).
    pub fn mk_coe(&mut self, stx: &SynElem, expected: ExprId, e: ExprId) -> Result<ExprId, ElabError> {
        match self.mctx.coerce(e, expected) {
            Ok(LOption::Some(new_e)) => Ok(new_e),
            Ok(LOption::None) | Err(MetaError::CoeExpansionMismatch(_)) => {
                let got = self.mctx.infer_type(e)?;
                Err(ElabError::TypeMismatch { expected, got })
            }
            Ok(LOption::Undef) => {
                let (mvar, id) = self.mk_fresh_expr_mvar_of_kind(expected, MVarKind::SyntheticOpaque)?;
                self.register_synthetic_mvar(
                    stx.clone(),
                    id,
                    SyntheticMVarKind::Coe {
                        expected_type: expected,
                        e,
                    },
                );
                Ok(mvar)
            }
            Err(MetaError::Unsupported(m)) => Err(ElabError::UnsupportedSyntax(m)),
            Err(err) => Err(ElabError::from(err)),
        }
    }

    /// oracle: `ensureHasType` (`TermElabM.lean:1334-1340`) — `none`
    /// expected type returns `e`; otherwise `isDefEq (← inferType e)
    /// expectedType` or `mkCoe`. Replaces the M4b-1 posture (error on a
    /// defeq mismatch) at every site that used to open-code it:
    /// `elab_term_ensuring_type`, the `($e :)` ascription arm, and
    /// `elab_and_add_new_arg` (`ensureArgType`, `App.lean:54-62`).
    pub fn ensure_has_type(&mut self, stx: &SynElem, expected: Option<ExprId>, e: ExprId) -> Result<ExprId, ElabError> {
        let Some(expected) = expected else {
            return Ok(e);
        };
        let e_type = self.mctx.infer_type(e)?;
        if self.mctx.is_def_eq(e_type, expected)? {
            return Ok(e);
        }
        self.mk_coe(stx, expected, e)
    }

    /// oracle: the `.coe` arm of `synthesizeSyntheticMVar`
    /// (`SyntheticMVars.lean:545-560`). First, under `withDefault`,
    /// `isDefEq (← inferType e) expectedType` — "types may be defeq now
    /// due to mvar assignments, type class defaulting, etc." — and, if
    /// the occurs check passes, assign `e` ITSELF (`:546-551`; no
    /// search, no expansion). Otherwise `coerceCollectingNames?`; on
    /// `.some coerced` with a passing occurs check, assign it (`:552-558`).
    /// Else `false`: not ready yet (`:559`). `check_occurs` answers `true`
    /// when the mvar does NOT occur — the oracle's `occursCheck` polarity
    /// (see its doc at `leanr_meta::MetaCtx::check_occurs`).
    pub(crate) fn synthesize_coe_mvar(&mut self, mvar_id: MVarId, expected: ExprId, e: ExprId) -> Result<bool, ElabError> {
        let e_type = self.mctx.infer_type(e)?;
        let defeq = self
            .mctx
            .with_transparency(TransparencyMode::Default, |m| m.is_def_eq(e_type, expected))?;
        if defeq && self.mctx.check_occurs(mvar_id, e)? {
            self.mctx.mctx_mut().assign(mvar_id, e)?;
            return Ok(true);
        }
        match self.mctx.coerce(e, expected) {
            Ok(LOption::Some(coerced)) => {
                if self.mctx.check_occurs(mvar_id, coerced)? {
                    self.mctx.mctx_mut().assign(mvar_id, coerced)?;
                    return Ok(true);
                }
                Ok(false)
            }
            Ok(LOption::None) | Ok(LOption::Undef) => Ok(false),
            // The oracle has no `try` here: a post-expansion throw
            // propagates as the elaboration error it is.
            Err(MetaError::CoeExpansionMismatch(_)) => Err(ElabError::TypeMismatch {
                expected,
                got: e_type,
            }),
            Err(MetaError::Unsupported(m)) => Err(ElabError::UnsupportedSyntax(m)),
            Err(err) => Err(ElabError::from(err)),
        }
    }
}
```

Add `pub mod coe; // M4b-3 P4` to `crates/leanr_elab/src/lib.rs`
beside the other module lines.

- [ ] **Step 6: Wire the arm, the reporter, and the three sites**

`src/synthetic/ladder.rs`, the `Coe` arm of `synthesize_synthetic_mvar`:

```rust
            SyntheticMVarKind::Coe { expected_type, e } => {
                self.synthesize_coe_mvar(mvar_id, expected_type, e)
            }
```

`src/synthetic/report.rs:97-99`:

```rust
            SyntheticMVarKind::Coe { expected_type, e } => {
                let got = self.mctx.infer_type(e)?;
                Err(ElabError::StuckCoercion {
                    expected: expected_type,
                    got,
                })
            }
```

`src/elab.rs:293-307` — the body of `elab_term_ensuring_type` becomes:

```rust
        let e = self.elab_term(elem, kinds, expected)?;
        self.ensure_has_type(elem, expected, e)
```

(and its doc gains: "oracle: `elabTermEnsuringType` = `elabTerm` then
`ensureHasType` (`TermElabM.lean`); coercion-inserting since M4b-3 P4").

`src/builtin/ascription.rs:141-149` — the `None` arm's `if let Some(t) =
expected { … TypeMismatch … }` block becomes:

```rust
            elab.ensure_has_type(e, expected, e_val)
```

where `e` is the term's `SynElem` in that function (rename the local if
the two `e`s collide). Update the arm's comment: `ensureHasType
expectedType? e` (`:435`) now inserts a coercion.

`src/app/args.rs:863-885` — `elab_and_add_new_arg` becomes:

```rust
    let expected = app.get_arg_expected_type()?;
    let stx = match &arg {
        Arg::Stx(elem) => elem.clone(),
        Arg::Expr(_) => app.ctx.stx.clone(),
    };
    let val = match arg {
        Arg::Expr(e) => e,
        Arg::Stx(elem) => app.elab.elab_term(&elem, kinds, Some(expected))?,
    };
    // oracle: `ensureArgType` = `ensureHasType expectedType arg none f`
    // (`App.lean:54-62`); its `errToSorry` recovery arm is prose leanr
    // does not do, so the `try … catch` collapses to the plain call.
    let val = app.elab.ensure_has_type(&stx, Some(expected), val)?;
    add_new_arg(app, val)
```

Delete the three now-dead `TypeMismatch` constructions. `TypeMismatch`
itself stays (it is what `mk_coe` raises); update its doc in
`error.rs:16-17` to say so.

- [ ] **Step 7: Run everything**

```bash
cargo test -p leanr_elab
```

Expected: PASS — the four records now agree (`oracle_elab` at 111 once
`CORPUS_FLOOR` is raised to 111 in `tests/oracle_elab.rs:154`; do that
now), both new smoke tests pass, and every pre-existing test is green.
If `coe_arm_assigns_e_itself_when_types_became_defeq` fails with an
`UnsupportedSyntax`, the harness's `Nat.zero` head elaborated a
`Postponed` mvar first — check `pending_mvars` and, if so, register
the `Coe` mvar after clearing the harness's own pending list.

- [ ] **Step 8: Measure the discriminators**

Apply each mutation, run the named test, confirm RED, revert:

- `expand_coe` returns `Ok(e)` → `coe/natToInt`, `coe/twoStep`,
  `coe/argPosition`, `coe/postponedThenResumed` (all four emit
  `CoeT.coe`).
- `elab_term_ensuring_type` restored to the M4b-1 `TypeMismatch` → `coe/natToInt`, `coe/twoStep`.
- `elab_and_add_new_arg` restored → `coe/argPosition`, `coe/postponedThenResumed`.
- the ladder `Coe` arm returns `Ok(false)` unconditionally → `coe/postponedThenResumed` (reported as `StuckCoercion`), `coe_arm_assigns_e_itself_when_types_became_defeq`.
- `synthesize_coe_mvar`'s first branch replaced by `if false` → `coe_arm_assigns_e_itself_when_types_became_defeq` (the search at `Instances` answers `.none` on `NatAlias`).
- the reporter arm restored to its seam → `stuck_coercion_is_reported_by_the_coe_reporter_arm`.

- [ ] **Step 9: Commit**

```bash
mise run ci
git add crates/leanr_elab tests/fixtures/elab/dump_elab.lean tests/fixtures/elab/elab-queries.jsonl
git commit -F - <<'MSG'
M4b-3 P4 task 7: mk_coe, ensure_has_type, the .coe ladder arm, four records

TermElabM.lean:1294-1340 in leanr_elab/src/coe.rs; SyntheticMVars.lean
:545-560 as the ladder's Coe arm and :304-310 as StuckCoercion; the
three open-coded mismatch sites (elab_term_ensuring_type, the ($e :)
ascription arm, elab_and_add_new_arg) route through ensure_has_type.
Records coe/natToInt, coe/twoStep, coe/argPosition,
coe/postponedThenResumed; the 107 prior records byte-identical.

Mutations measured: <fill in from step 8>.

Claude-Session: https://claude.ai/code/session_01P6daLFfQsqbKWFUWVvJqZs
MSG
```

---

### Task 8: `coerce_to_function` in `synthesizePendingAndNormalizeFunType`

`App.lean:378-380`: when the function's type does not reduce to a
`forall` after synthesis, try `coerceToFunction? s.f` and, on success,
replace `f` and `fType` and let the state machine continue. The seam at
`args.rs:120-127` retargets to P5 alone.

**Files:**
- Modify: `crates/leanr_elab/src/app/args.rs:104-134`
- Modify: `tests/fixtures/elab/dump_elab.lean` (`coeQueries`), regenerate `elab-queries.jsonl`; `tests/oracle_elab.rs` (`CORPUS_FLOOR` → 112)
- Test: `crates/leanr_elab/tests/seam_audit.rs:167-176` (`mvar_function_type_is_a_named_seam`)

**Interfaces:**
- Consumes: `MetaCtx::coerce_to_function`, `AppElab::f_type_is_forall`, `State::{f, f_type}`.

- [ ] **Step 1: Add the record and regenerate**

Append to `coeQueries`:

```lean
  , ("coe/funApp", "fun (g : Fn) => g Nat.zero")
```

```bash
mise run fixtures:regen-elab 2>&1 | grep -i 'failed\|error'
grep '"id":"coe/funApp"' tests/fixtures/elab/elab-queries.jsonl | cut -c1-240
```

Expected: 112 records; `coe/funApp`'s body is `app(app(const Fn.f, bvar 0), const Nat.zero)`.

- [ ] **Step 2: Run the gate to verify the record fails**

```bash
cargo test -p leanr_elab --test oracle_elab
```

Expected: `coe/funApp` fails with `FunctionExpected` (the type `Fn` is
not a `forall` and not an mvar); the 111 others pass.

- [ ] **Step 3: Rewire the site**

`crates/leanr_elab/src/app/args.rs`, in `synthesize_pending_and_normalize_fun_type`,
replace everything from the `// oracle: \`coerceToFunction? s.f\` (:378) — M4b-3 P4.`
comment through the mvar seam with:

```rust
    // oracle: `if let some f ← coerceToFunction? s.f then modify fun s
    // => { s with f, fType }` (`App.lean:378-380`) — the state machine's
    // `main` loop re-tests `fTypeIsForall` on the new `fType` and
    // proceeds (M4b-3 P4).
    let f = app.st.f;
    match app.elab.mctx.coerce_to_function(f) {
        Ok(Some(f2)) => {
            let f_type = app.elab.mctx.infer_type(f2)?;
            app.st.f = f2;
            app.st.f_type = f_type;
            return Ok(());
        }
        Ok(None) => {}
        Err(leanr_meta::MetaError::Unsupported(m)) => return Err(ElabError::UnsupportedSyntax(m)),
        Err(e) => return Err(ElabError::from(e)),
    }
    // The oracle's remaining arms are diagnostics: a deprecated-argument
    // linter, `throwInvalidNamedArg` (which needs `foundNamedArgs`
    // rendering leanr does not do), and the "Function expected" error.
    // Only the last changes control flow, so only it is ported.
    let f_type = app.st.f_type;
    if app.f_type_is_mvar_after_instantiation()? {
        return Err(ElabError::UnsupportedSyntax(
            "function type is still an unassigned metavariable after synthesis: needs \
             expected-type propagation into `fun` binder domains for the M4b-2 `fun` \
             shape — M4b-3 P5"
                .to_string(),
        ));
    }
```

(the `FunctionExpected` return that follows is unchanged). If
`f_type_is_forall` caches a whnf'd `f_type` in a field other than
`st.f_type`, reset that field here too — read `state.rs:129-150`.

- [ ] **Step 4: Update the seam test and run**

`tests/seam_audit.rs:167-176`: the assertion becomes
`msg.contains("M4b-3 P5")` only, with the doc updated to say the
`CoeFun` half landed in P4 and only the `fun`-binder propagation is
still owed. Then:

```bash
cargo test -p leanr_elab
```

Expected: PASS at `CORPUS_FLOOR = 112`.

- [ ] **Step 5: Measure, then commit**

Mutation: make `coerce_to_function`'s call site `Ok(None)` unconditionally
→ `coe/funApp` red (`FunctionExpected`). Revert.

```bash
mise run ci
git add crates/leanr_elab tests/fixtures/elab/dump_elab.lean tests/fixtures/elab/elab-queries.jsonl
git commit -F - <<'MSG'
M4b-3 P4 task 8: coerceToFunction? in synthesizePendingAndNormalizeFunType

App.lean:378-380: a non-forall function type is coerced through CoeFun
before the state machine continues; the P4 half of the mvar seam is
retired and the message names P5 alone. Record coe/funApp; 111 prior
records byte-identical. Mutation measured: call site forced to None ->
coe/funApp FunctionExpected.

Claude-Session: https://claude.ai/code/session_01P6daLFfQsqbKWFUWVvJqZs
MSG
```

---

### Task 9: `ensure_type` and the `CoeSort` binder domain

`binder.rs`'s `elab_type` documents itself as "`elabType t` … then
ensure-is-type" and implements only the first half, letting
`elab_term_ensuring_type`'s `isDefEq` stand in for `ensureType`
(`TermElabM.lean:1935-1949`). That is exact until a domain can be COERCED
to a sort (A5 item 8). Since Task 7 the stand-in routes through
`ensure_has_type`, which happens to reach `CoeSort` via the
`[CoeSort α β] : CoeOut α β` instance — a coincidence, not the oracle's
path; this task replaces it with the real `ensureType`.

**Files:**
- Modify: `crates/leanr_elab/src/coe.rs` (append `ensure_type`), `src/error.rs` (`TypeExpected`), `src/builtin/binder.rs:24-36`
- Modify: `tests/fixtures/elab/dump_elab.lean` (`coeQueries`), regenerate `elab-queries.jsonl`; `tests/oracle_elab.rs` (`CORPUS_FLOOR` → 113)
- Test: `crates/leanr_elab/tests/binder_smoke.rs`

**Interfaces:**
- Produces: `TermElabM::ensure_type(&mut self, stx: &SynElem, e: ExprId) -> Result<ExprId, ElabError>`; `ElabError::TypeExpected { e: ExprId, ty: ExprId }`.

- [ ] **Step 1: Add the record and regenerate**

Append to `coeQueries`:

```lean
  , ("coe/sortDomain", "fun (c : Carrier) (x : c) => x")
```

```bash
mise run fixtures:regen-elab 2>&1 | grep -i 'failed\|error'
grep '"id":"coe/sortDomain"' tests/fixtures/elab/elab-queries.jsonl | cut -c1-260
```

Expected: 113 records; the record's second binder's domain is
`app(const Carrier.ty, bvar 0)`.

- [ ] **Step 2: Write the failing smoke test**

Append to `crates/leanr_elab/tests/binder_smoke.rs`:

```rust
/// `ensureType` (`TermElabM.lean:1935-1949`, M4b-3 P4 task 9): a binder
/// domain that is neither a `Sort` nor unifiable with one, and has no
/// `CoeSort` instance, is "type expected" — a distinct error from the
/// value-level `TypeMismatch`, because the oracle's `elabType` never
/// calls `ensureHasType`. `Nat.zero : Nat` is such a domain.
#[test]
fn non_type_binder_domain_without_coe_sort_is_type_expected() {
    match elab_result("fun (x : Nat.zero) => x") {
        Err(leanr_elab::ElabError::TypeExpected { .. }) => {}
        other => panic!("expected TypeExpected, got {other:?}"),
    }
}
```

`elab_result` is whatever `binder_smoke.rs`'s existing error-path
helper is called (grep `expect_err` there); if it only has the
panicking `elab_json`, add a `Result`-returning twin beside it.

- [ ] **Step 3: Run them to verify they fail**

```bash
cargo test -p leanr_elab --test oracle_elab
cargo test -p leanr_elab --test binder_smoke non_type_binder_domain_without_coe_sort_is_type_expected
```

Expected: `coe/sortDomain` — either a `TypeMismatch`-shaped failure or,
via the Task-7 stand-in, an accidental pass (record the observed
outcome; the smoke test is the load-bearing discriminator here);
the smoke test fails on the missing variant.

- [ ] **Step 4: Implement**

`src/error.rs`, after `FunctionExpected`:

```rust
    /// oracle: `ensureType`'s "type expected, got …"
    /// (`TermElabM.lean:1946-1949`). Raised from `binder.rs`'s
    /// `elab_type` since M4b-3 P4; before that a non-type domain was
    /// (wrongly) a value-level `TypeMismatch` against `Sort ?u`.
    TypeExpected {
        e: ExprId,
        ty: ExprId,
    },
```

`src/coe.rs`, inside the `impl`:

```rust
    /// oracle: `ensureType` (`TermElabM.lean:1935-1949`) — `isType e`
    /// (`InferType.lean:502-508`: the type `whnfD`s to a `Sort`); else
    /// `isDefEq eType (Sort ?u)` with a fresh level mvar; else
    /// `coerceToSort?`; else "type expected". The `hasSyntheticSorry`
    /// `throwAbortTerm` branch (`:1947`) has no producer here (leanr has
    /// no `sorry` recovery).
    pub fn ensure_type(&mut self, _stx: &SynElem, e: ExprId) -> Result<ExprId, ElabError> {
        let ty = self.mctx.infer_type(e)?;
        let w = self
            .mctx
            .with_transparency(TransparencyMode::Default, |m| m.whnf(ty))?;
        let base = self.view.store;
        if matches!(
            self.mctx.store().expr_node(Some(base), w),
            leanr_kernel::bank::terms::Node::Sort { .. }
        ) {
            return Ok(e);
        }
        let u = self.mk_fresh_level_mvar()?;
        let sort_u = self
            .mctx
            .store_mut()
            .expr_sort(None, u)
            .map_err(MetaError::from)?;
        if self.mctx.is_def_eq(ty, sort_u)? {
            return Ok(e);
        }
        match self.mctx.coerce_to_sort(e) {
            Ok(Some(coerced)) => Ok(coerced),
            Ok(None) => Err(ElabError::TypeExpected { e, ty }),
            Err(MetaError::CoeExpansionMismatch(_)) => Err(ElabError::TypeExpected { e, ty }),
            Err(MetaError::Unsupported(m)) => Err(ElabError::UnsupportedSyntax(m)),
            Err(err) => Err(ElabError::from(err)),
        }
    }
```

`src/builtin/binder.rs:24-36` — `elab_type` becomes:

```rust
    let u = elab.mk_fresh_level_mvar()?;
    let sort = elab
        .mctx
        .store_mut()
        .expr_sort(None, u)
        .map_err(leanr_meta::MetaError::from)?;
    // oracle: `elabType stx = elabTerm stx (mkSort ?u)` then `ensureType`
    // (`TermElabM.lean:1951-1954`) — the second half is real since M4b-3
    // P4 task 9; before that `elab_term_ensuring_type`'s `isDefEq` stood
    // in for it, which is exact only while no domain can be coerced.
    let e = elab.elab_term(elem, kinds, Some(sort))?;
    elab.ensure_type(elem, e)
```

- [ ] **Step 5: Run everything**

```bash
cargo test -p leanr_elab
```

Expected: PASS at `CORPUS_FLOOR = 113`. Any pre-existing test that
asserted `TypeMismatch` for a non-type binder domain now sees
`TypeExpected`; update its expectation (grep `TypeMismatch` under
`crates/leanr_elab/tests`) — that is the corrected oracle error class,
not a regression.

- [ ] **Step 6: Measure, then commit**

Mutation: `ensure_type` returns `Err(TypeExpected)` instead of calling
`coerce_to_sort` → `coe/sortDomain` red. Mutation: `elab_type` restored
to `elab_term_ensuring_type` → `non_type_binder_domain_without_coe_sort_is_type_expected`
red (`TypeMismatch` instead). Revert both.

```bash
mise run ci
git add crates/leanr_elab tests/fixtures/elab/dump_elab.lean tests/fixtures/elab/elab-queries.jsonl
git commit -F - <<'MSG'
M4b-3 P4 task 9: ensure_type and the CoeSort binder domain

TermElabM.lean:1935-1949 as TermElabM::ensure_type; binder.rs's
elab_type gains the half it documented but lacked; TypeExpected replaces
the value-level TypeMismatch on a non-type domain. Record
coe/sortDomain; 112 prior records byte-identical. Mutations measured:
coerce_to_sort skipped -> coe/sortDomain; elab_type restored ->
non_type_binder_domain_without_coe_sort_is_type_expected.

Claude-Session: https://claude.ai/code/session_01P6daLFfQsqbKWFUWVvJqZs
MSG
```

---

### Task 10: retire the seam ledger entries and gate that they stay retired

The three P4 seams are real code; every ledger, index and doc comment
that still says "M4b-3 P4" as an OWNER is reconciled, and a textual gate
pins that the retired seam wording never returns
(`no_seam_points_at_the_retired_p2b_ii_label`'s pattern).

**Files:**
- Modify: `crates/leanr_elab/src/dispatch.rs:144` (deferred table row), `src/lib.rs:93-96` (the coercions bullet), `src/app/mod.rs:52` and `:84-92` (index row + the seam paragraph), `src/app/state.rs:182` (doc), `src/synthetic/state.rs:46-51` (doc), `src/synthetic/default_inst.rs:86,199-201` (docs), `src/error.rs:16-17` (`TypeMismatch` doc, if Task 7 did not already), `crates/leanr_elab/tests/app_smoke.rs:1327-1330` (the stale `coeM` sentence PR #35 recorded), `tests/seam_audit.rs:1-30` (header) and a new gate

- [ ] **Step 1: Write the failing gate**

Append to `crates/leanr_elab/tests/seam_audit.rs`, after
`no_seam_points_at_the_retired_p2b_ii_label`:

```rust
/// M4b-3 P4 RETIRED three seams — the ladder's `Coe` arm, the reporter's
/// `Coe` arm, and the `CoeFun` half of `synthesize_pending_and_normalize_fun_type`'s
/// mvar seam — and rewired every `TypeMismatch`-on-defeq-failure site
/// through `mk_coe`. Their messages read "… coercion insertion — M4b-3
/// P4" and "needs CoeFun (M4b-3 P4)". Mirrors the retired-label gates
/// above and inherits their stated precondition: a TEXTUAL scan is a
/// floor (the retired wording never comes back), not a ceiling.
#[test]
fn no_seam_points_at_the_retired_p4_label() {
    let src_dir = concat!(env!("CARGO_MANIFEST_DIR"), "/src");
    let needles = ["coercion insertion — M4b-3 P4", "needs CoeFun (M4b-3 P4)"];
    let mut offenders = Vec::new();
    for path in walk_rs_files(src_dir) {
        let text = std::fs::read_to_string(&path).expect("readable source");
        for (n, line) in text.lines().enumerate() {
            if needles.iter().any(|needle| line.contains(needle)) {
                offenders.push(format!("{}:{}", path.display(), n + 1));
            }
        }
    }
    assert!(
        offenders.is_empty(),
        "P4 retired the coercion seams (real bodies in `coe.rs`, `ladder.rs`, \
         `report.rs`, `app/args.rs`); stale label at {offenders:?}"
    );
}
```

- [ ] **Step 2: Run it**

```bash
cargo test -p leanr_elab --test seam_audit no_seam_points_at_the_retired_p4_label
```

Expected: PASS already if Tasks 7–8 deleted the messages cleanly; FAIL
listing any leftover line. Either way, proceed to reconcile the docs.

- [ ] **Step 3: Reconcile the ledgers and docs**

- `dispatch.rs:144`: replace the `coercions (CoeT / CoeFun / CoeSort,
  mkCoe) . M4b-3 P4` row with nothing, and extend the "Reconciled …"
  paragraph above the table: "Reconciled a FOURTH time by M4b-3 P4:
  coercion insertion landed (`coe.rs`, the ladder's `Coe` arm,
  `ensure_type`) and is no longer deferred either."
- `lib.rs:93-96`: rewrite the coercions bullet: "**coercions** — SHIPPED
  in M4b-3 P4 (`coe.rs`: `mk_coe` / `ensure_has_type` / `ensure_type`;
  the ladder's `Coe` arm). Still deferred: `coerceMonadLift?` (the
  do-notation slice; a shape guard in `leanr_meta::coe` names it) and
  the `↑`/`⇑`/`↥` notations (the parser slice that adds them)."
- `app/mod.rs:52`: the index row becomes `coercions (CoeT/CoeFun/CoeSort,
  mkCoe) ........... P4 SHIPPED — coe.rs, args.rs`; `:84-92`: replace
  the "P4 coercion seam is a `TypeMismatch`" paragraph with one sentence
  saying the seam was retired in P4 and `TypeMismatch` is now only
  `mk_coe`'s immediate failure.
- `app/state.rs:182`, `synthetic/state.rs:46-51`, `default_inst.rs:86`,
  `:199-201`: change "not yet ported"/"P4 produces"/"that is P2b/P4" to
  past tense with the file that holds the code.
- `tests/app_smoke.rs:1327-1330`: replace "`Elab0.lean` does not declare
  `Lean.Internal.coeM` until task 5 … `false` end-to-end today" with
  "`Elab0.lean` declares `Lean.Internal.coeM` (P2b-ii task 5), so
  `elab_app_aux` computes the flag `true`; the harness forces it here
  regardless so the test does not depend on the fixture".
- `tests/seam_audit.rs:1-30` header: delete the "P4 coercion seam"
  bullet and its "used to be a third unreachable row" analogue: state
  that coercions are real code exercised by `tests/oracle_elab.rs`'s
  `coe/*` records and `tests/synthetic_smoke.rs`.

Then grep for any remaining forward reference:

```bash
grep -rn 'M4b-3 P4' crates/leanr_elab/src crates/leanr_meta/src | grep -v 'shipped\|SHIPPED\|task [0-9]\|design spec'
```

Expected: no line naming P4 as a future owner.

- [ ] **Step 4: Run the whole workspace and commit**

```bash
mise run ci
git add crates/leanr_elab crates/leanr_meta
git commit -F - <<'MSG'
M4b-3 P4 task 10: retire the coercion seam ledger entries

Every ledger/index/doc that named P4 as an owner reconciled to the
shipped code; no_seam_points_at_the_retired_p4_label pins the retired
wording out; PR #35's stale coeM comment in app_smoke.rs fixed.

Claude-Session: https://claude.ai/code/session_01P6daLFfQsqbKWFUWVvJqZs
MSG
```

Then open the PR per the repository's standing workflow (branch, push,
PR titled `M4b-3 P4: coercions`, merge on green CI, verify, delete the
branch).

---

## Verification summary

After Task 10, these must all hold:

- `mise run test` — green, including `oracle_elab` at 113 records: the
  107 pre-existing ones byte-identical across every task (including the
  fixture chain landing in Task 6), plus `coe/natToInt`, `coe/twoStep`,
  `coe/argPosition`, `coe/postponedThenResumed`, `coe/funApp`,
  `coe/sortDomain`; and `oracle_synth` at 24 compared records: the 18
  pre-existing ones byte-identical plus `coeChain/synth/0..3`,
  `coeFun/synth/0`, `coeSort/synth/0`.
- `mise run ci` — green (`cargo fmt --check` + clippy included).
- `git diff` against the merge base touches `leanr_meta` only
  additively (Tasks 2–5: two new modules, `LOption`/`try_synth_instance`,
  `with_transparency`/`whnf_r`/`mk_arrow`, one `MetaError` variant, one
  `EnvExtensions` field, `is_coe_decl`), `leanr_olean` only additively
  (Task 2), and no `leanr_kernel` file.
- Every mechanism this plan adds has a test that goes red when it is
  mutated, and each was MEASURED (Tasks 5.6, 7.8, 8.5, 9.6):
  `expand_coe` → `coerce_simple_expands_*`, `coe/natToInt`, `coe/twoStep`;
  the resolver's diamond path → `coeChain/synth/1`;
  `coerce`'s dispatch order → `coerce_prefers_coe_fun_under_a_forall_expected_type`;
  the monad-lift guard → `monad_lift_guard_fires_only_when_the_env_declares_monad`;
  `elab_term_ensuring_type` / ascription rewire → `coe/natToInt`, `coe/twoStep`;
  the `args.rs` rewire → `coe/argPosition`;
  the ladder `Coe` arm → `coe/postponedThenResumed`, `coe_arm_assigns_e_itself_when_types_became_defeq`;
  the arm's first branch → `coe_arm_assigns_e_itself_when_types_became_defeq`;
  the reporter arm → `stuck_coercion_is_reported_by_the_coe_reporter_arm`;
  `coerce_to_function` at the app site → `coe/funApp`;
  `ensure_type` → `coe/sortDomain`, `non_type_binder_domain_without_coe_sort_is_type_expected`.
- No source line under `crates/leanr_elab/src` contains
  `coercion insertion — M4b-3 P4` or `needs CoeFun (M4b-3 P4)`.

## What this plan deliberately does NOT do

- **No `coerceMonadLift?` port.** The guard (Task 5) names the
  do-notation slice on the only shape the oracle's function can answer;
  `Lean.Internal.coeM` stays an existence-only axiom (§ Seams).
- **No `↑x` / `⇑x` / `↥x` notations.** Not parsed by leanr; the parser
  slice that adds them owns `elabCoe` / `elabCoeFunNotation` /
  `elabCoeSortNotation` (A5 item 13).
- **No error-message prose** — `errorMsgHeader?`, `mkErrorMsg?`,
  `f?`, `CoeExpansionTrace`, `recordExtraModUseFromDecl` (A5 items 5, 7).
- **No mctx-depth model.** `try_synth_instance`'s residues 2 and 3 keep
  their owner; the pre-test moves, unchanged (A5 item 3).
- **No drop guard** on `with_transparency` or
  `with_assignable_synthetic_opaque` (§ Follow-ups item 4 stays
  `leanr_meta`'s).
- **No `lean-toolchain` bump, no workflow change, no spec edit** — the
  post-P4 "Next step" update is the next amendment's, as before.
