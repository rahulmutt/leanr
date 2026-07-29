# M4b-3 P2b-i — outParam support inside synthesis: implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Port the oracle's output-parameter mechanism — `preprocess`,
`preprocessOutParam`, `assignOutParams` — into `leanr_meta`'s synthesis
entry point, so an `outParam` argument left as a metavariable by the
caller is *assigned as a result of synthesis* exactly as the pinned
oracle assigns it.

**Architecture:** Three layers, each with an existing in-repo precedent.
`leanr_olean` grows a `Lean.classExtension` decode (`ClassEntry` =
name + `outParams` + `outLevelParams`) beside the existing
`instanceExtension` arm. `leanr_meta` grows a `ClassTable` built once in
`MetaCtx::new` beside `InstanceTable::build`, and `synth.rs`'s
`synth_instance_main` takes the oracle's own three-part shape:
`preprocess` before the snapshot, `preprocess_out_param` inside it, and a
new `apply_abstract_result` — open the answer, then `assign_out_params` —
*after* it. That last placement is the whole feature: leanr's
`checkpoint`/`rollback` pair is its stand-in for `withNewMCtxDepth`, and
the oracle assigns the caller's mvar only after the depth block closes.

**Tech Stack:** Rust (workspace crates `leanr_olean`, `leanr_meta`),
Lean 4 fixtures (`prelude`-mode, import-free), `mise` task runner,
`serde_json` for the differential corpora.

## Global Constraints

Copied from the spec (`docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md`,
§ Global constraints and § Amendment 3) and `AGENTS.md`. Every task's
requirements implicitly include this section.

- **Pinned oracle: `leanprover/lean4:v4.33.0-rc1`** (`lean-toolchain`).
  Every citation in this plan is against that toolchain's sources, found
  locally at
  `/home/dev/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/`.
  **Never bump the pin.**
- **Kernel is byte-untouched.** `leanr_kernel` depends on no workspace
  crate and no existing kernel function is modified.
- **`leanr_meta/src` is widened for this plan, and only as scoped here:**
  the control flow of `MetaCtx::synth_instance_main`, new private helpers
  in `synth.rs`, a `ClassTable` reached through `MetaCtx::new`, and the
  two `pub` class accessors. No other `leanr_meta` path changes behavior.
- **`leanr_elab` is not modified except for doc comments** (Task 9), which
  retarget ownership notes that this plan makes stale.
- **`leanr_olean` decoders are untrusted-input parsers.** They must never
  panic on arbitrary bytes (`docs/THREAT_MODEL.md`); no existing decode
  path changes. Never truncate a decoded `Nat` with `as usize` — use
  `Nat::to_usize()` and treat overflow as a shape error, matching
  `default_instance_entry`.
- **Named seams, never silent divergence.** Where the oracle does
  something this plan does not implement, detect the shape and return
  `MetaError::Unsupported(..)` naming the seam and its owner.
- **Correctness is byte-for-byte agreement with the pinned oracle**, via
  the committed corpora. Never re-baseline a record to make a test pass:
  a record that moves means the code is wrong.
- **`mise run ci` gates `cargo fmt --check` and clippy**, not only tests.
  Run it before every commit; the test tasks alone do not cover it.
- **Fixture regeneration is `mise run fixtures:regen`** (rebuilds
  `Instances.olean`, `Synth0.olean`, `Elab0.olean` and re-runs the
  dumpers). It needs the pinned Lean toolchain on `PATH`.
- **Determinism:** no wall-clock, no `maxHeartbeats`; leanr counts
  deterministic `MetaCtx::step`s.

## File Structure

**Created:**
- none — every change lands in an existing file, following that file's
  established pattern.

**Modified:**
- `tests/fixtures/Instances.lean` — the outParam declaration block
  (Task 1). Consumed by `leanr_olean`'s decode tests and by
  `leanr_meta`'s `with_instances_ctx` unit tests.
- `tests/fixtures/meta/Synth0.lean` — the same block, plus `Dual`
  (Task 1). Consumed by the differential gate.
- `tests/fixtures/Instances.olean`, `tests/fixtures/meta/Synth0.olean`,
  `tests/fixtures/meta/synth-queries.jsonl` — regenerated artifacts.
- `crates/leanr_olean/src/module_data.rs` — `ClassEntry` struct +
  `ModuleData::classes` (Task 2).
- `crates/leanr_olean/src/interp_id.rs` — the `Lean.classExtension`
  decode arm + `class_entry` (Task 2).
- `crates/leanr_meta/src/metactx.rs` — `EnvExtensions` (Task 3),
  `ClassTable` wiring + the two class accessors (Task 4).
- `crates/leanr_meta/src/instances.rs` — `ClassTable` lives here beside
  `InstanceTable` (Task 4).
- `crates/leanr_meta/src/synth.rs` — `preprocess` (Task 5),
  `preprocess_out_param` (Task 6), `apply_abstract_result` /
  `assign_out_params` / the narrowed snapshot (Task 7), seam-doc
  retargeting (Task 9).
- `crates/leanr_meta/src/test_support.rs` — `with_instances_ctx` and
  friends move to `EnvExtensions` (Task 3).
- `crates/leanr_meta/tests/support/mod.rs`,
  `crates/leanr_meta/tests/oracle_fast.rs`,
  `crates/leanr_meta/tests/oracle_synth.rs`,
  `crates/leanr_meta/tests/synth_sweep.rs`,
  `crates/leanr_elab/src/elab.rs`, `crates/leanr_elab/src/app/head.rs`,
  `crates/leanr_elab/tests/**` — `MetaCtx::new` call sites (Task 3).
- `tests/fixtures/meta/dump_synth.lean` — pre-synthesis goal encoding +
  the `assigns` field (Task 8), the new queries (Task 9).
- `crates/leanr_meta/tests/oracle_synth.rs` — `assigns` comparison
  (Task 8), `compared` count (Task 9).
- `crates/leanr_elab/src/synthetic/ladder.rs`,
  `crates/leanr_elab/src/lib.rs` — doc comments only (Task 9).

## Orientation for the implementer

Read these before Task 1. They are short and they are what the code below
mirrors.

- **The oracle's entry point:** `SynthInstance.lean:960-1010`
  (`synthInstanceCore?`), `:737-773` (`preprocess`), `:775-817`
  (`preprocessOutParam`), `:847-861` (`assignOutParams`), `:877-925`
  (`applyAbstractResult?`), and `Class.lean:11-31,76-88` (`ClassEntry`
  and its accessors).
- **leanr's counterpart:** `crates/leanr_meta/src/synth.rs:1595-1690`
  (`synth_instance` / `synth_instance_main` / `synth_instance_body`) and
  `:1511-1544` (`open_abstract_mvars_result`).
- **The spec:** § P2b-i and § Amendment 3 of
  `docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md`.

**The one mental model that matters.** leanr has no mctx-depth model.
Where the oracle runs the search under `withNewMCtxDepth` so the caller's
metavariables are read-only inside it, leanr wraps the search in
`checkpoint` / `rollback` so that whatever the search assigned is
*discarded* afterwards. Both achieve "the search cannot leave assignments
on the caller's mvars". The consequence for this plan: `assign_out_params`
must run **after** the rollback, in the caller's frame, or its assignment
is thrown away with everything else — and the corpus cannot see the
difference until Task 8 adds the `assigns` field.

---

### Task 1: outParam fixture declarations

The fixtures gain outParam classes but **no new queries** — the queries
land in Task 9, once the engine can answer them. This task's deliverable
is that the two `.olean`s contain an outParam class and that regenerating
the synthesis corpus leaves every committed record byte-identical.

**Files:**
- Modify: `tests/fixtures/Instances.lean` (append at end of file)
- Modify: `tests/fixtures/meta/Synth0.lean` (append at end of file)
- Regenerate: `tests/fixtures/Instances.olean`,
  `tests/fixtures/meta/Synth0.olean`,
  `tests/fixtures/meta/synth-queries.jsonl`

**Interfaces:**
- Produces: Lean constants `outParam`, `Op`, `instOpN`, `Lvl`,
  `instLvlN`, `Get`, `instGetN` in both fixtures, and `Dual` in
  `Synth0` only. Every later task names these.

- [ ] **Step 1: Append the shared block to `tests/fixtures/Instances.lean`**

```lean
-- === M4b-3 P2b-i: outParam classes (design spec § P2b-i) ===
--
-- The FIRST classes in any leanr fixture carrying an `outParam`. Until
-- this block, `getOutParamPositions?` was empty everywhere and the
-- oracle's `preprocessOutParam`/`assignOutParams` were unreachable, so
-- leanr's not having them was invisible (design spec § Amendment 3,
-- item 2).
--
-- `outParam` must be declared here, at the ROOT namespace, because these
-- fixtures are `prelude`-mode and import no `Init`. The oracle's `class`
-- command decides output-parameter positions with
-- `Lean.Expr.isOutParam` (`Expr.lean:1708-1710`), which is
-- `isAppOfArity ``outParam 1` against the ROOT name `outParam` — so this
-- declaration is the real thing, not a look-alike. Copied verbatim from
-- `Init/Prelude.lean:702` of the pin.
@[reducible] def outParam (α : Sort u) : Sort u := α

-- `Op` — the binop shape. Two ordinary parameters and one `outParam`,
-- i.e. `ClassEntry.outParams == #[2]` and `outLevelParams == #[]` (all
-- three parameters share the universe `u`). This is the shape
-- `crates/leanr_elab/src/synthetic/ladder.rs:105-115` cites as a live
-- divergence — the oracle answers `Op N N ?γ` with `?γ := N` assigned,
-- leanr (before this plan) answers `Undef`.
class Op (a : Type u) (b : Type u) (c : outParam (Type u)) where
  op : a → b → c

instance instOpN : Op N N N where
  op := fun _ b => b

-- `Lvl` — a universe that appears ONLY in an output parameter, i.e.
-- `outParams == #[1]` AND `outLevelParams == #[1]` (the universe `v`
-- occurs only in `b`'s type). It is what gives `ClassEntry`'s third
-- field a non-empty producer, and it is the class
-- `preprocessOutParam`'s `preprocessLevels` branch
-- (`SynthInstance.lean:786-795`) runs on.
class Lvl (a : Type u) (b : outParam (Type v)) where
  lvl : a → b

instance instLvlN : Lvl N N where
  lvl := fun a => a

-- `Get` — the `GetElem` shape from the oracle's own worked example
-- (`App.lean:143-146`): two ordinary parameters, one `outParam`, and a
-- method taking both ordinary parameters. M4b-3 P2b-ii needs exactly
-- this shape in `Elab0.lean`; proving it out at the synthesis tier first
-- is why it is here.
class Get (cont : Type u) (idx : Type v) (elem : outParam (Type w)) where
  get : cont → idx → elem

instance instGetN : Get N N N where
  get := fun c _ => c
```

- [ ] **Step 2: Append the same block plus `Dual` to `tests/fixtures/meta/Synth0.lean`**

Append the block from Step 1 verbatim (including its comments — the two
fixtures deliberately share these shapes, as `Synth0.lean`'s own header
records), then append this extra declaration, which `Instances.lean` does
not need:

```lean
-- `Dual` — SEMIREDUCIBLE by construction (a plain `def`, no
-- `@[reducible]`). It exists for one query, `outParamNoMVars/synth/0`
-- (`Op N N (Dual N)`), and it is what makes that query discriminating
-- rather than merely covering. Type class resolution runs at
-- `TransparencyMode.instances`, which cannot unfold `Dual`, so a search
-- against the goal as written fails; the oracle instead replaces the
-- output parameter with a fresh mvar (`preprocessOutParam`, called even
-- on the `.noMVars` path — `SynthInstance.lean:983-1000`, the
-- `OrderDual` note), finds `instOpN`, and then reconciles with
-- `assignOutParams`' `isDefEq` under `withDefault`
-- (`SynthInstance.lean:851`), where `Dual` DOES unfold. Skip either
-- half and the answer flips from `some instOpN` to `none`.
def Dual (a : Type) : Type := a
```

- [ ] **Step 3: Rebuild the fixtures and regenerate the synthesis corpus**

```bash
git status --porcelain tests/fixtures            # expect only the two .lean edits
git stash list                                   # sanity: nothing stashed
cp tests/fixtures/meta/synth-queries.jsonl /tmp/claude-1000/-workspace/synth-queries.before
mise run fixtures:regen
```

- [ ] **Step 4: Verify the committed records did not move**

```bash
diff /tmp/claude-1000/-workspace/synth-queries.before tests/fixtures/meta/synth-queries.jsonl && echo "IDENTICAL"
```

Expected: `IDENTICAL`. New declarations must not perturb existing goals —
they add instances for classes no committed query mentions. **If a record
moved, stop and diagnose**; do not commit a moved record. Then confirm
the whole suite is still green:

```bash
mise run test
```

Expected: PASS. (`Elab0.olean` is rebuilt by the same task; the elab
corpus is untouched by these declarations, so `oracle_elab` must stay
green too.)

- [ ] **Step 5: Commit**

```bash
git add tests/fixtures/Instances.lean tests/fixtures/Instances.olean \
        tests/fixtures/meta/Synth0.lean tests/fixtures/meta/Synth0.olean \
        tests/fixtures/meta/synth-queries.jsonl
git commit -m "M4b-3 P2b-i task 1: outParam classes in the Instances/Synth0 fixtures

First fixture classes carrying an \`outParam\`. Declarations only — the
queries land in task 9, once the engine can answer them. The committed
synth-queries.jsonl records are byte-identical after regen."
```

---

### Task 2: `classExtension` decode

**Files:**
- Modify: `crates/leanr_olean/src/module_data.rs` (add `ClassEntry`
  beside `DefaultInstanceEntry` at `:255-278`; add the `classes` field to
  `ModuleData` at `:361`; add the test)
- Modify: `crates/leanr_olean/src/interp_id.rs` (add the
  `"Lean.classExtension"` arm beside `"Lean.Meta.defaultInstanceExtension"`
  at `:1012`; add `class_entry` beside `default_instance_entry` at `:868`)
- Modify: `crates/leanr_olean/src/lib.rs` (re-export `ClassEntry` — follow
  the existing `DefaultInstanceEntry` re-export line)

**Interfaces:**
- Consumes: Task 1's `Op` / `Lvl` / `Get` constants in `Instances.olean`.
- Produces:
  ```rust
  pub struct ClassEntry {
      pub name: NameId,
      pub out_params: Vec<usize>,
      pub out_level_params: Vec<usize>,
  }
  // and
  pub struct ModuleData { /* ... */ pub classes: Vec<ClassEntry> }
  ```

- [ ] **Step 1: Write the failing test**

Add to `crates/leanr_olean/src/module_data.rs`'s test module, beside the
existing `defaultInstanceExtension` test:

```rust
/// `Lean.classExtension` decodes. The three shapes that matter are all
/// present in `Instances.lean`: a class with no output parameters
/// (`Add`), one whose output parameter is in the LAST position
/// (`Op`, `outParams == #[2]`, no out-level params), and one whose
/// universe appears only in an output parameter (`Lvl`,
/// `outParams == #[1]` AND `outLevelParams == #[1]`). `Op` is what
/// catches a swapped-field decode: `Lvl`'s two arrays are equal, so on
/// its own it could not.
#[test]
fn class_extension_decodes_out_param_positions() {
    let bytes = fixture("Instances.olean");
    let mut env = Environment::default();
    let md = ModuleData::parse(&bytes, env.store_mut()).expect("decode");
    let render = |n: NameId| env.store().to_name(None, Some(n)).to_string();
    let find = |n: &str| {
        md.classes
            .iter()
            .find(|c| render(c.name) == n)
            .unwrap_or_else(|| {
                panic!(
                    "classExtension entry for {n}; decoded: {:?}",
                    md.classes.iter().map(|c| render(c.name)).collect::<Vec<_>>()
                )
            })
    };

    let add = find("Add");
    assert!(add.out_params.is_empty(), "Add out_params: {:?}", add.out_params);
    assert!(add.out_level_params.is_empty());

    let op = find("Op");
    assert_eq!(op.out_params, vec![2], "Op out_params");
    assert!(op.out_level_params.is_empty(), "Op out_level_params: {:?}", op.out_level_params);

    let lvl = find("Lvl");
    assert_eq!(lvl.out_params, vec![1], "Lvl out_params");
    assert_eq!(lvl.out_level_params, vec![1], "Lvl out_level_params");
}
```

The setup lines are copied verbatim from the `defaultInstanceExtension`
test at `module_data.rs:776-781`, which is this test's model.

- [ ] **Step 2: Run the test to verify it fails**

Run: `cargo test -p leanr_olean class_extension_decodes_out_param_positions`
Expected: FAIL — `no field 'classes' on type 'ModuleData'`.

- [ ] **Step 3: Add the entry type and the `ModuleData` field**

In `crates/leanr_olean/src/module_data.rs`, beside `DefaultInstanceEntry`:

```rust
/// One decoded `Lean.classExtension` entry: oracle `Lean.ClassEntry`
/// (`Class.lean:13-31`, pinned toolchain v4.33.0-rc1):
///
/// ```text
/// structure ClassEntry where
///   name           : Name       -- 0
///   outParams      : Array Nat  -- 1
///   outLevelParams : Array Nat  -- 2
/// ```
///
/// THREE fields, not the two the design spec's § P2b originally named
/// (corrected in § Amendment 3, item 5). `outLevelParams` is the set of
/// universe-parameter positions that occur only in output-parameter
/// types; the oracle uses it in `preprocessOutParam`'s level refresh
/// (`SynthInstance.lean:786-795`) and in the synthesis cache key
/// (`:757-763`), and leanr consumes the first but not the second — it
/// has no synthesis cache (named seam, design spec § Seams).
///
/// `classExtension` is a `SimplePersistentEnvExtension`
/// (`Class.lean:69-73`), NOT a `SimpleScopedEnvExtension` like
/// `instanceExtension` — so its entries are a bare, unwrapped array of
/// `ClassEntry`, the same posture as `defaultInstanceExtension` above,
/// and there is no `scope` field here.
#[derive(Debug, Clone)]
pub struct ClassEntry {
    pub name: NameId,
    /// `outParams` (field 1): positions of the class's output
    /// parameters, as computed by the oracle's `checkOutParam`.
    pub out_params: Vec<usize>,
    /// `outLevelParams` (field 2): positions of universe parameters
    /// occurring only in output-parameter types.
    pub out_level_params: Vec<usize>,
}
```

And on `ModuleData`, after `projection_fns`:

```rust
    /// Typed decode of the `Lean.classExtension` entries (M4b-3 P2b-i).
    /// All other extension entries stay opaque.
    pub classes: Vec<ClassEntry>,
```

Then follow the compiler: `ModuleData` is constructed in at least two
places in this file (the single-file `parse` and the multi-part
`parse_parts` merge at `:513-516`); add `classes` to each exactly the way
`default_instances` is handled there (`std::mem::take(&mut base.classes)`
in the merge). Re-export `ClassEntry` from `lib.rs` beside
`DefaultInstanceEntry`.

- [ ] **Step 4: Add the decoder**

In `crates/leanr_olean/src/interp_id.rs`, beside `default_instance_entry`:

```rust
    /// `Lean.ClassEntry` (`Class.lean:13-31`) — three pointer fields,
    /// no scalar tail (`Name`, `Array Nat`, `Array Nat`; no nullary-enum
    /// field like `InstanceEntry.attrKind`). See `crate::ClassEntry`'s
    /// doc for the source confirmation that `classExtension` is a
    /// `SimplePersistentEnvExtension` and therefore carries no
    /// `ScopedEnvExtension.Entry` wrapper.
    fn class_entry(&mut self, r: &Raw) -> Result<crate::ClassEntry, OleanError> {
        // Untrusted-bignum positions: never truncate via `as usize` (the
        // identical posture `default_instance_entry` above takes) — a
        // value too large to fit is a shape error, not silently wrapped.
        fn nat_positions(r: &Raw) -> Result<Vec<usize>, OleanError> {
            array(r)?
                .iter()
                .map(|e| {
                    nat(e)?
                        .to_usize()
                        .ok_or_else(|| bad("ClassEntry position Nat"))
                })
                .collect()
        }
        let (f, _) = ctor(r, 0, 3, "ClassEntry")?;
        Ok(crate::ClassEntry {
            name: self.name_req(&f[0])?,
            out_params: nat_positions(&f[1])?,
            out_level_params: nat_positions(&f[2])?,
        })
    }
```

And the dispatch arm, beside `"Lean.Meta.defaultInstanceExtension"`:

```rust
                // SimplePersistentEnvExtension: entries are bare
                // ClassEntry ctors, no scoped wrapper (same posture as
                // `defaultInstanceExtension` just above) — see
                // `crate::ClassEntry`'s doc for the source confirmation
                // (Class.lean:69-73).
                "Lean.classExtension" => {
                    for e in array(&pf[1])? {
                        classes.push(self.class_entry(e)?);
                    }
                }
```

Declare the `classes` accumulator beside the existing `default_instances`
one in the same function and thread it into the returned `ModuleData`,
exactly as `default_instances` is threaded.

- [ ] **Step 5: Run the test to verify it passes**

Run: `cargo test -p leanr_olean class_extension_decodes_out_param_positions -- --nocapture`
Expected: PASS.

**If it fails with an empty `decoded: []` list, the extension NAME is
wrong, not the ctor shape.** `classExtension` is registered by
`builtin_initialize classExtension : ... ← registerSimplePersistentEnvExtension`
inside `namespace Lean` (`Class.lean:69-73`), and
`registerSimplePersistentEnvExtension` defaults its `name` to
`decl_name%` — hence `Lean.classExtension`. To see the truth rather than
guess, temporarily add `eprintln!("ext: {}", ext_name);` at the top of the
match in `interp_id.rs`'s dispatch loop, re-run with `--nocapture`, read
the printed list, then remove the `eprintln!`.

- [ ] **Step 6: Run the whole crate's tests and commit**

```bash
cargo test -p leanr_olean
mise run ci
git add crates/leanr_olean/src
git commit -m "M4b-3 P2b-i task 2: decode Lean.classExtension (ClassEntry)

Name + outParams + outLevelParams, following defaultInstanceExtension's
unwrapped SimplePersistentEnvExtension posture. Untrusted-input
discipline: positions go through Nat::to_usize, never \`as usize\`."
```

---

### Task 3: group the extension slices into `EnvExtensions`

Pure refactor, no behavior change. It exists so Task 4 adds a struct
field instead of a ninth positional argument across 25 call sites — and
so P4's `coe_decl` extension does not pay that churn again. A reviewer
can reject this task without rejecting the port.

**Files:**
- Modify: `crates/leanr_meta/src/metactx.rs:261-300` (`MetaCtx::new`)
- Modify: `crates/leanr_meta/src/lib.rs` (re-export `EnvExtensions`)
- Modify: every `MetaCtx::new` call site:
  `crates/leanr_meta/src/{test_support.rs,infer.rs,whnf.rs,lazy_delta.rs,defeq.rs,assign.rs}`,
  `crates/leanr_meta/tests/{oracle_fast.rs,oracle_synth.rs,synth_sweep.rs}`,
  `crates/leanr_elab/src/{elab.rs,app/head.rs}`,
  `crates/leanr_elab/tests/{support/mod.rs,binder_smoke.rs,oracle_elab.rs}`

**Interfaces:**
- Produces:
  ```rust
  #[derive(Default, Clone, Copy)]
  pub struct EnvExtensions<'a> {
      pub reducibility: &'a [ReducibilityEntry],
      pub matchers: &'a [MatcherEntry],
      pub instances: &'a [InstanceEntry],
      pub default_instances: &'a [DefaultInstanceEntry],
      pub projection_fns: &'a [ProjectionFnInfo],
  }
  pub fn MetaCtx::new(view, scratch, cfg, exts: EnvExtensions) -> MetaCtx
  ```

- [ ] **Step 1: Add the struct and change the signature**

In `crates/leanr_meta/src/metactx.rs`, above `impl MetaCtx`:

```rust
/// The decoded environment-extension entries `MetaCtx` reads, grouped so
/// adding one is a field rather than a positional parameter across every
/// call site. Introduced by M4b-3 P2b-i, whose `ClassTable` is the sixth
/// such table and whose successor (M4b-3 P4's `coe_decl`) is the
/// seventh; before this the constructor took five bare slices.
///
/// `Default` gives all-empty slices, so a caller that needs only one
/// table writes `EnvExtensions { instances: &insts, ..Default::default() }`.
#[derive(Default, Clone, Copy)]
pub struct EnvExtensions<'a> {
    pub reducibility: &'a [ReducibilityEntry],
    pub matchers: &'a [MatcherEntry],
    pub instances: &'a [InstanceEntry],
    pub default_instances: &'a [DefaultInstanceEntry],
    pub projection_fns: &'a [ProjectionFnInfo],
}
```

Change the constructor to:

```rust
    pub fn new(
        view: EnvView<'e>,
        scratch: &'e mut Store,
        cfg: Config,
        exts: EnvExtensions<'_>,
    ) -> MetaCtx<'e> {
```

and rename the uses in the body (`reducibility` → `exts.reducibility`,
etc.). The body's filtering, `InstanceTable::build` call and
`projection_fns` map construction are otherwise untouched.

- [ ] **Step 2: Update every call site**

`cargo build --workspace` lists them all. The mechanical rewrite is:

```rust
// before
let mut ctx = MetaCtx::new(
    view, &mut scratch, Config::default(),
    &reducibility, &matchers, &instances, &default_instances, &projection_fns,
);
// after
let mut ctx = MetaCtx::new(
    view, &mut scratch, Config::default(),
    EnvExtensions {
        reducibility: &reducibility,
        matchers: &matchers,
        instances: &instances,
        default_instances: &default_instances,
        projection_fns: &projection_fns,
    },
);
```

and for the all-empty sites (e.g. `test_support::with_ctx`):

```rust
let mut ctx = MetaCtx::new(view, &mut scratch, Config::default(), EnvExtensions::default());
```

- [ ] **Step 3: Verify nothing changed behaviorally**

```bash
cargo build --workspace
mise run test
```

Expected: PASS, with no fixture or corpus file modified
(`git status --porcelain tests/` must be empty).

- [ ] **Step 4: Commit**

```bash
mise run ci
git add -A
git commit -m "M4b-3 P2b-i task 3: group MetaCtx::new's extension slices into EnvExtensions

Pure refactor, no behavior change: the ClassTable in task 4 becomes a
struct field rather than a ninth positional argument across 25 call
sites, and M4b-3 P4's coe_decl extension will not pay that churn again."
```

---

### Task 4: `ClassTable` and the class accessors

**Files:**
- Modify: `crates/leanr_meta/src/instances.rs` (add `ClassTable` at the
  end, beside `InstanceTable`)
- Modify: `crates/leanr_meta/src/metactx.rs` (the `classes` field on
  `EnvExtensions` and on `MetaCtx`; the two `pub` accessors beside the
  existing `default_instances` accessor at `:808`)

**Interfaces:**
- Consumes: `leanr_olean::ClassEntry` (Task 2), `EnvExtensions` (Task 3).
- Produces:
  ```rust
  impl<'e> MetaCtx<'e> {
      pub fn get_out_param_positions(&self, class_name: NameId) -> Option<&[usize]>;
      pub fn get_out_level_param_positions(&self, class_name: NameId) -> Option<&[usize]>;
      pub fn has_out_params(&self, class_name: NameId) -> bool;
  }
  ```

- [ ] **Step 1: Write the failing test**

Add to `crates/leanr_meta/src/instances.rs`'s test module:

```rust
    /// oracle: `getOutParamPositions?` / `getOutLevelParamPositions?` /
    /// `hasOutParams` (`Class.lean:76-88`). `Add` is a class with no
    /// output parameters, so it is PRESENT with an empty array — the
    /// oracle's `isClass` is exactly "present in this map"
    /// (`Class.lean:76-77`), and collapsing "absent" into "no out
    /// params" would lose that distinction. `NotAClass` stands for a
    /// name that is not a class at all.
    #[test]
    fn class_table_reads_out_param_positions() {
        with_instances_ctx(|ctx| {
            let op = const_named(ctx, "Op");
            let add = const_named(ctx, "Add");
            let lvl = const_named(ctx, "Lvl");

            assert_eq!(ctx.get_out_param_positions(op), Some(&[2usize][..]));
            assert_eq!(ctx.get_out_level_param_positions(op), Some(&[][..]));
            assert!(ctx.has_out_params(op));

            assert_eq!(ctx.get_out_param_positions(add), Some(&[][..]));
            assert!(!ctx.has_out_params(add), "Add has no out params but IS a class");

            assert_eq!(ctx.get_out_param_positions(lvl), Some(&[1usize][..]));
            assert_eq!(ctx.get_out_level_param_positions(lvl), Some(&[1usize][..]));
        });
    }
```

`const_named` returns an `ExprId`, not a `NameId` — use whatever the
neighbouring tests in this module use to obtain a `NameId` for a string
(see `test_support::render_name`'s inverse, or intern the name directly
via `ctx.scratch`). Match the surrounding style rather than adding a new
helper.

- [ ] **Step 2: Run the test to verify it fails**

Run: `cargo test -p leanr_meta class_table_reads_out_param_positions`
Expected: FAIL — `no method named 'get_out_param_positions'`.

- [ ] **Step 3: Add `ClassTable`**

In `crates/leanr_meta/src/instances.rs`:

```rust
/// The decoded `Lean.classExtension` state. oracle: `ClassState`
/// (`Class.lean:41-45`) — two maps keyed by class name, built once from
/// the module's entries by `ClassState.addEntry` (`:49-53`).
///
/// Built once, from `MetaCtx::new`, exactly like [`InstanceTable`] just
/// above; never per-query. Last-write-wins on a duplicate name, matching
/// `SMap.insert` and the same untrusted-input posture
/// `MetaCtx::new`'s `projection_fns` map documents: a real `.olean`
/// never registers a class twice, so a collision is reachable only via
/// adversarial bytes and must not panic.
#[derive(Default)]
pub(crate) struct ClassTable {
    out_params: HashMap<NameId, Vec<usize>>,
    out_level_params: HashMap<NameId, Vec<usize>>,
}

impl ClassTable {
    pub(crate) fn build(entries: &[ClassEntry]) -> ClassTable {
        let mut out_params = HashMap::new();
        let mut out_level_params = HashMap::new();
        for e in entries {
            out_params.insert(e.name, e.out_params.clone());
            out_level_params.insert(e.name, e.out_level_params.clone());
        }
        ClassTable {
            out_params,
            out_level_params,
        }
    }

    pub(crate) fn out_params(&self, class_name: NameId) -> Option<&[usize]> {
        self.out_params.get(&class_name).map(|v| v.as_slice())
    }

    pub(crate) fn out_level_params(&self, class_name: NameId) -> Option<&[usize]> {
        self.out_level_params.get(&class_name).map(|v| v.as_slice())
    }
}
```

- [ ] **Step 4: Wire it through and add the accessors**

Add `pub classes: &'a [ClassEntry]` to `EnvExtensions`, a
`classes: ClassTable` field to `MetaCtx`, and
`classes: ClassTable::build(exts.classes)` in `MetaCtx::new`. Then, in
`metactx.rs` beside the existing `default_instances` accessor:

```rust
    /// oracle: `getOutParamPositions?` (`Class.lean:79-81`). `Some(&[])`
    /// means "is a class, with no output parameters"; `None` means "not
    /// a class" — the oracle's `isClass` is precisely the `Some`/`None`
    /// distinction (`Class.lean:76-77`), so they must not be collapsed.
    pub fn get_out_param_positions(&self, class_name: NameId) -> Option<&[usize]> {
        self.classes.out_params(class_name)
    }

    /// oracle: `getOutLevelParamPositions?` (`Class.lean:87-88`).
    pub fn get_out_level_param_positions(&self, class_name: NameId) -> Option<&[usize]> {
        self.classes.out_level_params(class_name)
    }

    /// oracle: `hasOutParams` (`Class.lean:83-86`) — a class with a
    /// NON-EMPTY output-parameter array.
    pub fn has_out_params(&self, class_name: NameId) -> bool {
        matches!(self.get_out_param_positions(class_name), Some(p) if !p.is_empty())
    }
```

Finally, thread `classes: md.classes` (or `&classes`) through every
`MetaCtx::new` call site that decodes a real `.olean`:
`test_support.rs`'s `with_instances_ctx` / `with_cyclic_instances_ctx`,
`tests/support/mod.rs`'s `replay_fixture` (add `classes` to the
`Replayed` struct), `synth_sweep.rs`, and `leanr_elab`'s `elab.rs` /
`head.rs` / test support. Sites that pass `EnvExtensions::default()` need
no change.

- [ ] **Step 5: Run the test to verify it passes**

Run: `cargo test -p leanr_meta class_table_reads_out_param_positions`
Expected: PASS.

- [ ] **Step 6: Run the suite and commit**

```bash
mise run test
mise run ci
git add -A
git commit -m "M4b-3 P2b-i task 4: ClassTable + get_out_param_positions accessors

oracle: Class.lean:41-53,76-88. Built once in MetaCtx::new beside
InstanceTable::build. Some(&[]) vs None is the oracle's own isClass
distinction and is preserved."
```

---

### Task 5: `preprocess` — the goal classification

This is the task that changes behavior for **every** synthesis goal, not
only outParam ones: the oracle normalizes the goal before searching and
leanr did not. The regression evidence is that both committed corpora
stay byte-identical.

**Files:**
- Modify: `crates/leanr_meta/src/synth.rs` (add `PreprocessKind`,
  `PreprocessResult`, `preprocess`; call it from `synth_instance_main` at
  `:1599`)

**Interfaces:**
- Consumes: `MetaCtx::get_out_param_positions` /
  `get_out_level_param_positions` (Task 4).
- Produces:
  ```rust
  enum PreprocessKind { NoMVars, MVarsNoOutputParams, MVarsOutputParams }
  struct PreprocessResult { ty: ExprId, kind: PreprocessKind }
  impl<'e> MetaCtx<'e> {
      fn preprocess(&mut self, ty: ExprId) -> Result<PreprocessResult, MetaError>;
  }
  ```

- [ ] **Step 1: Write the failing tests**

Add to `crates/leanr_meta/src/synth.rs`'s test module:

```rust
    /// oracle: `preprocess` (`SynthInstance.lean:737-773`). The three
    /// kinds, one goal each. `Add N` is ground; `Wrap`-style goals do
    /// not exist in this fixture, so the mvars-but-no-out-params case
    /// uses `Add ?a`; `Op N N ?c` is the out-params case.
    #[test]
    fn preprocess_classifies_the_three_kinds() {
        with_instances_ctx(|ctx| {
            let ty = type_sort(ctx);

            let ground = parse_goal(ctx, "Add N");
            assert!(matches!(
                ctx.preprocess(ground).expect("preprocess").kind,
                PreprocessKind::NoMVars
            ));

            let (a, _) = fresh_mvar(ctx, ty);
            let add = const_named(ctx, "Add");
            let no_out = ctx.mk_app_spine(add, &[a]).expect("app");
            assert!(matches!(
                ctx.preprocess(no_out).expect("preprocess").kind,
                PreprocessKind::MVarsNoOutputParams
            ));

            let (c, _) = fresh_mvar(ctx, ty);
            let n = const_named(ctx, "N");
            let op = const_named(ctx, "Op");
            let with_out = ctx.mk_app_spine(op, &[n, n, c]).expect("app");
            assert!(matches!(
                ctx.preprocess(with_out).expect("preprocess").kind,
                PreprocessKind::MVarsOutputParams
            ));
        });
    }

    /// A pi-shaped synthesis goal (`∀ x, C x`) needs
    /// `forallTelescopeReducing` + `mkForallFVars`, which this crate has
    /// no fvar-telescope for at the Meta layer. NAMED SEAM, not a wrong
    /// answer — the same posture `try_resolve`'s forall-shaped-goal seam
    /// already takes (`MetaError::Unsupported`'s own doc cites it).
    #[test]
    fn preprocess_seams_a_pi_shaped_goal() {
        with_instances_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let add_n = parse_goal(ctx, "Add N");
            let pi = ctx.mk_arrow_for_test(n, add_n);
            match ctx.preprocess(pi) {
                Err(MetaError::Unsupported(msg)) => {
                    assert!(msg.contains("forallTelescope"), "seam names the mechanism: {msg}");
                }
                other => panic!("expected a named seam, got {other:?}"),
            }
        });
    }
```

`mk_arrow_for_test` is not an existing helper — build the pi with the
store directly (`ctx.scratch.expr_forall(..)`) the way the neighbouring
tests in this module build binder shapes, or reuse whatever local helper
they already have. Do not add a production `mk_arrow` for a test.

- [ ] **Step 2: Run to verify they fail**

Run: `cargo test -p leanr_meta preprocess_`
Expected: FAIL — `no method named 'preprocess'`.

- [ ] **Step 3: Implement `preprocess`**

In `crates/leanr_meta/src/synth.rs`, above `synth_instance_main`:

```rust
/// oracle: `PreprocessKind` (`SynthInstance.lean:706-716`).
///
/// **The classification is behavior-neutral in this crate today, and
/// that is deliberate rather than dead code.** The oracle branches on
/// it twice: to decide whether to run `preprocessOutParam` (`:983-1002`
/// — every arm but `.mvarsNoOutputParams` does) and to build the
/// synthesis cache key (`:757-763`). For a class with no output
/// parameters `preprocessOutParam` is the identity, so the first branch
/// collapses here; the second has no consumer at all, because this
/// crate has no synthesis cache (NAMED SEAM, design spec § Seams,
/// owner: the slice that builds one). The kind is computed anyway so
/// that the seam is one missing CONSUMER rather than a missing
/// classification — and so that the `cacheKeyType` port, when it lands,
/// is additive.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum PreprocessKind {
    NoMVars,
    MVarsNoOutputParams,
    MVarsOutputParams,
}

/// oracle: `PreprocessResult` (`SynthInstance.lean:718-722`) minus
/// `cacheKeyType`, which has no consumer here (see [`PreprocessKind`]).
struct PreprocessResult {
    ty: ExprId,
    kind: PreprocessKind,
}
```

and the method:

```rust
    /// oracle: `preprocess` (`SynthInstance.lean:737-773`).
    ///
    /// **The telescope reduces to a `whnf`.** The oracle opens
    /// `forallTelescopeReducing type`, `whnf`s the body and rebuilds
    /// with `mkForallFVars`. For a goal with NO leading binders — every
    /// goal any leanr caller produces today — `xs` is empty and the
    /// whole thing is exactly `whnf type`. A pi-shaped goal is a NAMED
    /// SEAM rather than a silent identity: answering it needs an
    /// fvar-telescope this crate does not have at the Meta layer, the
    /// same gap `try_resolve` already seams
    /// (`MetaError::Unsupported`'s own doc).
    fn preprocess(&mut self, ty: ExprId) -> Result<PreprocessResult, MetaError> {
        let ty = self.instantiate_mvars(ty)?;
        let ty = self.whnf(ty)?;
        if matches!(self.node(ty), Node::Forall { .. }) {
            return Err(MetaError::Unsupported(
                "synth_instance: pi-shaped synthesis goal needs forallTelescopeReducing + \
                 mkForallFVars (SynthInstance.lean:740-742); no Meta-layer fvar telescope in \
                 this crate. Owner: the slice that grows one — same seam as `try_resolve`'s \
                 (SynthInstance.lean:351)"
                    .to_string(),
            ));
        }
        if !self.data(ty).has_expr_mvar() {
            return Ok(PreprocessResult {
                ty,
                kind: PreprocessKind::NoMVars,
            });
        }
        // oracle: the `typeBody.isConst` workaround for parameterless
        // classes such as `ToLevel.{u}` (`:744-749`), then the
        // "head is not a constant" and "not a class" fallbacks.
        let head = self.get_app_fn(ty);
        let Node::Const { name, .. } = self.node(head) else {
            return Ok(PreprocessResult {
                ty,
                kind: PreprocessKind::MVarsNoOutputParams,
            });
        };
        if head == ty {
            return Ok(PreprocessResult {
                ty,
                kind: PreprocessKind::MVarsNoOutputParams,
            });
        }
        let out_params = self.get_out_param_positions(name).unwrap_or(&[]).len();
        let out_levels = self.get_out_level_param_positions(name).unwrap_or(&[]).len();
        let kind = if out_params == 0 && out_levels == 0 {
            PreprocessKind::MVarsNoOutputParams
        } else {
            PreprocessKind::MVarsOutputParams
        };
        Ok(PreprocessResult { ty, kind })
    }
```

Note on the `unwrap_or(&[])`: the oracle returns `.mvarsNoOutputParams`
when `getOutParamPositions?` is `none` (`:754`), which is what an empty
slice produces here — the two agree, and folding them keeps the borrow
short.

- [ ] **Step 4: Call it from `synth_instance_main`**

Replace the body of `synth_instance_main` so `preprocess` runs inside the
config scope but outside the snapshot — the oracle's `withConfig`
(`:963-964`) wraps everything while `withNewMCtxDepth` (`:978`) wraps
only `main`:

```rust
    fn synth_instance_main(&mut self, ty: ExprId) -> Result<Option<ExprId>, MetaError> {
        let saved_cfg = self.cfg;
        self.cfg.transparency = TransparencyMode::Instances;
        self.cfg.fo_approx = true;
        self.cfg.ctx_approx = true;
        self.cfg.const_approx = false;
        self.cfg.univ_approx = false;
        let r = self.synth_instance_preprocessed(ty);
        self.cfg = saved_cfg;
        r
    }

    /// The `withConfig` body of `synthInstanceCore?`
    /// (`SynthInstance.lean:965-1006`): preprocess, then run the search
    /// under this crate's `withNewMCtxDepth` stand-in (the
    /// `checkpoint`/`rollback` pair), then apply the result OUTSIDE it.
    fn synth_instance_preprocessed(&mut self, ty: ExprId) -> Result<Option<ExprId>, MetaError> {
        let PreprocessResult { ty, kind: _ } = self.preprocess(ty)?;
        let snap = self.checkpoint();
        let r = self.synth_instance_body(ty);
        self.rollback(snap);
        r
    }
```

Keep the existing long `withConfig` comment block on
`synth_instance_main` where it is — it documents the six config fields
and their seams and none of that changed. Add one line to it recording
that `preprocess` is no longer part of its NAMED SEAM list (Task 9
finishes that edit; leaving it stale for one task is fine, correcting it
here is better).

- [ ] **Step 5: Run to verify the tests pass**

Run: `cargo test -p leanr_meta preprocess_`
Expected: PASS.

- [ ] **Step 6: Verify the regression gate — both corpora unmoved**

```bash
mise run test
```

Expected: PASS, including `oracle_synth` (15 records) and `oracle_elab`
(101 records). **`preprocess` now `whnf`s every synthesis goal, so this
step is the real deliverable of the task.** If a record fails, the port
is wrong — do not regenerate the corpus, and do not add a seam exclusion.
Diagnose by printing the pre- and post-`preprocess` goal for the failing
record.

- [ ] **Step 7: Commit**

```bash
mise run ci
git add crates/leanr_meta/src/synth.rs
git commit -m "M4b-3 P2b-i task 5: preprocess — goal classification + whnf normalization

oracle: SynthInstance.lean:737-773, called from synthInstanceCore?'s
withConfig body. The forallTelescopeReducing/mkForallFVars pair reduces
to a whnf for binder-free goals; a pi-shaped goal is a named seam.
Normalizes EVERY goal, so the gate is both committed corpora staying
byte-identical."
```

---

### Task 6: `preprocess_out_param`

**Files:**
- Modify: `crates/leanr_meta/src/synth.rs` (add `preprocess_out_param`;
  call it from `synth_instance_preprocessed`)

**Interfaces:**
- Consumes: `PreprocessKind` / `PreprocessResult` (Task 5).
- Produces:
  ```rust
  impl<'e> MetaCtx<'e> {
      fn preprocess_out_param(&mut self, ty: ExprId) -> Result<ExprId, MetaError>;
  }
  ```

- [ ] **Step 1: Write the failing tests**

```rust
    /// oracle: `preprocessOutParam` (`SynthInstance.lean:775-817`).
    /// Output-parameter arguments are replaced by FRESH metavariables so
    /// the search never unifies against the caller's term in those
    /// positions; every other argument is untouched.
    #[test]
    fn preprocess_out_param_replaces_output_arguments() {
        with_instances_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let op = const_named(ctx, "Op");
            let goal = ctx.mk_app_spine(op, &[n, n, n]).expect("app");
            let pre = ctx.preprocess_out_param(goal).expect("preprocess_out_param");
            let args = ctx.get_app_args(pre);
            assert_eq!(args.len(), 3);
            assert_eq!(args[0], n, "ordinary parameter untouched");
            assert_eq!(args[1], n, "ordinary parameter untouched");
            assert!(
                matches!(ctx.node(args[2]), Node::MVar { .. }),
                "output parameter replaced by a fresh mvar"
            );
        });
    }

    /// A class with NO output parameters is returned unchanged — the
    /// oracle's `outParamsPos.isEmpty && outLevelParamPos.isEmpty` early
    /// return (`:784`).
    #[test]
    fn preprocess_out_param_is_identity_without_out_params() {
        with_instances_ctx(|ctx| {
            let goal = parse_goal(ctx, "Add N");
            assert_eq!(ctx.preprocess_out_param(goal).expect("identity"), goal);
        });
    }

    /// oracle: `preprocessLevels` (`:786-795`) — universes occurring
    /// ONLY in output-parameter types are refreshed to fresh level
    /// mvars, so a candidate at a different universe can still match.
    /// This is a UNIT test rather than a corpus record on purpose: the
    /// committed record scheme has no `lmvar` case at all
    /// (`dump_synth.lean`'s `encLevel` panics on one, deliberately), so
    /// a goal carrying a level mvar cannot be dumped.
    #[test]
    fn preprocess_out_param_refreshes_out_only_universes() {
        with_instances_ctx(|ctx| {
            let n = const_named(ctx, "N");
            // `Lvl.{0, 0} N N` — universe 1 is `outLevelParams == #[1]`.
            let lvl = const_named_at_levels(ctx, "Lvl", &[0, 0]);
            let goal = ctx.mk_app_spine(lvl, &[n, n]).expect("app");
            let pre = ctx.preprocess_out_param(goal).expect("preprocess_out_param");
            let head = ctx.get_app_fn(pre);
            let Node::Const { levels, .. } = ctx.node(head) else {
                panic!("head stays a constant")
            };
            let base = Some(ctx.view.store);
            let us = ctx.scratch.level_list_at(base, levels);
            assert!(!ctx.is_level_mvar(us[0]), "universe 0 is not out-only: untouched");
            assert!(ctx.is_level_mvar(us[1]), "universe 1 is out-only: refreshed");
        });
    }
```

`const_named_at_levels` and `is_level_mvar` are not existing helpers.
Build the constant with explicit levels using
`ctx.scratch.intern_level_list` + `ctx.scratch.expr_const` (the exact
idiom in `mk_const_with_fresh_mvar_levels`, `synth.rs:2077-2093`), and
test for a level mvar by matching the level node the way
`KeyNormalizer::norm_level` does. Keep both local to the test module.

- [ ] **Step 2: Run to verify they fail**

Run: `cargo test -p leanr_meta preprocess_out_param`
Expected: FAIL — `no method named 'preprocess_out_param'`.

- [ ] **Step 3: Implement it**

```rust
    /// oracle: `preprocessOutParam` (`SynthInstance.lean:775-817`).
    ///
    /// Replaces the caller's terms in output-parameter positions with
    /// fresh metavariables, and refreshes universes that occur only in
    /// output-parameter types. The point is not the substitution itself
    /// but what it buys the caller: the search then never unifies
    /// against the caller's term in those positions, so it can neither
    /// get stuck on it (the oracle's `isDefEqStuckEx` path) nor assign
    /// it eagerly (this crate's, which has no read-only mvars). The
    /// caller's term is reconciled afterwards, by
    /// [`MetaCtx::assign_out_params`].
    ///
    /// The oracle's `forallTelescope` here is the NON-reducing one and
    /// leanr's goals are binder-free by the time `preprocess` has
    /// seamed the pi case, so there is no telescope to open.
    fn preprocess_out_param(&mut self, ty: ExprId) -> Result<ExprId, MetaError> {
        let head = self.get_app_fn(ty);
        let Node::Const { name, levels } = self.node(head) else {
            return Ok(ty);
        };
        if head == ty {
            // oracle: the `typeBody.isConst` workaround (`:780`).
            return Ok(ty);
        }
        let out_params: Vec<usize> = self
            .get_out_param_positions(name)
            .unwrap_or(&[])
            .to_vec();
        let out_levels: Vec<usize> = self
            .get_out_level_param_positions(name)
            .unwrap_or(&[])
            .to_vec();
        if out_params.is_empty() && out_levels.is_empty() {
            return Ok(ty);
        }
        // oracle: `preprocessLevels` (`:786-795`).
        let base = Some(self.view.store);
        let head = if out_levels.is_empty() {
            head
        } else {
            let us = self.scratch.level_list_at(base, levels).to_vec();
            let mut fresh = Vec::with_capacity(us.len());
            for (i, u) in us.into_iter().enumerate() {
                if out_levels.contains(&i) {
                    fresh.push(self.fresh_level_mvar()?.1);
                } else {
                    fresh.push(u);
                }
            }
            let base = Some(self.view.store);
            let levels2 = self.scratch.intern_level_list(base, &fresh)?;
            self.scratch.expr_const(base, name, levels2)?
        };
        if out_params.is_empty() {
            let args = self.get_app_args(ty);
            return self.mk_app_spine(head, &args);
        }
        // oracle: `preprocessArgs` (`:796-812`) — walk the class's own
        // type alongside the arguments so each fresh mvar gets the
        // PARAMETER's type, and instantiate as we go so a later
        // parameter's type sees the earlier substitutions.
        let mut args = self.get_app_args(ty);
        let mut c_type = self.infer_type(head)?;
        for i in 0..args.len() {
            self.step()?;
            c_type = self.whnf(c_type)?;
            let Node::Forall {
                binder_type, body, ..
            } = self.node(c_type)
            else {
                return Err(MetaError::Infer(
                    "preprocess_out_param: type class resolution failed, insufficient number \
                     of arguments (SynthInstance.lean:808)"
                        .to_string(),
                ));
            };
            if out_params.contains(&i) {
                let (m, _) = self.mk_aux_mvar(binder_type)?;
                args[i] = m;
            }
            let base = Some(self.view.store);
            c_type = instantiate(self.scratch, base, body, args[i], &mut self.guard)?;
        }
        self.mk_app_spine(head, &args)
    }
```

Match the `instantiate` import and `self.guard` threading to how
`open_abstract_mvars_result` (`synth.rs:1511-1544`) already does it.

- [ ] **Step 4: Call it from `synth_instance_preprocessed`**

```rust
        let PreprocessResult { ty, kind } = self.preprocess(ty)?;
        let snap = self.checkpoint();
        // oracle: the `withNewMCtxDepth` dispatch (`:983-1002`). Only
        // `.mvarsNoOutputParams` skips `preprocessOutParam` — `.noMVars`
        // runs it too, deliberately (the `OrderDual` note at `:984-999`).
        let searched = match kind {
            PreprocessKind::MVarsNoOutputParams => Ok(ty),
            PreprocessKind::NoMVars | PreprocessKind::MVarsOutputParams => {
                self.preprocess_out_param(ty)
            }
        };
        let r = searched.and_then(|t| self.synth_instance_body(t));
        self.rollback(snap);
        r
```

- [ ] **Step 5: Run to verify the tests pass**

Run: `cargo test -p leanr_meta preprocess_out_param`
Expected: PASS.

- [ ] **Step 6: Verify the corpora are still unmoved, then commit**

```bash
mise run test
mise run ci
git add crates/leanr_meta/src/synth.rs
git commit -m "M4b-3 P2b-i task 6: preprocessOutParam + the out-only universe refresh

oracle: SynthInstance.lean:775-817. Runs on .noMVars too, per the
OrderDual note at :984-999. preprocessLevels is unit-tested rather than
corpus-tested: the committed record scheme has no level-mvar case."
```

---

### Task 7: `apply_abstract_result` and `assign_out_params`

The headline task. `assign_out_params` must run **after** the rollback,
so `open_abstract_mvars_result` moves out of `synth_instance_body`.

**Files:**
- Modify: `crates/leanr_meta/src/synth.rs` (`synth_instance_body`'s
  return type, new `apply_abstract_result` and `assign_out_params`,
  `synth_instance_preprocessed`'s tail)

**Interfaces:**
- Consumes: `preprocess_out_param` (Task 6),
  `open_abstract_mvars_result` (`synth.rs:1511`),
  `with_assignable_synthetic_opaque` (`metactx.rs:992`).
- Produces:
  ```rust
  impl<'e> MetaCtx<'e> {
      fn assign_out_params(&mut self, ty: ExprId, result: ExprId) -> Result<bool, MetaError>;
      fn apply_abstract_result(
          &mut self,
          ty: ExprId,
          r: Option<AbstractMVarsResult>,
      ) -> Result<Option<ExprId>, MetaError>;
  }
  // and `synth_instance_body` now returns Result<Option<AbstractMVarsResult>, MetaError>
  ```

- [ ] **Step 1: Write the failing tests**

```rust
    /// THE headline behavior of M4b-3 P2b-i. oracle: `assignOutParams`
    /// (`SynthInstance.lean:847-861`), called from
    /// `applyAbstractResult?` (`:880`) AFTER `withNewMCtxDepth` has
    /// closed (`:1003-1004`). The caller's `?c` is assigned as a RESULT
    /// of synthesis. Before this task the search's assignments were
    /// discarded wholesale by the rollback, so `?c` came back
    /// unassigned even though the answer was right.
    #[test]
    fn synth_instance_assigns_the_callers_out_param() {
        with_instances_ctx(|ctx| {
            let ty = type_sort(ctx);
            let (c, cid) = fresh_mvar(ctx, ty);
            let n = const_named(ctx, "N");
            let op = const_named(ctx, "Op");
            let goal = ctx.mk_app_spine(op, &[n, n, c]).expect("app");

            let got = ctx.synth_instance(goal).expect("synth").expect("an instance");
            assert_eq!(render_expr(ctx, got), "instOpN");

            let assigned = ctx.instantiate_mvars(c).expect("instantiate");
            assert_eq!(
                render_expr(ctx, assigned),
                "N",
                "?c must be assigned by assignOutParams, not left over from the search"
            );
            let _ = cid;
        });
    }

    /// `assignOutParams` returning FALSE rejects the answer. `NoBase` is
    /// not `N`, so the reconciling `isDefEq` fails and the whole
    /// synthesis answers `none` even though the search found `instOpN`
    /// against the preprocessed goal. A constant-`true`
    /// `assign_out_params` passes every other test in this plan and
    /// fails this one.
    #[test]
    fn synth_instance_rejects_a_result_whose_out_param_does_not_match() {
        with_instances_ctx(|ctx| {
            // `Prod N N`, not `NoBase`: `NoBase` exists only in
            // `Synth0.lean` (where the corpus twin of this test,
            // `outParamReject/synth/0`, uses it), while this unit test
            // runs against `Instances.olean`. `Prod` is in the scaffold
            // both fixtures share, and `Prod N N` is no more `N` than
            // `NoBase` is.
            let goal = parse_goal(ctx, "Op N N (Prod N N)");
            assert!(ctx.synth_instance(goal).expect("synth").is_none());
        });
    }

    /// oracle: `assignOutParams`' `withAssignableSyntheticOpaque`
    /// (`:851`) — "output parameters of local instances may be marked as
    /// `syntheticOpaque` by the application-elaborator". M4b-3 P2b-ii is
    /// what produces such a goal from source; this pins the mechanism
    /// now, at the layer that owns it.
    #[test]
    fn synth_instance_assigns_a_synthetic_opaque_out_param() {
        with_instances_ctx(|ctx| {
            let ty = type_sort(ctx);
            let (c, _) = fresh_mvar_of_kind(ctx, ty, MVarKind::SyntheticOpaque);
            let n = const_named(ctx, "N");
            let op = const_named(ctx, "Op");
            let goal = ctx.mk_app_spine(op, &[n, n, c]).expect("app");

            assert!(ctx.synth_instance(goal).expect("synth").is_some());
            assert_eq!(render_expr(ctx, ctx.instantiate_mvars(c).expect("inst")), "N");
        });
    }
```

`fresh_mvar_of_kind` does not exist — add it beside `fresh_mvar` in
`crates/leanr_meta/src/test_support.rs`, taking an `MVarKind` and
otherwise identical to `fresh_mvar`.

Confirm `Prod` really is in `Instances.lean`'s scaffold before relying on
it (`Synth0.lean`'s header says the two fixtures share their prefix
verbatim through `instOfNN`, which covers the scaffold); if it is not,
substitute any declared type other than `N`.

- [ ] **Step 2: Run to verify they fail**

Run: `cargo test -p leanr_meta synth_instance_assigns synth_instance_rejects`
Expected: FAIL — the first on the `?c` assertion (`?c` is still an
unassigned mvar, so `render_expr` prints the mvar, not `N`).

- [ ] **Step 3: Change `synth_instance_body` to return the abstract result**

```rust
    fn synth_instance_body(
        &mut self,
        ty: ExprId,
    ) -> Result<Option<AbstractMVarsResult>, MetaError> {
        // ... unchanged through the `while` loop ...
        Ok(st.result.take())
    }
```

The `open_abstract_mvars_result` call at the old `:1688` is deleted here
— it moves to `apply_abstract_result`, which runs after the rollback.
Leave `open_abstract_mvars_result` itself untouched.

- [ ] **Step 4: Add `assign_out_params` and `apply_abstract_result`**

```rust
    /// oracle: `assignOutParams` (`SynthInstance.lean:847-861`).
    ///
    /// Reconciles the caller's goal with the answer's actual type, and
    /// this is where the caller's output-parameter metavariables get
    /// assigned — [`MetaCtx::preprocess_out_param`] having kept them out
    /// of the search entirely. It runs OUTSIDE the search's
    /// `checkpoint`/`rollback` pair, which is this crate's stand-in for
    /// the oracle's `withNewMCtxDepth`; inside it, the assignment would
    /// be rolled back with everything else.
    ///
    /// Two config overrides, both load-bearing and both taken verbatim
    /// from the oracle:
    ///
    /// - `withDefault` (`:851`): the reconciling `isDefEq` runs at
    ///   DEFAULT transparency, not the `.instances` transparency the
    ///   search itself uses, so a semireducible definition standing
    ///   between the goal and the answer still unfolds. The oracle's own
    ///   note records that removing it broke thousands of `OrderDual`
    ///   sites in Mathlib.
    /// - `withAssignableSyntheticOpaque` (`:851`): output parameters of
    ///   local instances may be marked `syntheticOpaque` by the
    ///   application elaborator (M4b-3 P2b-ii), and this `isDefEq` must
    ///   be allowed to assign them anyway.
    fn assign_out_params(&mut self, ty: ExprId, result: ExprId) -> Result<bool, MetaError> {
        let result_type = self.infer_type(result)?;
        let saved = self.cfg.transparency;
        self.cfg.transparency = TransparencyMode::Default;
        let r = self.with_assignable_synthetic_opaque(|ctx| ctx.is_def_eq(ty, result_type));
        self.cfg.transparency = saved;
        r
    }

    /// oracle: `applyAbstractResult?` (`SynthInstance.lean:877-925`).
    ///
    /// **Its tail is a NAMED SEAM.** After `assignOutParams` the oracle
    /// runs `checkMayHaveSideEffects` and, if it says yes, `check
    /// result` — a full type check whose purpose is to propagate
    /// universe constraints the search derived but `withNewMCtxDepth`
    /// discarded (issue #796, `:891-923`). This crate has no
    /// `Lean.Meta.check`, and `leanr_check` sits ABOVE it, so the pair
    /// cannot be ported here. Owner: the slice that grows a Meta-layer
    /// `check` (design spec § Seams). The consequence is
    /// incompleteness on universe-polymorphic answers whose universe is
    /// determined only by the search, never a wrong assignment.
    fn apply_abstract_result(
        &mut self,
        ty: ExprId,
        r: Option<AbstractMVarsResult>,
    ) -> Result<Option<ExprId>, MetaError> {
        let Some(abst) = r else { return Ok(None) };
        let result = self.open_abstract_mvars_result(&abst)?;
        if !self.assign_out_params(ty, result)? {
            return Ok(None);
        }
        Ok(Some(self.instantiate_mvars(result)?))
    }
```

- [ ] **Step 5: Rewire `synth_instance_preprocessed`**

```rust
    fn synth_instance_preprocessed(&mut self, ty: ExprId) -> Result<Option<ExprId>, MetaError> {
        let PreprocessResult { ty, kind } = self.preprocess(ty)?;
        let snap = self.checkpoint();
        let searched = match kind {
            PreprocessKind::MVarsNoOutputParams => Ok(ty),
            PreprocessKind::NoMVars | PreprocessKind::MVarsOutputParams => {
                self.preprocess_out_param(ty)
            }
        };
        let abst = searched.and_then(|t| self.synth_instance_body(t));
        // The rollback is this crate's `withNewMCtxDepth` boundary: the
        // answer survives it because `mk_answer` already abstracted it
        // (`abstract_mvars`), and everything below runs OUTSIDE it so
        // `assign_out_params` can assign the caller's mvars for real.
        self.rollback(snap);
        self.apply_abstract_result(ty, abst?)
    }
```

Note the ordering: `rollback` runs on the error path too, so `abst?` is
unwrapped only after it. Update `synth_instance`'s doc comment
(`synth.rs:1556-1570`), which currently states that the returned term
"survives that rollback" because it is metavariable-free — still true,
but now say where `assign_out_params` sits relative to the pair.

- [ ] **Step 6: Run to verify the tests pass**

Run: `cargo test -p leanr_meta synth_instance_`
Expected: PASS, all three new tests plus the existing `synth.rs` suite.

- [ ] **Step 7: Verify the corpora are still unmoved, then commit**

```bash
mise run test
```

Expected: PASS. `oracle_synth`'s 15 records and `oracle_elab`'s 101 must
still be green: no committed query has an mvar in an output-parameter
position (no fixture class had an `outParam` before Task 1, and Task 1
added no queries), so this task must not move any of them.

```bash
mise run ci
git add crates/leanr_meta/src/synth.rs crates/leanr_meta/src/test_support.rs
git commit -m "M4b-3 P2b-i task 7: applyAbstractResult + assignOutParams after the rollback

oracle: SynthInstance.lean:847-861, 877-925. The search's
checkpoint/rollback pair is this crate's withNewMCtxDepth stand-in, so
assign_out_params runs outside it — that placement is what lets the
caller's outParam mvar be assigned as a RESULT of synthesis.
checkMayHaveSideEffects + check stay a named seam (no Meta.check here)."
```

---

### Task 8: the `assigns` record field

Until this lands, the corpus cannot see Task 7 at all: `Op N N ?γ` and a
version of leanr that leaves `?γ` unassigned produce the *same* committed
record. This task also fixes a dumper panic that Task 9's queries would
otherwise hit.

**Files:**
- Modify: `tests/fixtures/meta/dump_synth.lean` (module header, the
  `encGoalAndMVars` block, the record fields)
- Modify: `crates/leanr_meta/tests/oracle_synth.rs` (compare `assigns`)
- Regenerate: `tests/fixtures/meta/synth-queries.jsonl`

**Interfaces:**
- Produces: every record gains `"assigns": [{"i":<N>,"e":<E>}]`, encoded
  in the same `EncSt` as `goal` / `mvars[].t` / `val`, an absent entry
  meaning "still unassigned".

- [ ] **Step 1: Encode the goal BEFORE synthesis**

`dump_synth.lean`'s `encGoalAndMVars` currently runs *after*
`synthInstance?` and **panics** if a goal mvar was assigned during the
call ("likely got ASSIGNED during synthesis; a corpus record cannot
honestly report an index for it"). That panic was correct when nothing
could assign a goal mvar; `assignOutParams` now does, by design. Move the
`goal`/`mvars` encode to before the `synthInstance?` call:

```lean
      let goal ← mkGoal
      let goalMVars := (← getMVars goal)
      -- `goal` and `mvars[].t` are encoded BEFORE synthesis: they record
      -- the query AS ASKED. Post-synthesis state belongs in `assigns`
      -- below, not smuggled into `goal` — and an output parameter the
      -- oracle assigns (`assignOutParams`, SynthInstance.lean:847-861)
      -- would otherwise vanish from `goal` entirely and take the
      -- `mvars[].i` numbering with it. Every record committed before
      -- M4b-3 P2b-i is byte-identical either way: no query in the corpus
      -- at that point could assign a goal mvar.
      let (goalJ, st0) := (encExpr (← instantiateMVars goal)).run {}
      let (mvarsJ, st1) ← goalMVars.foldlM (fun (acc, st) (m : MVarId) => do
        let ty ← instantiateMVars (← m.getType)
        let (tyJ, st') := (encExpr ty).run st
        let idx := match st'.mvars.get? m with
          | some i => i
          | none => panic! s!"dump_synth: mvar {m.name} not numbered by `goal` (collected by \
              getMVars before synthInstance? but not reachable from the pre-synthesis goal)"
        pure (acc.push (Json.mkObj [("i", idx), ("t", tyJ)]), st'))
        (#[], st0)
```

Keep the loud `panic!` — its reason changes (it can no longer be an
assignment) but a goal mvar unreachable from its own goal is still a
record this dumper must not emit.

- [ ] **Step 2: Emit `assigns` after synthesis**

After the `synthInstance?` call, in BOTH the `exc` and the ordinary
branch:

```lean
      -- `assigns`: the post-synthesis state of every goal mvar. This is
      -- the ONLY place `assignOutParams`' effect is observable —
      -- `ok`/`val` are identical whether or not the caller's output
      -- parameter was assigned (design spec § Amendment 3, item 6). An
      -- mvar that is still unassigned contributes no entry.
      let (assignsJ, _) ← goalMVars.foldlM (fun (acc, st) (m : MVarId) => do
        if !(← m.isAssigned) then pure (acc, st) else
        let v ← instantiateMVars (.mvar m)
        let (vJ, st') := (encExpr v).run st
        let idx := (st'.mvars.get? m).getD 0
        pure (acc.push (Json.mkObj [("i", idx), ("e", vJ)]), st'))
        (#[], st1)
```

`idx` is safe to read from `st1` here rather than re-deriving: `st1`
already numbered every goal mvar while encoding the pre-synthesis
`goal`, so `get?` cannot miss. Add `("assigns", Json.arr assignsJ)` to
both record field lists.

- [ ] **Step 3: Document the field in the module header**

Extend the "Record shape" block near the top of `dump_synth.lean`:

```
  , "assigns": [ {"i":<N>, "e":<E>} ]  -- post-synthesis assignments
```

with a sentence stating why it exists (it is the only observable
difference `assignOutParams` makes) and that `goal`/`mvars` are
pre-synthesis while `assigns` is post.

- [ ] **Step 4: Compare it in the gate**

In `crates/leanr_meta/tests/oracle_synth.rs`, after the `val` comparison
and inside the same `Ok(got)` arm (so the `EncSt` `est` is the one that
already encoded `goal` and `val`):

```rust
                // `assigns`: the post-synthesis state of every goal
                // mvar. Comparing it is what makes M4b-3 P2b-i's
                // `assignOutParams` visible at all — `ok` and `val` are
                // identical whether or not the caller's output parameter
                // was assigned, and so is the term the gate compares.
                let mut got_assigns = Vec::new();
                for (idx, val) in assigned.iter() {
                    got_assigns.push(serde_json::json!({
                        "i": idx,
                        "e": encode_expr(&scratch, base, *val, &mut est),
                    }));
                }
                let want_assigns = q["assigns"].as_array().cloned().unwrap_or_default();
                if got_assigns != want_assigns {
                    failures.push(format!(
                        "{id}: leanr assigns={got_assigns:?} oracle assigns={want_assigns:?}"
                    ));
                }
```

`assigned` is collected **before** `drop(ctx)` (the gate drops `ctx` to
read `scratch` back), right next to the existing
`ctx.instantiate_mvars(v)` call on the answer. Keep
`declared_mvars: Vec<(u64, NameId)>` from the declaration loop above —
the loop already has both the record's canonical index and the `NameId`
— and build it with the `MVarCtx` accessors the crate already exposes:

```rust
        // Post-synthesis state of every goal mvar, in the record's own
        // index order. `assignment` is `mctx`'s existing accessor
        // (`mvar_ctx.rs:91`); an unassigned mvar contributes nothing,
        // matching the dumper.
        let mut assigned: Vec<(u64, ExprId)> = Vec::new();
        for (idx, nid) in &declared_mvars {
            if ctx.mctx().assignment(MVarId(*nid)).is_none() {
                continue;
            }
            let m = scratch_mvar(&mut ctx, *nid);
            match ctx.instantiate_mvars(m) {
                Ok(v) => assigned.push((*idx, v)),
                Err(e) => {
                    failures.push(format!("{id}: instantiate_mvars on goal mvar {idx}: {e:?}"));
                }
            }
        }
        assigned.sort_by_key(|(i, _)| *i);
```

`scratch_mvar` re-creates the mvar's `ExprId` with
`scratch.expr_mvar(base, Some(nid))` — the same call
`tests/support/mod.rs:369` already makes when decoding a `{"k":"mvar"}`
node; inline it or lift it into `support` if both gates end up wanting
it. Sorting by `i` makes the comparison order-insensitive by
construction.

- [ ] **Step 5: Regenerate and check the diff is additive only**

```bash
cp tests/fixtures/meta/synth-queries.jsonl /tmp/claude-1000/-workspace/synth-queries.t8
mise run fixtures:regen
diff <(jq -c 'del(.assigns)' /tmp/claude-1000/-workspace/synth-queries.t8) \
     <(jq -c 'del(.assigns)' tests/fixtures/meta/synth-queries.jsonl) && echo "ONLY assigns CHANGED"
jq -c 'select((.assigns // []) | length > 0) | .id' tests/fixtures/meta/synth-queries.jsonl
```

Expected: `ONLY assigns CHANGED`, and the second command prints
**nothing** — no committed query can assign a goal mvar yet, so every
`assigns` is empty. (If `jq` is unavailable, compare with a two-line
Python script instead; do not skip the check.)

- [ ] **Step 6: Run the gate and commit**

```bash
cargo test -p leanr_meta --test oracle_synth
mise run test
mise run ci
git add tests/fixtures/meta/dump_synth.lean tests/fixtures/meta/synth-queries.jsonl \
        crates/leanr_meta/tests/oracle_synth.rs
git commit -m "M4b-3 P2b-i task 8: record post-synthesis goal-mvar assignments

The synth record shape could not see assignOutParams at all: ok and val
are identical whether or not the caller's outParam was assigned. goal and
mvars now encode the query as ASKED (pre-synthesis) and the new assigns
field carries the post-synthesis state. Every committed record is
byte-identical apart from an empty assigns array."
```

---

### Task 9: the outParam queries, and retargeting the stale seam docs

**Files:**
- Modify: `tests/fixtures/meta/dump_synth.lean` (`synthQueries` + the
  curated-list doc block above it)
- Modify: `crates/leanr_meta/tests/oracle_synth.rs` (`compared` count)
- Modify: `crates/leanr_meta/src/synth.rs` (the `withConfig` seam block)
- Modify: `crates/leanr_elab/src/synthetic/ladder.rs`,
  `crates/leanr_elab/src/lib.rs` (**doc comments only**)
- Regenerate: `tests/fixtures/meta/synth-queries.jsonl`

**Interfaces:**
- Consumes: everything above.
- Produces: five new committed records; `compared` rises 13 → 18.

- [ ] **Step 1: Add the queries**

In `dump_synth.lean`'s `synthQueries`, after the `mvarGoal` entry:

```lean
  , (`outParam,        0, do
      pure (mkApp (mkApp (mkApp (mkConst `Op [Level.zero]) nTy) nTy) (← mkFreshExprMVar type0)))
  , (`outParamReject,  0, pure (mkApp (mkApp (mkApp (mkConst `Op [Level.zero]) nTy) nTy)
      (mkConst `NoBase)))
  , (`outParamNoMVars, 0, pure (mkApp (mkApp (mkApp (mkConst `Op [Level.zero]) nTy) nTy)
      (mkApp (mkConst `Dual) nTy)))
  , (`outParamLevel,   0, do
      pure (mkApp (mkApp (mkConst `Lvl [Level.zero, Level.zero]) nTy) (← mkFreshExprMVar type0)))
  , (`outParamGet,     0, do
      pure (mkApp (mkApp (mkApp (mkConst `Get [Level.zero, Level.zero, Level.zero]) nTy) nTy)
        (← mkFreshExprMVar type0)))
```

Check `nTy` / `type0` / `cls1` against their definitions further up the
file and use the existing helpers where they fit (`cls1` builds a
one-argument class application; these are three- and two-argument ones,
so they are spelled out).

- [ ] **Step 2: Document each query in the curated-list block**

Add to the `/-- ... -/` block above `synthQueries`, in the same style as
the existing entries:

```
* `outParam`        — `Op N N ?c` with `?c` an UNASSIGNED mvar minted
                      OUTSIDE the search, in the class's OUTPUT
                      parameter position. The oracle answers `instOpN`
                      AND assigns `?c := N` (`assignOutParams`,
                      SynthInstance.lean:847-861). The assignment is
                      visible only in `assigns` — `ok`/`val` are the
                      same either way, which is why that field exists.
                      This is the shape leanr_elab's ladder.rs:105-115
                      cites as a live divergence.
* `outParamReject`  — `Op N N NoBase`: the search succeeds against the
                      PREPROCESSED goal (`instOpN`, with the output
                      position replaced by a fresh mvar) and the answer
                      is then REJECTED, because `assignOutParams`'
                      `isDefEq` cannot reconcile `NoBase` with `N`.
                      `ok:false`. An `assignOutParams` stubbed to `true`
                      answers `instOpN` here and fails the gate.
* `outParamNoMVars` — `Op N N (Dual N)`: a GROUND goal against an
                      out-param class, i.e. `preprocess`'s `.noMVars`
                      kind, which the oracle nevertheless routes through
                      `preprocessOutParam` (:983-1000, the `OrderDual`
                      note). `Dual` is semireducible, so the search
                      cannot unfold it at `.instances` transparency and
                      a goal taken literally would FAIL; replacing the
                      output position with an mvar finds `instOpN`, and
                      `assignOutParams`' `withDefault` `isDefEq` (:851)
                      is what then reconciles `Dual N` with `N`.
                      `ok:true`. Skip either half and the verdict flips.
* `outParamLevel`   — `Lvl N ?b`: the class whose universe `v` occurs
                      ONLY in its output parameter, so
                      `ClassEntry.outLevelParams` is non-empty and
                      `preprocessOutParam`'s `preprocessLevels` branch
                      (:786-795) runs. The RECORD pins the answer and
                      `?b := N`; the level refresh itself is unit-tested
                      in `synth.rs` instead, because the canonical
                      record scheme has no level-mvar case at all (see
                      `encLevel`).
* `outParamGet`     — `Get N N ?e`: the `GetElem` shape from the
                      oracle's own worked example (App.lean:143-146),
                      which M4b-3 P2b-ii needs in `Elab0.lean`. Proved
                      out here first.
```

- [ ] **Step 3: Regenerate and inspect the new records**

```bash
mise run fixtures:regen
jq -c 'select(.id | startswith("outParam")) | {id, ok, assigns}' tests/fixtures/meta/synth-queries.jsonl
```

Expected, from the oracle:
`outParam/synth/0` → `ok:true`, one `assigns` entry;
`outParamReject/synth/0` → `ok:false`;
`outParamNoMVars/synth/0` → `ok:true`;
`outParamLevel/synth/0` → `ok:true`, one `assigns` entry;
`outParamGet/synth/0` → `ok:true`, one `assigns` entry.

**If `outParamNoMVars` came back `ok:false`, do not "fix" it** — the
oracle is the definition of correct. Record what it actually did, and
check whether `Dual` really is semireducible in the regenerated fixture
(a stray `@[reducible]`, or `Dual` being unfolded by the elaborator
before the query is built, would make the query non-discriminating; say
so in the curated-list entry rather than leaving prose that claims a
discrimination the record does not have).

- [ ] **Step 4: Raise the `compared` count**

In `crates/leanr_meta/tests/oracle_synth.rs`:

```rust
    assert_eq!(
        compared, 18,
        "expected 18 compared synthesis records (skipped `exc`: {skipped_exc:?}; \
         skipped near-budget: {skipped_near_budget:?}; seam-excluded: \
         {skipped_seam:?}) — if the curated list in dump_synth.lean grew or shrank \
         deliberately, update this count"
    );
```

- [ ] **Step 5: Run the gate**

Run: `cargo test -p leanr_meta --test oracle_synth -- --nocapture`
Expected: PASS with 18 compared records.

- [ ] **Step 6: Retarget the seam docs this plan made stale**

Three edits, all comments:

1. `crates/leanr_meta/src/synth.rs`, the `withConfig` block on
   `synth_instance_main` (`:1651-1659` before this plan): its last bullet
   lists `preprocess` / `preprocessOutParam` **and**
   `withNewMCtxDepth (allowLevelAssignments := true)` as one NAMED SEAM
   owned by "M4b". `preprocess`/`preprocessOutParam` are now ported —
   rewrite the bullet so it names only the depth model, keeps the
   `SynthInstance.lean:958-968` citation, and points at
   `synth_instance_preprocessed` for what did land.
2. `crates/leanr_elab/src/synthetic/ladder.rs:97-123` ("Residue 1"): it
   says the residue is "unreachable today only because outParam support
   is itself a named seam" and that the pre-test "MUST be taught to
   exempt output-parameter positions" when P2b lands `classExtension`.
   Update it to record that P2b-i has landed the mechanism in
   `leanr_meta`, that the elaborator pre-test exemption is **P2b-ii's**
   and still open, and that `Elab0.lean` still has no outParam class —
   which is what keeps it unreachable now.
3. `crates/leanr_elab/src/lib.rs` — the "local-instance outParam result
   types" bullet and the residue list around `:242-246`: same retarget,
   P2b-i shipped the synthesis half, P2b-ii owns the elaborator half.

Do not change any `leanr_elab` code in this task — comments only.

- [ ] **Step 7: Full gate and commit**

```bash
mise run test
mise run ci
git add -A
git commit -m "M4b-3 P2b-i task 9: outParam synthesis queries + seam-doc retargeting

Five committed records: the assigned outParam, the rejected one, the
ground .noMVars/OrderDual shape, the out-only-universe class, and the
GetElem shape P2b-ii needs. compared 13 -> 18. The preprocess/
preprocessOutParam seam notes in synth.rs, ladder.rs and lib.rs now name
only what is still open — the mctx-depth model, and P2b-ii's pre-test
exemption."
```

---

## Verification summary

After Task 9, these must all hold:

- `mise run test` — green, including `oracle_synth` (18 compared) and
  `oracle_elab` (101 records, unmoved throughout).
- `mise run ci` — green (`cargo fmt --check` + clippy included).
- `git diff` against the merge base touches no `leanr_kernel` file, and
  no `leanr_elab` file outside doc comments.
- Every mechanism this plan adds has a test that fails when it is stubbed:
  `assign_out_params` → `outParamReject/synth/0`;
  its `withDefault` and `preprocessOutParam`'s `.noMVars` call →
  `outParamNoMVars/synth/0`; the post-rollback *placement* →
  `outParam/synth/0`'s `assigns`; `preprocessLevels` →
  `preprocess_out_param_refreshes_out_only_universes`;
  `with_assignable_synthetic_opaque` →
  `synth_instance_assigns_a_synthetic_opaque_out_param`.

## What this plan deliberately does NOT do

Each is a named seam with an owner, not an oversight:

- **`checkMayHaveSideEffects` + `check result`** (`SynthInstance.lean:876-923`)
  — needs a Meta-layer `Lean.Meta.check`, which this crate does not have
  and cannot take from `leanr_check` (that crate sits above it).
- **`preprocess`'s `cacheKeyType` and the synthesis cache** — no cache
  exists in `leanr_meta`, so the wildcarding has no consumer.
- **The mctx-depth model** — `ladder.rs`'s residues 2 and 3, and
  `oracle_synth.rs`'s existing `mvarGoal/synth/0` seam exclusion, stay
  exactly as they are. This plan closes residue 1 only.
- **Pi-shaped synthesis goals** — `preprocess` seams them rather than
  silently treating them as flat.
- **Anything in `leanr_elab`** — the stuck pre-test exemption, the
  `finalize` outParam branch, `Elab0.lean`'s outParam class and
  `Lean.Internal.coeM`: all M4b-3 P2b-ii, which gets its own plan.
