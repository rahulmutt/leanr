# M4a Plan 4 — Typeclass Synthesis Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Give `leanr_meta` a discrimination-tree-indexed instance table and a tabled (Prolog-style) typeclass-synthesis engine, wired into the existing `is_def_eq`/`whnf` stuck paths, verified against the oracle in two tiers — completing M4a.

**Architecture:** Three PRs. **PR-A** adds typed decode of three environment extensions to `leanr_olean` (`instanceExtension`, `defaultInstanceExtension`, `projectionFnInfoExt`) plus the `DiscrTree.Key` type they carry — pure olean-format work, independently fuzzed and tested. **PR-B** adds `discr_tree.rs` (a generic trie over the decoded `Key`), `instances.rs` (the instance table + `synth_order`), `synth.rs` (the tabled engine), and fills `synth_pending` + the two projection seams — gated by `meta:fast` extended with a committed synthesis fixture corpus. **PR-C** adds a separate `meta:nightly` discovery sweep (oracle-dump-then-diff, sharded by constant index, ratcheting its own pass-list) with its own GitHub workflow.

**Tech Stack:** Rust (workspace crates `leanr_olean`, `leanr_meta`, `leanr_kernel`), `mise` task runner, `cargo` + `cargo-fuzz`, Lean 4 metaprograms for oracle fixtures, GitHub Actions.

## Global Constraints

Every task's requirements implicitly include this section. Values copied verbatim from the spec and repo.

- **Toolchain pin:** `leanprover/lean4:v4.33.0-rc1` (`lean-toolchain`). Never bump outside a milestone boundary.
- **Mathlib pin:** SHA `c732b96d05efdb1fb84511dfdc24a8f70005ae99` (`mathlib-pin` line 3). Do not change.
- **`leanr_kernel` is not modified.** It is the TCB and depends on no other workspace crate. All new types and logic land in `leanr_olean` or `leanr_meta`.
- **`.olean` bytes are untrusted.** Every decoder must return `Ok(...)` or a structured `OleanError` on arbitrary bytes — never panic, abort, hang, or allocate unbounded (`docs/THREAT_MODEL.md`). Shape mismatch → `Err(bad("<expected>"))`. `unreachable!()`/`expect` only after the shape was already validated.
- **`meta:fast` is hermetic:** the committed `.olean` + `.jsonl` are the only inputs; CI never installs Lean and never touches `.mathlib`. Runs in seconds.
- **Every failure in `leanr_meta` is incompleteness, never unsoundness** — the kernel independently re-checks synthesized terms. Budgets are distinct error variants, never a `false` verdict. `IsDefEqStuck` is never collapsed to `false`.
- **Determinism:** a deterministic step counter (`MetaCtx::step`), never `maxHeartbeats`. Queries near any step/depth budget are recorded and excluded from the gate.
- **Tabled resolution, not memoized backtracking** — cyclic instance graphs must terminate.
- **`synth_order` is computed once at registration**, transcribing Lean's `computeSynthOrder`; never recomputed per query. Nightly pins import order explicitly.
- **The nightly synthesis sweep is a SEPARATE workflow** from `nightly-sweep.yml`, with a DISTINCT pass-list path and re-baseline branch, so the two never race.
- **Tools are mise-pinned** (`mise use --pin`). App deps via cargo only; every new dependency needs justification (prefer none).
- **Lean internals are transcribed from the pinned toolchain source and pinned empirically against fixture bytes.** Where this plan gives a Lean structure shape (ctor tags, field order, `Key` variants, `computeSynthOrder`), treat it as the expected shape to CONFIRM against `$(lean --print-prefix)/src/lean/Lean/...` at the pin and against a temporary `eprintln` probe over the fixture — exactly as every existing decoder's doc comment records.

---

# PR-A — Typed decode of three environment extensions (`leanr_olean`)

**Deliverable:** `ModuleData` exposes decoded instance, default-instance, and projection-function-info tables plus the `DiscrTree.Key` type, all fuzz-reachable and unit-tested against a committed fixture olean. No `leanr_meta` changes. Merges independently.

**Six edit sites per extension** (the reducibility/matcher precedent): (1) pub type + `ModuleData` field in `module_data.rs`; (2) re-export in `lib.rs`; (3) decoder fn + dispatch arm + struct-literal field in `interp_id.rs::module_data`; (4) `parse_parts` `std::mem::take` line; (5) fixture `.lean` + `fixtures:regen` line; (6) inline `#[cfg(test)]` test in `module_data.rs`.

## Task A1: Fixture source module + regen wiring

**Files:**
- Create: `tests/fixtures/Instances.lean`
- Modify: `mise.toml` (inside `fixtures:regen`, near the `Reducibility.olean`/`Matcher.olean` lines ~124–130)
- Create (generated, committed): `tests/fixtures/Instances.olean`

**Interfaces:**
- Produces: a committed `Instances.olean` whose `instanceExtension`, `defaultInstanceExtension`, and `projectionFnInfoExt` entries are non-empty, consumed by every A-task test and by PR-B's instance-table tests.

The module must be `prelude`-mode and import-free (same hermetic contract as `Matcher.lean`/`Meta0.lean`), carrying its own minimal scaffold, and must exercise: a class with instances, a class with a superclass (projection + diamond potential), a default instance, and a parametrized instance (subgoal chaining).

- [ ] **Step 1: Write the fixture module.** Reuse the scaffold prefix from `tests/fixtures/Matcher.lean` (lines 21–66: `lcErased`/`Eq`/`HEq`/`Prod`/`PProd`/`Unit`/`N`), then add class/instance content. Concretely include (adapt names to what elaborates under bare `prelude`):

```lean
-- classes with a superclass relationship (exercises projections + diamonds)
class Add (a : Type u) where add : a → a → a
class Mul (a : Type u) where mul : a → a → a
class Semigroup (a : Type u) extends Mul a where       -- projection: Semigroup.toMul
class Monoid (a : Type u) extends Semigroup a where one : a

-- concrete instances (simple resolution)
inductive N where | zero | succ (n : N)
instance instAddN : Add N where add := fun _ b => b
instance instMulN : Mul N where mul := fun _ b => b
instance instSemigroupN : Semigroup N where            -- diamond source via toMul
instance instMonoidN : Monoid N where one := N.zero

-- parametrized instance (subgoal chaining: Add (Prod a b) needs Add a, Add b)
instance instAddProd {a b : Type u} [Add a] [Add b] : Add (Prod a b) where
  add := fun p q => Prod.mk (Add.add p.fst q.fst) (Add.add p.snd q.snd)

-- a default instance
class OfN (n : N) (a : Type u) where ofN : a
@[default_instance] instance instOfNN (n : N) : OfN n N where ofN := n
```

- [ ] **Step 2: Add the regen line.** In `mise.toml`, alongside the existing fixture builds (built from inside `tests/fixtures` so the module name matches):

```
"sh -c 'cd tests/fixtures && lean Instances.lean -o Instances.olean'",
```

- [ ] **Step 3: Build the fixture.** Run: `mise run fixtures:regen` (requires the pinned Lean via elan). Expected: `tests/fixtures/Instances.olean` is (re)written with no error.

- [ ] **Step 4: Sanity-probe the extension names present.** Temporarily add, at the top of `interp_id.rs::module_data`'s entry loop, `eprintln!("[probe] ext = {}", self.st.to_name(None, ext_name).to_string());` (a throwaway probe — the documented pinning method). Run: `cargo test -p leanr_olean --lib -- --nocapture reducibility_entries_decode` after temporarily pointing a scratch test at `Instances.olean`, OR write a one-off `#[test]` that parses `Instances.olean` and prints. Record the exact rendered names for `instanceExtension`, `defaultInstanceExtension`, and the projection-info extension (likely `Lean.Meta.instanceExtension`, `Lean.Meta.defaultInstanceExtension`, `Lean.projectionFnInfoExt` — CONFIRM). Remove the probe.

- [ ] **Step 5: Commit.**

```bash
git add tests/fixtures/Instances.lean tests/fixtures/Instances.olean mise.toml
git commit -m "test(fixtures): Instances.olean — classes, instances, default instance, projections"
```

## Task A2: Decode `DiscrTree.Key`

**Files:**
- Modify: `crates/leanr_olean/src/module_data.rs` (add `DiscrKey` enum near `ReducibilityStatus`)
- Modify: `crates/leanr_olean/src/lib.rs` (re-export)
- Modify: `crates/leanr_olean/src/interp_id.rs` (add `discr_key` decoder — not yet dispatched)

**Interfaces:**
- Produces: `pub enum DiscrKey` and `InterpId::discr_key(&mut self, r: &Raw) -> Result<DiscrKey, OleanError>`, consumed by `InstanceEntry` decode (Task A3) and by `leanr_meta::discr_tree` (PR-B, Task B1).

Transcribe `Lean.Meta.DiscrTree.Key` from the pinned source (`Lean/Meta/DiscrTree.lean` or `.../DiscrTree/Types.lean` in v4.33.0-rc1). The expected shape (CONFIRM variants + tags against source and a fixture probe):

- [ ] **Step 1: Write the failing test.** In `module_data.rs` tests, decode `Instances.olean` and assert at least one instance's keys begin with a `const` key naming the class. First define the type and a helper on `ModuleData` in later tasks; here write the type + decoder test in isolation using a probe. Concretely, add this test (it will fail to compile until the enum exists):

```rust
#[test]
fn discr_key_const_decodes() {
    // Built in A3 once instance_entries exist; here we assert the enum shape
    // via a hand-built RawValue is out of scope — this test is a placeholder
    // that A3 replaces with a real instance-keys assertion.
    use crate::DiscrKey;
    let k = DiscrKey::Const { name_is_some: true, arity: 2 };
    assert!(matches!(k, DiscrKey::Const { arity: 2, .. }));
}
```

- [ ] **Step 2: Define the enum.** In `module_data.rs`:

```rust
/// oracle: `Lean.Meta.DiscrTree.Key` (v4.33.0-rc1). CONFIRM the variant
/// set and ctor tags against the pinned source and a fixture probe — the
/// arities and the `star`/`other` wildcard split are load-bearing for
/// matching (PR-B). `NameId` is `None` only for the anonymous name, which
/// a well-formed key never carries.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum DiscrKey {
    Const { name: NameId, arity: usize },
    Fvar { arity: usize },          // fvar identity is not serialized stably; keep arity only
    Bvar { index: usize, arity: usize },
    Lit(LitValue),                  // reuse the crate's literal representation
    Star,
    Other,
    Arrow,
    Proj { structure: NameId, index: usize, arity: usize },
    Sort,
}
```

(Adjust `LitValue`/`Fvar` to the crate's existing literal + fvar handling; if `DiscrTree.Key.lit` carries `Literal`, reuse whatever `interp_id` already uses for `Expr.lit`.)

- [ ] **Step 3: Write the decoder.** In `interp_id.rs`, following `reducibility_status`/`matcher_entry` (boxed-nullary ctors arrive as `RawValue::Scalar(tag)`; ctors-with-fields as `Ctor { tag, fields }`):

```rust
fn discr_key(&mut self, r: &Raw) -> Result<crate::DiscrKey, OleanError> {
    use crate::DiscrKey;
    match &**r {
        RawValue::Ctor { tag: 0, fields, .. } if fields.len() == 2 => Ok(DiscrKey::Const {
            name: self.name_req(&fields[0])?,
            arity: nat(&fields[1])? as usize,
        }),
        // ... one arm per Key ctor, tags CONFIRMED against source order ...
        RawValue::Scalar(t) => Err(bad("DiscrTree.Key scalar")), // fix once tags known
        _ => Err(bad("DiscrTree.Key")),
    }
}
```

Pin the exact tag→variant mapping by probing `Instances.olean`'s first instance's `keys` array (temporary `eprintln!("{:?}", raw)` in the loop).

- [ ] **Step 4: Re-export.** In `lib.rs` add `DiscrKey` (and `LitValue` if newly public) to the `pub use module_data::{...}` list.

- [ ] **Step 5: Run.** Run: `cargo test -p leanr_olean --lib discr_key_const_decodes`. Expected: PASS (compiles + the placeholder assertion holds). Real key assertions land in A3.

- [ ] **Step 6: Commit.**

```bash
git add crates/leanr_olean/src/module_data.rs crates/leanr_olean/src/lib.rs crates/leanr_olean/src/interp_id.rs
git commit -m "feat(olean): decode DiscrTree.Key"
```

## Task A3: Decode `instanceExtension`

**Files:**
- Modify: `crates/leanr_olean/src/module_data.rs` (`InstanceEntry` struct + `instances: Vec<InstanceEntry>` field + `parse_parts` take + inline test)
- Modify: `crates/leanr_olean/src/lib.rs` (re-export `InstanceEntry`)
- Modify: `crates/leanr_olean/src/interp_id.rs` (`instance_entry` decoder + `Lean.Meta.instanceExtension` dispatch arm + struct-literal field)

**Interfaces:**
- Consumes: `DiscrKey` (A2), `self.expr` (existing), `self.name_req`, `EntryScope`.
- Produces: `pub struct InstanceEntry { pub scope: EntryScope, pub keys: Vec<DiscrKey>, pub val: ExprId, pub priority: usize, pub global_name: Option<NameId> }` and `ModuleData.instances: Vec<InstanceEntry>`. Consumed by PR-B Task B3.

Transcribe `Lean.Meta.InstanceEntry` (v4.33.0-rc1): `keys : Array DiscrTree.Key`, `val : Expr`, `priority : Nat`, `globalName? : Option Name`, `attrKind : AttributeKind`. Serialized inside `ScopedEnvExtension.Entry` (global/scoped), like `reducibilityExtra`.

- [ ] **Step 1: Write the failing test.** In `module_data.rs`:

```rust
#[test]
fn instance_entries_decode() {
    let bytes = fixture("Instances.olean");
    let mut env = Environment::default();
    let md = ModuleData::parse(&bytes, env.store_mut()).expect("decode");
    let render = |n: NameId| env.store().to_name(None, Some(n)).to_string();
    // instAddN and instAddProd must both be present as global instances.
    let names: Vec<String> = md.instances.iter()
        .filter_map(|e| e.global_name.map(render)).collect();
    assert!(names.iter().any(|n| n == "instAddN"), "instances: {names:?}");
    assert!(names.iter().any(|n| n == "instAddProd"), "instances: {names:?}");
    // every instance carries at least one discrimination key headed by a const.
    for e in &md.instances {
        assert!(matches!(e.keys.first(), Some(DiscrKey::Const { .. })),
            "instance keys must start with a const head: {:?}", e.keys);
    }
}
```

- [ ] **Step 2: Run to verify it fails.** Run: `cargo test -p leanr_olean --lib instance_entries_decode`. Expected: FAIL (no `instances` field).

- [ ] **Step 3: Add the type + field.** In `module_data.rs` add the `InstanceEntry` struct and `pub instances: Vec<InstanceEntry>` to `ModuleData`; in `parse_parts` add `instances: std::mem::take(&mut base.instances),`.

- [ ] **Step 4: Add the decoder + dispatch.** In `interp_id.rs`:

```rust
fn instance_entry_payload(&mut self, r: &Raw) -> Result<(Vec<crate::DiscrKey>, ExprId, usize, Option<NameId>), OleanError> {
    // InstanceEntry: CONFIRM field count/order against source (keys, val,
    // priority, globalName?, attrKind). attrKind is validated by field count
    // but not stored.
    let (f, _) = ctor(r, 0, 5, "InstanceEntry")?;
    let keys = array(&f[0])?.iter().map(|k| self.discr_key(k)).collect::<Result<_,_>>()?;
    let val = self.expr(&f[1])?;
    let priority = nat(&f[2])? as usize;
    let global_name = self.opt_name(&f[3])?;
    Ok((keys, val, priority, global_name))
}
```

Dispatch arm (wrapped in `ScopedEnvExtension.Entry`, tag 0 global(v) / tag 1 scoped(ns, v) — reuse the exact match from `reducibilityExtra`):

```rust
"Lean.Meta.instanceExtension" => {
    for e in array(&pf[1])? {
        let RawValue::Ctor { tag, fields, .. } = &**e else { return Err(bad("ScopedEnvExtension.Entry")); };
        let (scope, payload) = match (tag, fields.len()) {
            (0, 1) => (crate::EntryScope::Global, &fields[0]),
            (1, 2) => (crate::EntryScope::Scoped(self.name_req(&fields[0])?), &fields[1]),
            _ => return Err(bad("ScopedEnvExtension.Entry")),
        };
        let (keys, val, priority, global_name) = self.instance_entry_payload(payload)?;
        instances.push(crate::InstanceEntry { scope, keys, val, priority, global_name });
    }
}
```

Add `let mut instances = Vec::new();` near the other accumulators and `instances,` to the returned struct literal.

- [ ] **Step 5: Run.** Run: `cargo test -p leanr_olean --lib instance_entries_decode`. Expected: PASS (after pinning the `InstanceEntry` field count/tags via a probe if the first attempt errors with `BadShape`).

- [ ] **Step 6: Re-export + commit.** Add `InstanceEntry` to `lib.rs`.

```bash
git add crates/leanr_olean/src
git commit -m "feat(olean): decode Meta.instanceExtension"
```

## Task A4: Decode `defaultInstanceExtension`

**Files:** same three files, mirroring A3.

**Interfaces:**
- Produces: `pub struct DefaultInstanceEntry { pub scope: EntryScope, pub class_name: NameId, pub instance_name: NameId, pub priority: usize }` and `ModuleData.default_instances: Vec<DefaultInstanceEntry>`. Consumed by PR-B Task B3.

Transcribe `Lean.Meta.DefaultInstanceEntry` (`className`, `instanceName`, `priority`), serialized in `ScopedEnvExtension.Entry`.

- [ ] **Step 1: Write the failing test.**

```rust
#[test]
fn default_instance_entries_decode() {
    let bytes = fixture("Instances.olean");
    let mut env = Environment::default();
    let md = ModuleData::parse(&bytes, env.store_mut()).expect("decode");
    let render = |n: NameId| env.store().to_name(None, Some(n)).to_string();
    assert!(md.default_instances.iter().any(|e|
        render(e.instance_name) == "instOfNN"), "defaults: {:?}",
        md.default_instances.iter().map(|e| render(e.instance_name)).collect::<Vec<_>>());
}
```

- [ ] **Step 2: Run to verify it fails.** Run: `cargo test -p leanr_olean --lib default_instance_entries_decode`. Expected: FAIL.

- [ ] **Step 3: Implement.** Add struct + `default_instances` field + `parse_parts` take + `default_instance_entry` decoder + `"Lean.Meta.defaultInstanceExtension"` dispatch arm (same scope-wrapper match) + struct-literal field + re-export. The payload decoder:

```rust
fn default_instance_payload(&mut self, r: &Raw) -> Result<(NameId, NameId, usize), OleanError> {
    let (f, _) = ctor(r, 0, 3, "DefaultInstanceEntry")?;
    Ok((self.name_req(&f[0])?, self.name_req(&f[1])?, nat(&f[2])? as usize))
}
```

- [ ] **Step 4: Run.** Run: `cargo test -p leanr_olean --lib default_instance_entries_decode`. Expected: PASS.

- [ ] **Step 5: Commit.**

```bash
git add crates/leanr_olean/src
git commit -m "feat(olean): decode Meta.defaultInstanceExtension"
```

## Task A5: Decode the projection-function-info extension

**Files:** same three files.

**Interfaces:**
- Produces: `pub struct ProjectionFnInfo { pub proj_fn: NameId, pub ctor: NameId, pub num_params: usize, pub index: usize, pub from_class: bool }` and `ModuleData.projection_fns: Vec<ProjectionFnInfo>`. Consumed by PR-B Task B6 (the `get_stuck_mvar` / `unfold_proj_inst_when_instances` seams).

Transcribe `Lean.ProjectionFunctionInfo` (`ctorName`, `numParams`, `i`, `fromClass`) keyed by the projection function name, from `projectionFnInfoExt` (a `SimplePersistentEnvExtension`, unwrapped like `reducibilityCore`/matcher — CONFIRM whether entries are `(Name × ProjectionFunctionInfo)` pairs).

- [ ] **Step 1: Write the failing test.**

```rust
#[test]
fn projection_fn_info_decodes() {
    let bytes = fixture("Instances.olean");
    let mut env = Environment::default();
    let md = ModuleData::parse(&bytes, env.store_mut()).expect("decode");
    let render = |n: NameId| env.store().to_name(None, Some(n)).to_string();
    // Semigroup.toMul is a class projection.
    let toMul = md.projection_fns.iter().find(|p| render(p.proj_fn) == "Semigroup.toMul");
    assert!(toMul.is_some(), "projections: {:?}",
        md.projection_fns.iter().map(|p| render(p.proj_fn)).collect::<Vec<_>>());
    assert!(toMul.unwrap().from_class, "toMul must be flagged fromClass");
}
```

- [ ] **Step 2: Run to verify it fails.** Run: `cargo test -p leanr_olean --lib projection_fn_info_decodes`. Expected: FAIL.

- [ ] **Step 3: Implement** the struct, field, `parse_parts` take, decoder, dispatch arm (CONFIRM extension name — likely `Lean.projectionFnInfoExt`), struct-literal field, re-export.

- [ ] **Step 4: Run.** Run: `cargo test -p leanr_olean --lib projection_fn_info_decodes`. Expected: PASS.

- [ ] **Step 5: Commit.**

```bash
git add crates/leanr_olean/src
git commit -m "feat(olean): decode projectionFnInfoExt"
```

## Task A6: Fuzz reachability + PR-A gate

**Files:** none (verification task).

- [ ] **Step 1: Confirm decoders are fuzz-reachable.** The three new dispatch arms live inside `interp_id::module_data`, which `ModuleData::parse`/`parse_parts` always walk — so the existing `fuzz/fuzz_targets/module_data.rs` reaches them with no change. Verify every new decoder returns `Err(bad(...))` (never `unwrap`/`panic`/`unreachable!`) on shape mismatch by reading each new arm.

- [ ] **Step 2: Run the fuzzer briefly.** Run: `mise run fuzz:olean`. Expected: no crash within the 60s budget.

- [ ] **Step 3: Run the full olean test suite.** Run: `cargo test -p leanr_olean`. Expected: all pass (new + existing decode tests, including `reducibility_entries_decode`, `matcher_entries_decode`).

- [ ] **Step 4: Run the workspace gate.** Run: `mise run ci` (or at minimum `cargo test --workspace && cargo clippy --workspace && cargo deny check`). Expected: green. PR-A is complete and mergeable.

---

# PR-B — Discrimination tree, instance table, tabled engine, `synth_pending` (`leanr_meta`)

**Deliverable:** `synth_instance` resolves typeclass goals against a discrimination-tree-indexed instance table via a tabled engine; `synth_pending` and the two projection seams are filled; `meta:fast` gains a committed synthesis fixture corpus that agrees with the oracle. Depends on PR-A (merged) for the decoded tables and `DiscrKey`.

Add `discr_tree`, `instances`, `synth` to the `mod` list in `crates/leanr_meta/src/lib.rs`.

## Task B1: `discr_tree.rs` — the generic trie (standalone, reusable)

**Files:**
- Create: `crates/leanr_meta/src/discr_tree.rs`
- Modify: `crates/leanr_meta/src/lib.rs` (add `pub(crate) mod discr_tree;` — or `pub mod` so later simp/rw slices reuse it)

> **Layering note (deviation from the design's wording).** The design placed the `Key` model inside `discr_tree.rs`. But instance keys are decoded olean data (`InstanceEntry.keys`, Task A2) that `leanr_meta` consumes, and `leanr_meta` depends on `leanr_olean` (never the reverse). So the `DiscrKey` *enum* lives in `leanr_olean` and this generic *trie* lives in `leanr_meta` — the only split that keeps the dependency direction correct. The trie stays "standalone and reusable" (no `MetaCtx` dependency) exactly as the design intends.

**Interfaces:**
- Consumes: `leanr_olean::DiscrKey`.
- Produces:
  - `pub struct DiscrTree<V> { ... }` with `Default`.
  - `pub fn insert(&mut self, path: &[DiscrKey], value: V)`.
  - `pub fn get_match_keys(&self, path: &[DiscrKey]) -> Vec<&V>` — returns matches **specific-before-wildcard**.
  This is a pure data structure with NO dependency on `MetaCtx` — its own unit tests only. PR-B Task B2 supplies expression→path computation; simp/rw reuse this module later.

Transcribe the trie + `getMatch` traversal from `Lean.Meta.DiscrTree` (v4.33.0-rc1). The match order rule (Lean's `getMatchCore`): at each node try the specific key first, then the `Star` (wildcard) child; a `Star` in the *query* path matches any child. Arity drives how many following keys a wildcard skips.

- [ ] **Step 1: Write the failing test.**

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use leanr_olean::DiscrKey;
    fn c(name_arity: (u32, usize)) -> DiscrKey { /* build a Const key with a test NameId */ }

    #[test]
    fn specific_beats_wildcard() {
        let mut t: DiscrTree<&'static str> = DiscrTree::default();
        // Add a → [Const Add 1, Const N 0] and a wildcard a → [Const Add 1, Star]
        t.insert(&[/*Add*/ c((1,1)), /*N*/ c((2,0))], "specific");
        t.insert(&[/*Add*/ c((1,1)), DiscrKey::Star], "wildcard");
        // A concrete query Add N returns specific FIRST, then wildcard.
        let got = t.get_match_keys(&[c((1,1)), c((2,0))]);
        assert_eq!(got, vec![&"specific", &"wildcard"]);
    }

    #[test]
    fn wildcard_query_matches_both() {
        let mut t: DiscrTree<&'static str> = DiscrTree::default();
        t.insert(&[c((1,1)), c((2,0))], "n");
        t.insert(&[c((1,1)), c((3,0))], "m");
        // Query Add ?  (Star) returns both stored branches.
        let got = t.get_match_keys(&[c((1,1)), DiscrKey::Star]);
        assert_eq!(got.len(), 2);
    }
}
```

- [ ] **Step 2: Run to verify it fails.** Run: `cargo test -p leanr_meta --lib discr_tree`. Expected: FAIL (no `DiscrTree`).

- [ ] **Step 3: Implement the trie.** A node maps `DiscrKey → child node` plus a `values: Vec<V>` at terminals. `insert` walks/creates the path. `get_match_keys` transcribes `getMatchCore`: consume the query path key-by-key, at each step following (a) the exact child then (b) the `Star` child, accumulating values in specific-then-wildcard order; a `Star` query key matches every child at that position (skipping subtrees by arity). Keep it generic over `V`.

- [ ] **Step 4: Run.** Run: `cargo test -p leanr_meta --lib discr_tree`. Expected: PASS.

- [ ] **Step 5: Commit.**

```bash
git add crates/leanr_meta/src/discr_tree.rs crates/leanr_meta/src/lib.rs
git commit -m "feat(meta): generic discrimination-tree trie over DiscrKey"
```

## Task B2: `mk_path` / `get_match_expr` — expression→path computation (`impl MetaCtx`)

**Files:**
- Create: `crates/leanr_meta/src/discr_path.rs` (an `impl MetaCtx` block; keep it beside `instances.rs`)
- Modify: `crates/leanr_meta/src/lib.rs`

**Interfaces:**
- Consumes: `self.whnf`, `self.node`, `self.get_app_fn`, `self.get_app_args`, transparency, `leanr_olean::DiscrKey`.
- Produces: `pub(crate) fn mk_path(&mut self, e: ExprId) -> Result<Vec<DiscrKey>, MetaError>` and `pub(crate) fn discr_get_match<'a, V>(&mut self, tree: &'a DiscrTree<V>, goal: ExprId) -> Result<Vec<&'a V>, MetaError>`.

Transcribe `Lean.Meta.DiscrTree.mkPath` / `mkPathAux` (v4.33.0-rc1): normalize each subterm by whnf at **reducible** transparency (`reduceDT`/`whnfR`), then emit a key for the head (`Const name arity`, `Sort`, `Arrow`, `Lit`, `Proj`, else `Star`/`Other`), recursing into arguments in order but **skipping instance-implicit and type-family arguments** per Lean's rule (it uses `ignoreArg`, driven by the function's binder info). This is risk 6 — key-computation fidelity — so keep the whnf transparency and the `ignoreArg` predicate exactly as the oracle.

- [ ] **Step 1: Write the failing test.** Using `test_support` over `Instances.olean` (add a `with_instances_ctx` helper mirroring `with_matcher_ctx`), build the goal `Add N` and assert its path head is `Const Add`:

```rust
#[test]
fn mk_path_heads_on_the_class() {
    with_instances_ctx(|ctx| {
        let add = ctx.const_expr("Add");        // helper: @Add applied to nothing
        let n = ctx.const_expr("N");
        let goal = ctx.mk_app_spine(add, &[/* Sort */ ctx.type0(), n]).unwrap();
        let path = ctx.mk_path(goal).unwrap();
        assert!(matches!(path.first(), Some(DiscrKey::Const { name, .. })
            if ctx.render(*name) == "Add"), "path: {path:?}");
    });
}
```

- [ ] **Step 2: Run to verify it fails.** Run: `cargo test -p leanr_meta --lib mk_path`. Expected: FAIL.

- [ ] **Step 3: Implement `mk_path` + `discr_get_match`.** `discr_get_match` = `tree.get_match_keys(&self.mk_path(goal)?)`. Add the `with_instances_ctx`/`const_expr`/`render`/`type0` helpers to `test_support.rs` (mirror `with_matcher_ctx`, replaying `Instances.olean`).

- [ ] **Step 4: Run.** Run: `cargo test -p leanr_meta --lib mk_path`. Expected: PASS.

- [ ] **Step 5: Commit.**

```bash
git add crates/leanr_meta/src/discr_path.rs crates/leanr_meta/src/test_support.rs crates/leanr_meta/src/lib.rs
git commit -m "feat(meta): reducible-transparency discrimination path computation"
```

## Task B3: `instances.rs` — the instance table + `synth_order`

**Files:**
- Create: `crates/leanr_meta/src/instances.rs`
- Modify: `crates/leanr_meta/src/lib.rs`; `crates/leanr_meta/src/metactx.rs` (hold the tables on `MetaCtx`)

**Interfaces:**
- Consumes: `leanr_olean::{InstanceEntry, DefaultInstanceEntry}`, `DiscrTree<InstanceEntry>` (B1), `mk_path`/`discr_get_match` (B2), `self.view.get`, `self.infer_type`.
- Produces:
  - `pub(crate) struct Instance { pub val: ExprId, pub ty: ExprId, pub priority: usize, pub synth_order: Vec<usize>, pub global_name: Option<NameId> }`
  - `pub(crate) struct InstanceTable { tree: DiscrTree<Instance>, defaults: Vec<(NameId /*class*/, NameId /*inst*/, usize /*prio*/)> }`
  - `MetaCtx::instances: InstanceTable` (built once, at ctx construction, from the decoded module data).
  - `pub(crate) fn get_instances(&mut self, goal: ExprId) -> Result<Vec<Instance>, MetaError>` — `discr_get_match` on the goal, cloned, sorted by priority desc then registration order (transcribe Lean's `getInstances` ordering).
  - `pub(crate) fn default_instances(&self, class: NameId) -> Vec<(NameId, usize)>`.

`synth_order` transcribes `Lean.Meta.computeSynthOrder` (v4.33.0-rc1): given the instance type `∀ (x₁ ... xₙ), C ...`, it is the order in which the instance-implicit binders (`[...]`) are attempted, driven by which binders' metavariables are determined by others. Compute once, here, at table construction; store the index list.

- [ ] **Step 1: Write the failing test.**

```rust
#[test]
fn instance_table_finds_add_n() {
    with_instances_ctx(|ctx| {
        let goal = ctx.parse_goal("Add N");        // helper building @Add Type N
        let found = ctx.get_instances(goal).unwrap();
        assert!(found.iter().any(|i| i.global_name.map(|n| ctx.render(n)) == Some("instAddN".into())),
            "found: {:?}", found.iter().map(|i| i.global_name.map(|n| ctx.render(n))).collect::<Vec<_>>());
    });
}

#[test]
fn parametrized_instance_has_two_synth_subgoals() {
    with_instances_ctx(|ctx| {
        // instAddProd : [Add a] [Add b] → Add (Prod a b) — synth_order lists 2 subgoals.
        let inst = ctx.instance_named("instAddProd").unwrap();
        assert_eq!(inst.synth_order.len(), 2, "synth_order: {:?}", inst.synth_order);
    });
}
```

- [ ] **Step 2: Run to verify it fails.** Run: `cargo test -p leanr_meta --lib instances`. Expected: FAIL.

- [ ] **Step 3: Build the table.** In `MetaCtx::new`, after storing reducibility/matchers, construct `InstanceTable` from `module_data.instances` (insert each into the tree under its decoded `keys`, computing `ty` from `global_name`→`view.get(name).type` and `synth_order` via `compute_synth_order(ty)`) and `module_data.default_instances`. Add the `instance_named`/`parse_goal` test helpers.

- [ ] **Step 4: Run.** Run: `cargo test -p leanr_meta --lib instances`. Expected: PASS.

- [ ] **Step 5: Commit.**

```bash
git add crates/leanr_meta/src/instances.rs crates/leanr_meta/src/metactx.rs crates/leanr_meta/src/test_support.rs crates/leanr_meta/src/lib.rs
git commit -m "feat(meta): instance table with discrimination indexing and synth_order"
```

## Task B4: `synth.rs` — tabled-engine data structures + table mechanics

**Files:**
- Create: `crates/leanr_meta/src/synth.rs`
- Modify: `crates/leanr_meta/src/lib.rs`

**Interfaces:**
- Produces (all `pub(crate)`):
  - `struct SynthState { answers: HashMap<GoalKey, TableEntry>, generators: Vec<GeneratorNode>, consumers: Vec<ConsumerNode>, step: u64 }`
  - `struct TableEntry { answers: Vec<Answer>, waiters: Vec<Waiter>, complete: bool }`
  - `struct Answer { val: ExprId, assignments: MetaSnapshot-like }` (the resolved instance term + the mvar assignments it induced)
  - `struct GeneratorNode { goal: ExprId, key: GoalKey, remaining: Vec<Instance> }`
  - `struct ConsumerNode { key: GoalKey, mvar: MVarId, subgoals: Vec<ExprId>, next: usize }`
  - `enum Waiter { Consumer(usize), Root }`
  - `type GoalKey` — a normalized (α-equivalent-up-to-mvar) hash of the goal, produced by `normalize_goal_key(goal)`.

Transcribe the node/table model from `Lean.Meta.SynthInstance` (v4.33.0-rc1): `Answer`, `TableEntry`, `GeneratorNode`, `ConsumerNode`, `Waiter`, `SynthInstance.State`. Table keys are the goal abstracted over its mvars (Lean's `mkTableKey` / `abstractMVars`) so α-equivalent goals share an entry.

- [ ] **Step 1: Write the failing test** (pure table mechanics, no resolution yet):

```rust
#[test]
fn table_key_is_stable_up_to_mvar_renaming() {
    with_instances_ctx(|ctx| {
        // Two goals `Add ?a` with different mvar ids normalize to the same key.
        let (m1, _) = ctx.fresh_mvar_typed("Type");
        let (m2, _) = ctx.fresh_mvar_typed("Type");
        let g1 = ctx.parse_goal_with("Add", m1);
        let g2 = ctx.parse_goal_with("Add", m2);
        assert_eq!(ctx.normalize_goal_key(g1).unwrap(), ctx.normalize_goal_key(g2).unwrap());
    });
}

#[test]
fn adding_answer_wakes_waiters() {
    let mut st = SynthState::default();
    let key = GoalKey::for_test(1);
    st.new_entry(key.clone());
    st.add_waiter(&key, Waiter::Root);
    let woken = st.add_answer(&key, Answer::for_test());
    assert_eq!(woken, vec![Waiter::Root]);
}
```

- [ ] **Step 2: Run to verify it fails.** Run: `cargo test -p leanr_meta --lib synth::`. Expected: FAIL.

- [ ] **Step 3: Implement the structures + `normalize_goal_key` + `new_entry`/`add_waiter`/`add_answer`.** `normalize_goal_key` uses `instantiate_mvars` then an `abstract_mvars`-style canonical renaming (mvars numbered in first-occurrence order) hashed structurally — reuse the creation-order-renaming discipline the oracle harness already uses. `add_answer` appends the answer and returns the entry's waiters to wake.

- [ ] **Step 4: Run.** Run: `cargo test -p leanr_meta --lib synth::`. Expected: PASS.

- [ ] **Step 5: Commit.**

```bash
git add crates/leanr_meta/src/synth.rs crates/leanr_meta/src/lib.rs
git commit -m "feat(meta): tabled-synthesis state, table keys, waiter mechanics"
```

## Task B5: `synth.rs` — the resolution driver (`synth_instance`)

**Files:**
- Modify: `crates/leanr_meta/src/synth.rs`

**Interfaces:**
- Consumes: B4 structures, `get_instances` (B3), `is_def_eq` at `.instances` transparency (`defeq.rs`), `checkpoint`/`rollback` (`metactx.rs`), `mk_aux_mvar` (`assign.rs`), `self.step`/`self.guarded`, `DEFAULT_STEP_BUDGET`, `MetaError::{StepBudgetExhausted, DepthBudgetExhausted, IsDefEqStuck}`.
- Produces: `pub(crate) fn synth_instance(&mut self, ty: ExprId) -> Result<Option<ExprId>, MetaError>` — the resolved instance term, or `None` if no instance, or `Err(IsDefEqStuck)`/budget error.

Transcribe the driver from `Lean.Meta.SynthInstance.main`/`synth`/`step`/`generate`/`resume`/`consume`/`newSubgoal`/`tryResolve`/`getTop`/`wakeUp` (v4.33.0-rc1). The loop: seed a root subgoal for `ty`; repeatedly `step` (advance a generator: pop the next candidate `Instance`, `checkpoint`, `is_def_eq` its conclusion against the goal at `.instances`, on success spawn `ConsumerNode` subgoals in `synth_order`; else `rollback`); when a consumer's subgoals are all answered, build the answer term and `add_answer`, waking waiters. Terminate when the root has an answer, or all generators/consumers are exhausted (`None`). Each iteration calls `self.step()?` (deterministic budget → `StepBudgetExhausted`) and reentrancy is bounded by `self.guarded` (→ `DepthBudgetExhausted`). A subgoal `is_def_eq` returning `Err(IsDefEqStuck)` propagates the stuck condition rather than treating it as `false`. Cyclic instance graphs terminate because a repeated goal resolves against its existing `TableEntry` (consumer/waiter) instead of re-generating.

- [ ] **Step 1: Write the failing test.**

```rust
#[test]
fn synthesizes_simple_instance() {
    with_instances_ctx(|ctx| {
        let goal = ctx.parse_goal("Add N");
        let inst = ctx.synth_instance(goal).unwrap().expect("an instance");
        // The synthesized term type-checks against the goal (kernel is the check).
        let ty = ctx.infer_type(inst).unwrap();
        assert!(ctx.is_def_eq(ty, goal).unwrap());
    });
}

#[test]
fn synthesizes_via_subgoal_chaining() {
    with_instances_ctx(|ctx| {
        let goal = ctx.parse_goal("Add (Prod N N)"); // needs instAddProd + Add N ×2
        assert!(ctx.synth_instance(goal).unwrap().is_some());
    });
}

#[test]
fn no_instance_returns_none() {
    with_instances_ctx(|ctx| {
        let goal = ctx.parse_goal("Mul (Prod N N)"); // no Mul (Prod ..) instance
        assert_eq!(ctx.synth_instance(goal).unwrap(), None);
    });
}
```

- [ ] **Step 2: Run to verify it fails.** Run: `cargo test -p leanr_meta --lib synth::`. Expected: FAIL.

- [ ] **Step 3: Implement the driver.** Follow the transcription notes above. Keep the whole trial under one `checkpoint` so a failed root leaves `mctx` unchanged; run all instance `is_def_eq` at `.instances` transparency (save/restore `self.cfg.transparency`).

- [ ] **Step 4: Run.** Run: `cargo test -p leanr_meta --lib synth::`. Expected: PASS.

- [ ] **Step 5: Add termination + diamond + stuck tests.**

```rust
#[test]
fn cyclic_instances_terminate() {
    with_cyclic_instances_ctx(|ctx| {         // fixture: instance A→B and B→A
        let goal = ctx.parse_goal("A N");
        let _ = ctx.set_step_budget(50_000);
        // Must return (Some/None), never loop; a budget error is also acceptable
        // ONLY if recorded — here we assert it completes without StepBudget error.
        assert!(matches!(ctx.synth_instance(goal), Ok(_)));
    });
}

#[test]
fn diamond_resolves_deterministically() {
    with_instances_ctx(|ctx| {
        let goal = ctx.parse_goal("Mul N");   // reachable directly and via Semigroup.toMul
        let a = ctx.synth_instance(goal).unwrap();
        let b = ctx.synth_instance(goal).unwrap();
        assert_eq!(a.map(|e| ctx.render_expr(e)), b.map(|e| ctx.render_expr(e)));
    });
}
```

Add the cyclic fixture (`tests/fixtures/InstancesCyclic.lean` + regen line) and `with_cyclic_instances_ctx`.

- [ ] **Step 6: Run + commit.** Run: `cargo test -p leanr_meta --lib synth::`. Expected: PASS.

```bash
git add crates/leanr_meta/src/synth.rs crates/leanr_meta/src/test_support.rs tests/fixtures/InstancesCyclic.lean tests/fixtures/InstancesCyclic.olean mise.toml
git commit -m "feat(meta): tabled synthesis driver (generate/resume/consume) with termination"
```

## Task B6: `synth_pending` + the projection seams

**Files:**
- Modify: `crates/leanr_meta/src/whnf.rs` (replace the `synth_pending` stub ~1097; fill the `get_stuck_mvar` `Const`-arm ~991 and `unfold_proj_inst_when_instances` ~2143)
- Modify: `crates/leanr_meta/src/metactx.rs` (hold the decoded `projection_fns` map)

**Interfaces:**
- Consumes: `synth_instance` (B5), `self.mctx` decl/assign, `leanr_olean::ProjectionFnInfo` (A5), `self.guarded` (depth budget = `maxSynthPendingDepth`).
- Produces: a real `synth_pending`; `get_stuck_mvar` that descends a stuck class-field projection to its instance mvar; `unfold_proj_inst_when_instances` that reduces a class projection into its instance's projection at `.instances`/`.implicit`.

- [ ] **Step 1: Write the failing test.** A whnf/defeq query that is stuck on a class projection over an unresolved-but-synthesizable instance now makes progress:

```rust
#[test]
fn synth_pending_resolves_stuck_class_projection() {
    with_instances_ctx(|ctx| {
        // `Mul.mul (a := N) x y` where the `Mul N` instance arg is a fresh mvar;
        // synth_pending should synthesize it so whnf can proceed.
        let (goal, mvar) = ctx.stuck_mul_over_fresh_instance();
        assert!(ctx.synth_pending(mvar).unwrap(), "expected progress");
        assert!(ctx.mctx().is_assigned(mvar));
    });
}
```

- [ ] **Step 2: Run to verify it fails.** Run: `cargo test -p leanr_meta --lib synth_pending`. Expected: FAIL (stub returns `false`).

- [ ] **Step 3: Implement.** `synth_pending(mvar)`: if `mvar` is unassigned and its declared type has a concrete class head (`get_app_fn` of the instantiated type is a `Const` naming a class), run `self.guarded(|s| s.synth_instance(ty))`; on `Some(term)` `assign` the mvar and return `Ok(true)`; on `None` return `Ok(false)`; propagate `Err`. Fill `get_stuck_mvar`'s `Const`-arm using the decoded `projection_fns` map: if the head const is a projection function (`from_class`), descend into the projected structure argument (`whnf` it, recurse) to find the blocking instance mvar. Fill `unfold_proj_inst_when_instances` via `getProjectionFnInfo?`: at `.instances`/`.implicit`, rewrite `Proj.f (inst …)` to the instance's own field projection. Store `projection_fns: HashMap<NameId, ProjectionFnInfo>` on `MetaCtx`, built in `new`.

- [ ] **Step 4: Run.** Run: `cargo test -p leanr_meta --lib synth_pending`. Expected: PASS.

- [ ] **Step 5: Regression-run the existing meta suite.** Run: `cargo test -p leanr_meta`. Expected: all existing whnf/infer/defeq tests still pass (the seams previously returned `None`/`false`; filling them must not change any already-green fixture — if one changes, it was under-constrained; investigate before proceeding).

- [ ] **Step 6: Commit.**

```bash
git add crates/leanr_meta/src/whnf.rs crates/leanr_meta/src/metactx.rs crates/leanr_meta/src/test_support.rs
git commit -m "feat(meta): synth_pending + class-projection stuck/unfold seams"
```

## Task B7: Tier-1 gate — `dump_synth.lean`, fixtures, replay

**Files:**
- Create: `tests/fixtures/meta/dump_synth.lean`
- Create: `tests/fixtures/meta/Synth0.lean` (+ committed `Synth0.olean`)
- Create (generated, committed): `tests/fixtures/meta/synth-queries.jsonl`
- Create: `crates/leanr_meta/tests/oracle_synth.rs`
- Modify: `mise.toml` (`fixtures:regen` build lines; extend `meta:fast`)

**Interfaces:**
- Consumes: `synth_instance` (B5), the JSONL encode/decode helpers from `oracle_fast.rs` (factor the shared `decode_expr`/`encode_expr`/`EncSt` into a small `tests/support` module or copy the proven code).
- Produces: `meta:fast` runs `oracle_synth` too; a committed corpus of synthesis queries whose leanr verdict + canonicalized instance term match the oracle.

`dump_synth.lean` mirrors `dump_defeq.lean`: import ONLY `Synth0` (`LEAN_PATH=$PWD`), enumerate a curated list of `(constName, index, goalType)` synthesis queries, call `Lean.Meta.synthInstance goalType`, and emit JSONL records `{ "id":"<const>/synth/<i>", "q":"synth", "goal":<expr>, "ok":<bool>, "val":<expr?> }` with the canonical expr scheme + creation-order mvar renaming (reuse `encExpr`/`encPair`). `Synth0.lean` is prelude-mode, import-free, curated to exercise: simple resolution, subgoal chaining, a diamond (one deterministic answer), a default instance, priority ordering, a negative (no instance), and a stuck case (a goal with an output mvar that blocks).

- [ ] **Step 1: Write `Synth0.lean`** (scaffold prefix + the eight query shapes above; reuse the `Instances.lean` content and extend with a priority pair and a `@[default_instance]`).

- [ ] **Step 2: Write `dump_synth.lean`** (copy `dump_defeq.lean`'s header/encoders/`main` skeleton; replace the query loop with a `synthQueries : List (Name × Nat × Expr)` loop calling `synthInstance`, catching failure as `ok:false`).

- [ ] **Step 3: Add regen lines** to `mise.toml` `fixtures:regen`:

```
"sh -c 'cd tests/fixtures/meta && lean Synth0.lean -o Synth0.olean'",
"sh -c 'cd tests/fixtures/meta && LEAN_PATH=$PWD lean --run dump_synth.lean > synth-queries.jsonl'",
```

- [ ] **Step 4: Generate the corpus.** Run: `mise run fixtures:regen`. Expected: `synth-queries.jsonl` written with one record per curated query; eyeball that the negative case has `"ok":false` and simple cases carry a `"val"`.

- [ ] **Step 5: Write the replay test** `crates/leanr_meta/tests/oracle_synth.rs` (mirror `oracle_fast.rs::oracle_fast_gate`): load `Synth0.olean`, `replay` constants, and for each `synth` record build a fresh `MetaCtx`, decode `goal`, run `ctx.synth_instance(goal)`, then compare `ok` against `q["ok"]` and — when `ok` — the canonicalized `val` against `q["val"]` (thread one `EncSt` seeded on `goal`). Collect failures into a `Vec<String>`, assert empty. Exclude any record flagged near a budget (add a `"near_budget":true` field emitted when the oracle query approached `maxHeartbeats`, and skip those, per the determinism rule).

- [ ] **Step 6: Wire `meta:fast`.** Change the `meta:fast` task's `run` to also run the new binary:

```
run = ["cargo test --release -p leanr_meta --test oracle_fast", "cargo test --release -p leanr_meta --test oracle_synth"]
```

- [ ] **Step 7: Run the gate.** Run: `mise run meta:fast`. Expected: PASS (both binaries green, seconds, no Lean).

- [ ] **Step 8: Commit.**

```bash
git add tests/fixtures/meta/dump_synth.lean tests/fixtures/meta/Synth0.lean tests/fixtures/meta/Synth0.olean tests/fixtures/meta/synth-queries.jsonl crates/leanr_meta/tests/oracle_synth.rs mise.toml
git commit -m "test(meta): tier-1 synthesis differential gate (dump_synth + oracle_synth)"
```

## Task B8: PR-B gate

- [ ] **Step 1: Full workspace + lint + gates.** Run: `mise run ci`. Expected: green, including `meta:fast`, `parse:mathlib:fast`, `fmt:mathlib`, both fuzz targets' build, `cargo deny`.
- [ ] **Step 2: Confirm no kernel change.** Run: `git diff --stat main -- crates/leanr_kernel`. Expected: empty. PR-B is complete and mergeable.

---

# PR-C — `meta:nightly` discovery sweep (separate workflow)

**Deliverable:** a nightly sweep over Mathlib that synthesizes instances for mined goals, diffs against the oracle, and ratchets a dedicated synthesis pass-list — sharded by constant index, in its own GitHub workflow with its own re-baseline branch. Depends on PR-B (merged).

> **PLAN-LEVEL CONCRETIZATION (flagged for review).** The design says tier-2 "diffs the synthesized term against the oracle." Unlike the parse sweep (a leanr-only property), that needs an oracle at sweep time. This plan concretizes it as **oracle-dump-then-diff**, mirroring the `fixtures:regen`→`oracle_fast.rs` precedent at Mathlib scale: each shard first runs a Lean metaprogram to emit expected `synthInstance` results for its constant slice, then a Rust binary runs leanr synthesis and diffs. "Green" = leanr's verdict **and** canonical instance term match the oracle. This is the meaningful (not merely kernel-checkable) check the design's risk-2 discussion calls for. If you'd rather green = "leanr synthesizes a kernel-checkable instance" (cheaper, no Lean at sweep time, but blind to wrong-instance divergence), say so and Tasks C1/C2 collapse.

## Task C1: `dump_synth_mathlib.lean` — the sharded oracle metaprogram

**Files:**
- Create: `tests/fixtures/meta/dump_synth_mathlib.lean`

**Interfaces:**
- Consumes env: `LEANR_SYNTH_SHARD=I/N`, `LEANR_SYNTH_OUT=<path>`, the Mathlib environment (via `LEAN_PATH`/`initSearchPath`, imports pinned).
- Produces: JSONL at `LEANR_SYNTH_OUT` — one record per mined query: `{ "const":<name>, "id":"<const>/synth/<i>", "goal":<expr>, "ok":<bool>, "val":<expr?>, "near_budget":<bool> }`, canonical expr scheme (reuse `dump_synth.lean`'s encoders).

Logic (transcribe the enumeration from `check_sweep.rs`'s constant fold, but in Lean): import a pinned Mathlib module set (list them explicitly — **import order is pinned**, per the global constraint and risk 3), enumerate `(← getEnv).constants` sorted by name, select the shard slice (`idx % N == I-1`), and for each selected constant mine its instance-argument positions (binders with `instImplicit` info), form the (closed) instance goal type, run `Lean.Meta.synthInstance` under a recorded `maxHeartbeats`, and emit the record (flag `near_budget` when the heartbeat count came within a margin of the limit).

- [ ] **Step 1: Write the metaprogram.** Base it on `dump_synth.lean`. Sort constants deterministically; apply the `idx % N == I-1` stride so the shard slice matches the Rust binary's slice exactly (same sort key).
- [ ] **Step 2: Smoke-test one shard locally.** Run (needs `.mathlib`): `LEANR_SYNTH_SHARD=1/12 LEANR_SYNTH_OUT=/tmp/s1.jsonl LEAN_PATH="$(cd .mathlib && lake env printenv LEAN_PATH)" lean --run tests/fixtures/meta/dump_synth_mathlib.lean` on a truncated module set. Expected: JSONL with plausible records.
- [ ] **Step 3: Commit.**

```bash
git add tests/fixtures/meta/dump_synth_mathlib.lean
git commit -m "test(meta): sharded Mathlib synthesis oracle dumper"
```

## Task C2: The Rust synthesis sweep binary

**Files:**
- Create: `crates/leanr_meta/tests/synth_sweep.rs`
- Create: `tests/fixtures/meta/synth-passlist.txt` (2-line header + empty body initially)

**Interfaces:**
- Consumes env (mirror `mathlib_sweep.rs` exactly): `LEANR_SYNTH_SHARD`, `LEANR_SYNTH_GREEN_OUT`, `LEANR_SYNTH_MANIFEST_OUT`, `LEANR_SYNTH_MERGE`, `LEANR_SYNTH_PASSLIST_UPDATE`, `LEANR_SYNTH_PASSLIST_ONLY`, plus `LEANR_SYNTH_ORACLE=<jsonl>` (the C1 output for this shard) and `LEANR_OLEAN_PATH`/`LEANR_MATHLIB_DIR`.
- Produces: an `#[ignore]`d integration test `synth_sweep_ratchet` that shards by **constant index**, loads the full pinned environment, runs `synth_instance` per mined query, diffs against the oracle JSONL, computes the green constant set, and (in update/merge mode) ratchets `synth-passlist.txt` keyed by **fully-qualified constant name**.

Transcribe the mode/shard/gate/manifest/merge machinery from `crates/leanr_grammar/tests/mathlib_sweep.rs` verbatim in structure, with three deltas: (a) the unit of work is the **constant** (sorted `Vec<NameId>` by rendered name), sharded via the same `idx % n == i-1` stride helper (`shard_slice`); (b) each shard does ONE `load_closure` over the whole pinned target set (the `check_sweep.rs` pattern) so every shard's environment is identical — the invariant `validate_shard_manifests` relies on; (c) "green" per constant = every mined query for it agrees with the oracle record (verdict + canonical term). Keep the up-front mode/mutual-exclusion asserts, the gate-BEFORE-rewrite `assert!(regressions.is_empty())`, the upstream-deletion reconcile (`split_missing_from_regressions`, `exists` injected from shard manifests in merge mode), and the manifest set validation (exactly one per `1..=N`, none vacuous, all `present` equal to the union, all-blind guard).

- [ ] **Step 1: Write a focused unit test** for the shard-stride + green-diff logic (extractable pure functions), e.g.:

```rust
#[test]
fn green_requires_all_queries_agree() {
    // A constant with two queries: one agrees, one diverges → NOT green.
    let recs = vec![oracle_rec("c/synth/0", true), oracle_rec("c/synth/1", true)];
    let leanr = vec![("c/synth/0", true /*match*/), ("c/synth/1", false /*diverge*/)];
    assert!(!constant_is_green("c", &recs, &leanr));
}
```

- [ ] **Step 2: Run to verify it fails.** Run: `cargo test -p leanr_meta --test synth_sweep green_requires`. Expected: FAIL.
- [ ] **Step 3: Implement** the binary (structure per `mathlib_sweep.rs`; `passlist_path()` → `tests/fixtures/meta/synth-passlist.txt`). Load oracle JSONL, run leanr per query, diff.
- [ ] **Step 4: Run.** Run: `cargo test -p leanr_meta --test synth_sweep green_requires`. Expected: PASS.
- [ ] **Step 5: Commit.**

```bash
git add crates/leanr_meta/tests/synth_sweep.rs tests/fixtures/meta/synth-passlist.txt
git commit -m "test(meta): constant-sharded synthesis sweep (gate/manifest/merge)"
```

## Task C3: mise tasks for the synthesis sweep

**Files:**
- Modify: `mise.toml`

**Interfaces:**
- Produces: `meta:nightly:shard`, `meta:nightly:merge`, and `meta:nightly` — mirroring `parse:mathlib:shard`/`:merge`/`:nightly`. Shard/merge pass the `LEANR_SYNTH_*` flags through and pin the mutually-exclusive ones empty (`non_empty_env` treats empty as absent). `meta:nightly:merge` has no `elan:bootstrap` dep and pins `LEANR_MATHLIB_DIR`/`LEANR_OLEAN_PATH` empty.

- [ ] **Step 1: Add the tasks.** Model each `run` on the corresponding `parse:mathlib:*` task (section-3 report), substituting `LEANR_SYNTH_*` for `LEANR_SWEEP_*` and `-p leanr_meta --test synth_sweep` for the grammar test. `meta:nightly` runs `meta:nightly:merge`-after-shards is orchestrated by the workflow, not a single task — `meta:nightly` itself is the local unsharded convenience (one shard `1/1`, dump then diff then update). Do NOT set `RAYON_NUM_THREADS` in the tasks (the caller sets it).
- [ ] **Step 2: Verify task wiring.** Run: `mise tasks | grep meta:nightly`. Expected: the three tasks listed.
- [ ] **Step 3: Commit.**

```bash
git add mise.toml
git commit -m "feat(mise): meta:nightly synthesis sweep tasks (shard/merge/local)"
```

## Task C4: The separate GitHub workflow

**Files:**
- Create: `.github/workflows/nightly-synth-sweep.yml`

**Interfaces:**
- Produces: a scheduled 12-shard + merge workflow, structurally mirroring `nightly-sweep.yml`, with a DISTINCT `REBASELINE_BRANCH: nightly/mathlib-synth-passlist` and `PASSLIST: tests/fixtures/meta/synth-passlist.txt` so it never races the parse sweep.

Mirror `.github/workflows/nightly-sweep.yml` exactly (section-3 report), with these changes: a different `cron` time (avoid overlapping the parse sweep's `17 2 * * *`); each shard runs TWO steps — first `dump_synth_mathlib.lean` writing `LEANR_SYNTH_OUT`, then `mise run meta:nightly:shard` reading `LEANR_SYNTH_ORACLE=<that file>`; upload green + manifest; the merge job runs `mise run meta:nightly:merge`, applies the same "all 12 shards present per extension" guard, and force-pushes the re-baselined `synth-passlist.txt` to `nightly/mathlib-synth-passlist` with `gh pr edit`/`create --base main`. Keep `RAYON_NUM_THREADS: "3"`, `fail-fast: false`, `if-no-files-found: error`, `concurrency` no-cancel, `timeout-minutes: 300`/`90`.

- [ ] **Step 1: Write the workflow** by copying `nightly-sweep.yml` and applying the changes above. Add the Lean-dump step before the shard sweep step in the matrix job.
- [ ] **Step 2: Lint the YAML.** Run: `mise run ci` or a local `actionlint .github/workflows/nightly-synth-sweep.yml` if available. Expected: no syntax errors.
- [ ] **Step 3: Commit.**

```bash
git add .github/workflows/nightly-synth-sweep.yml
git commit -m "ci: separate nightly Mathlib synthesis sweep workflow"
```

## Task C5: PR-C gate + docs

**Files:**
- Modify: `AGENTS.md` (add a bullet documenting the synthesis nightly alongside the parse-sweep tiering)

- [ ] **Step 1: Document the sweep** in `AGENTS.md`: the two-tier synthesis verification (`meta:fast` regression gate, `meta:nightly` discovery via `nightly-synth-sweep.yml`), the distinct pass-list + re-baseline branch, and that shards shard by constant index (not import set) and each loads the full pinned environment. Mirror the existing parse-sweep bullets' precision.
- [ ] **Step 2: Full gate.** Run: `mise run ci`. Expected: green (the nightly tasks are `#[ignore]`d and not run by CI; only their build is checked).
- [ ] **Step 3: Confirm no kernel change.** Run: `git diff --stat main -- crates/leanr_kernel`. Expected: empty.
- [ ] **Step 4: Commit.**

```bash
git add AGENTS.md
git commit -m "docs: two-tier synthesis verification (meta:fast + meta:nightly)"
```

PR-C is complete and mergeable. M4a is complete.
