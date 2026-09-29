# M4b-4a P1 — structures and projections Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `e.1`, `e.f`, `e.f.{u}` and chains of them elaborate to the pinned oracle's term whenever the receiver's type is a structure or a one-constructor inductive. A general term in function position (`(f) a`) elaborates too.

**Architecture:**
- `leanr_olean` decodes `structureExt` into typed `StructureInfo` rows.
- `leanr_meta` exposes the `Structure.lean` accessors over them.
- `leanr_elab` gains `app/lval.rs`, a one-to-one port of `resolveLValAux` / `resolveLValLoop` / `consumeImplicits` / `mkBaseProjections` / `elabAppLValsAux`, restricted to the `projFn` / `projIdx` resolutions. `elabAppFn` in `app/head.rs` is restructured to thread an LVal list and to own the call into `elabAppArgs`, exactly as the oracle's does.
- Anything P2–P4 own raises a named seam naming its sub-plan.

**Tech Stack:** Rust (workspace crates `leanr_olean`, `leanr_meta`, `leanr_elab`), Lean 4 `v4.33.0-rc1` as the differential oracle, `mise` tasks.

**Spec:** `docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md` (§ P1). Read § Architecture, § P1, § Errors and § Testing before starting any task.

## Global Constraints

- Oracle is `leanprover/lean4:v4.33.0-rc1` (`lean-toolchain`). Never bump it.
- Every oracle `file:line` citation written into code or tests is opened against `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/Lean/...` first. Citations in this plan were opened while writing it, but re-open any you copy.
- `.olean` bytes are untrusted. Decoders return `OleanError`, never panic: no `unwrap`/`expect`/indexing on decoded data. Use `ctor`/`array`/`bad`.
- `leanr_meta` changes are additive and TCB-neutral (new accessors, no behaviour change on existing paths). `leanr_kernel` is untouched.
- No new dependencies.
- Named-seam discipline:
  - A construct owned by P2/P3/P4 or a later slice raises `ElabError::UnsupportedSyntax` whose message names the owner (`M4b-4a P2`, `M4b-4a P3`, `M4b-4a P4`, or a slice name). It never falls through to a different term.
  - Genuine oracle errors get typed variants, never `UnsupportedSyntax`.
- Every committed `elab-queries.jsonl` record must stay byte-identical except for records this plan adds.
- Every new test is shown to discriminate. The implementer applies the mutation named in the task, watches the test go red, reverts, and records the command and output in the task report.
- Before every push: `mise run ci`, blocking, to completion (fmt, clippy, full suite). A subagent must not background it.
- Fixture regeneration, never `mise run fixtures:regen` (which also touches Mathlib):
  - `cd tests/fixtures/elab && lean Elab0.lean -o Elab0.olean`
  - `mise run fixtures:regen-elab`

## Review Focus

These are the five input classes most likely to bite a user that no task's happy path exercises. Each has a test, added in the owning task.

1. **A recursor-named head followed by a projection** (`Nat.rec.1`) must not hit the `elabAsElim` seam. The oracle resolves the LVal on `Nat.rec`'s type and reports `OnFunction`. Test in Task 6.
2. **A seam must not trigger the unfold retry.** `fun (s : S3Alias) => (s).zzz` must raise the P3 seam, not `InvalidField`. Otherwise leanr reports an oracle-looking error for a path it never ran. Test in Task 5.
3. **`(self := …)` supplied by the user alongside field notation** must be `DuplicateNamedArg("self")`, as the oracle's `addNamedArg` reports. Test in Task 6.
4. **Projecting data out of a `Prop`** (`fun (h : PBox) => h.1`) must be `NonPropFromProp`, not a silently built `Expr.proj`. Test in Task 5.
5. **A dotted field token** (`(s).toS2.toS1`: one lexer token, two LVals) must split into components, not be looked up as the single name `toS2.toS1`. Corpus record in Task 6.

---

## File Structure

| File | Responsibility | Task |
|---|---|---|
| `tests/fixtures/elab/Elab0.lean` | new fixture declarations | 1 |
| `tests/fixtures/elab/dump_structs.lean` (new) | oracle dump of every fixture structure's `StructureInfo`, `findField?`, paths, resolution order | 1 |
| `tests/fixtures/elab/structures.jsonl` (new, generated) | that dump | 1 |
| `mise.toml` | `fixtures:regen-elab` also runs `dump_structs.lean` | 1 |
| `crates/leanr_olean/src/module_data.rs` | `StructureInfo` / `StructureFieldInfo` / `StructureParentInfo` types, `ModuleData::structures` | 2 |
| `crates/leanr_olean/src/interp_id.rs` | the `structureExt` decode | 2 |
| `crates/leanr_olean/src/lib.rs` | re-exports | 2 |
| `crates/leanr_meta/src/structure.rs` (new) | `StructureTable` + `MetaCtx` structure accessors | 3 |
| `crates/leanr_meta/src/metactx.rs` | `EnvExtensions::structures`, `MetaCtx::structures`, `pub` wrappers `unfold_definition_pub`/`instantiate1` | 3 |
| `crates/leanr_meta/tests/structures.rs` (new) | accessors vs `structures.jsonl` | 3 |
| `crates/leanr_meta/tests/support/mod.rs` + every `EnvExtensions {…}` / `Replayed {…}` site | plumbing | 3 |
| `crates/leanr_elab/src/app/mod.rs` | `AppCall`, `elab_app_args` (extracted), `elab_app_aux` rewired, `peel_head`/`elab_explicit` proj arms | 4, 7 |
| `crates/leanr_elab/src/app/head.rs` | `elab_app_fn` threads `lvals`, owns the call into `lval::elab_app_lvals`, proj / explicitUniv / hole / generic arms; `mk_const` extracted | 4, 5 |
| `crates/leanr_elab/src/app/lval.rs` (new) | the LVal machinery | 4, 5, 6 |
| `crates/leanr_elab/src/app/args.rs` | `numImplicitParams` arm | 6 |
| `crates/leanr_elab/src/error.rs` | new variants | 5 |
| `crates/leanr_elab/src/dispatch.rs` | route `Term.proj`; deferral table | 5, 7 |
| `crates/leanr_elab/src/elab.rs` | `is_mvar_app` → `pub(crate)` | 5 |
| `crates/leanr_elab/tests/lval_smoke.rs` (new) | rejections and seams | 5, 6, 7 |
| `crates/leanr_elab/tests/seam_audit.rs` | reconciled cases | 5, 7 |
| `tests/fixtures/elab/dump_elab.lean`, `elab-queries.jsonl` | new corpus records | 5, 6, 7 |
| `crates/leanr_elab/src/lib.rs`, `app/mod.rs` docs, spec § Landed | reconciliation | 7 |

---

### Task 1: Fixture declarations and the structure oracle dump

**Files:**
- Modify: `tests/fixtures/elab/Elab0.lean` (append before the end of the file)
- Create: `tests/fixtures/elab/dump_structs.lean`
- Create (generated): `tests/fixtures/elab/structures.jsonl`
- Modify: `mise.toml` (`[tasks."fixtures:regen-elab"]`)
- Regenerate: `tests/fixtures/elab/Elab0.olean`, `tests/fixtures/elab/elab-queries.jsonl`

**Interfaces:**
- Produces: fixture constants `S1 S2 S3 D1 D2 D3 One S3Alias Poly dflt PBox`. Also `structures.jsonl`, one JSON object per line and per structure declared in `Elab0`, sorted by name:
  `{"s": str, "fields": [str], "info": [{"f": str, "proj": str, "sub": str|null, "bi": "default"|"implicit"|"strictImplicit"|"instImplicit"}], "parents": [{"s": str, "sub": bool, "proj": str}], "order": [str], "paths": [{"base": str, "path": [str]|null}], "find": [{"f": str, "in": str|null}]}`
  - `info` is in the oracle's stored order (sorted by `Name.quickLt`), not re-sorted.
  - `paths` has one entry per element of `order`, including `s` itself, whose path is `[]`.
  - `find` has one entry per field name of every structure in `order`, plus `"zzz"`, deduplicated, in first-seen order.

- [ ] **Step 1: Append the declarations to `Elab0.lean`**

Every term below was checked against the pinned oracle on a scratch copy while writing this plan.

```lean
-- === M4b-4a P1: structures and projections ===
-- Subobject chain: `S3 extends S2 extends S1`. `(s).a` walks
-- `S3.toS2`, `S2.toS1` (`mkBaseProjections`, App.lean:1700-1710).
structure S1 where
  a : Nat
structure S2 extends S1 where
  b : Nat
structure S3 extends S2 where
  c : Nat
-- Diamond: `D2` shares `y` with `D1`, so it is a NON-subobject parent
-- of `D3` (its `z` is copied into `D3` as a direct field). Exercises
-- `getPathToBaseStructure?`'s parentInfo fallback (Structure.lean:338-356).
structure D1 where
  x : Nat
  y : Nat
structure D2 where
  y : Nat
  z : Nat
structure D3 extends D1, D2 where
  w : Nat
-- One-constructor `inductive`, not `structure`: `.i` builds `Expr.proj`
-- (`LValResolution.projIdx`, App.lean:1532-1540).
inductive One where
  | mk : Nat -> Nat -> One
-- A `def` alias: field access needs `resolveLValLoop`'s
-- `unfoldDefinition?` retry (App.lean:1687-1694).
def S3Alias : Type := S3
-- Universe-polymorphic structure, for `.{u}` on a field.
structure Poly (α : Type u) where
  val : α
-- Implicit leading binder: `(@dflt).1` needs `consumeImplicits`
-- (App.lean:1659-1676) before the projection resolves.
def dflt {_α : Type} : Prod Nat Nat := Prod.mk Nat.zero Nat.zero
-- A `Prop` with a data field: `.1` must be rejected by
-- `mkProjAndCheck` (App.lean:65-73).
inductive PBox : Prop where
  | mk : Nat -> PBox
```

If `Elab0.lean` has no `universe u` in scope at the append point, write `structure Poly (α : Type _)` instead. Check with `grep -n "^universe" tests/fixtures/elab/Elab0.lean`.

- [ ] **Step 2: Rebuild the olean and confirm the existing corpus is unchanged**

Run:
```bash
cd tests/fixtures/elab && lean Elab0.lean -o Elab0.olean && cd ../../.. \
  && mise run fixtures:regen-elab && git diff --stat tests/fixtures/elab/elab-queries.jsonl
```
Expected: `Elab0.olean` rebuilds with no errors, and `git diff --stat` on `elab-queries.jsonl` shows nothing. New declarations must not move any existing record.

- [ ] **Step 3: Write `dump_structs.lean`**

```lean
/- Dumps, for every structure declared in `Elab0`, the oracle's own
answers to the `Structure.lean` accessors leanr ports (M4b-4a P1, design
spec § Testing: "compared against values the oracle dumps ... never
hand-computed"). One JSON object per line, sorted by structure name.
Run with LEAN_PATH set to this directory (see `fixtures:regen-elab`). -/
import Lean
open Lean

def nameStr (n : Name) : String := n.toString (escape := false)

def biStr : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

def optName : Option Name → Json
  | none => Json.null
  | some n => Json.str (nameStr n)

unsafe def main : IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Elab0 }] {} (trustLevel := 0) (loadExts := true)
  let some modIdx := env.getModuleIdx? `Elab0
    | throw (IO.userError "dump_structs: Elab0 not loaded")
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    if env.getModuleIdxFor? n == some modIdx && isStructure env n then acc.push n else acc
  let names := names.qsort (fun a b => nameStr a < nameStr b)
  let coreCtx : Core.Context := { fileName := "<dump_structs>", fileMap := default }
  let coreState : Core.State := { env }
  let go : CoreM Unit := do
    for s in names do
      let some info := getStructureInfo? env s | unreachable!
      let order ← getStructureResolutionOrder s
      let paths := order.toList.map fun b =>
        Json.mkObj [("base", nameStr b),
          ("path", match getPathToBaseStructure? env b s with
            | none => Json.null
            | some p => Json.arr (p.map (Json.str ∘ nameStr)).toArray)]
      let mut seen : Array Name := #[]
      for t in order do
        for f in getStructureFields env t do
          unless seen.contains f do seen := seen.push f
      unless seen.contains `zzz do seen := seen.push `zzz
      let find := seen.toList.map fun f =>
        Json.mkObj [("f", nameStr f), ("in", optName (findField? env s f))]
      let j := Json.mkObj [
        ("s", nameStr s),
        ("fields", Json.arr (info.fieldNames.map (Json.str ∘ nameStr))),
        ("info", Json.arr (info.fieldInfo.map fun fi => Json.mkObj [
          ("f", nameStr fi.fieldName), ("proj", nameStr fi.projFn),
          ("sub", optName fi.subobject?), ("bi", biStr fi.binderInfo)])),
        ("parents", Json.arr (info.parentInfo.map fun p => Json.mkObj [
          ("s", nameStr p.structName), ("sub", p.subobject), ("proj", nameStr p.projFn)])),
        ("order", Json.arr (order.map (Json.str ∘ nameStr))),
        ("paths", Json.arr paths.toArray),
        ("find", Json.arr find.toArray)]
      IO.println j.compress
  discard <| go.toIO coreCtx coreState
```

If `env.getModuleIdx?` does not exist in the pinned toolchain, find the right accessor with `grep -n "def getModuleIdx" ~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/Lean/Environment.lean` and use that. Do not guess.

- [ ] **Step 4: Wire it into `fixtures:regen-elab` and generate**

In `mise.toml`, `[tasks."fixtures:regen-elab"]`, append to `run`:
```toml
  # M4b-4a P1: oracle answers for the structure accessors
  # (crates/leanr_meta/tests/structures.rs compares against these).
  "sh -c 'cd tests/fixtures/elab && LEAN_PATH=$PWD lean --run dump_structs.lean > structures.jsonl'",
```
Run: `mise run fixtures:regen-elab && wc -l tests/fixtures/elab/structures.jsonl && grep '"s":"S3"' tests/fixtures/elab/structures.jsonl`

Expected: one line per `Elab0` structure (≥ 20: classes count, since every `class` registers a `StructureInfo`). The `S3` line has `"fields":["toS2","c"]`, a `toS2` info entry with `"sub":"S2"`, and `paths` containing `{"base":"S1","path":["S3.toS2","S2.toS1"]}`. `elab-queries.jsonl` is still unchanged (`git diff --stat`).

- [ ] **Step 5: Commit**

```bash
git add tests/fixtures/elab/Elab0.lean tests/fixtures/elab/Elab0.olean \
  tests/fixtures/elab/dump_structs.lean tests/fixtures/elab/structures.jsonl mise.toml
git commit -m "fixtures: M4b-4a P1 structures and the structureExt oracle dump"
```

---

### Task 2: Decode `structureExt` in `leanr_olean`

**Files:**
- Modify: `crates/leanr_olean/src/module_data.rs` (types after `ProjectionFnInfo`, the `ModuleData` field, the multi-part merge at `ModuleData { … }` near `projection_fns: std::mem::take(…)`, and a test)
- Modify: `crates/leanr_olean/src/interp_id.rs` (decoder fns next to `projection_fn_pair`, an arm in `module_data`'s extension `match`, and the `ModuleData` literal)
- Modify: `crates/leanr_olean/src/lib.rs:217` (re-export list)

**Interfaces:**
- Produces (public in `leanr_olean`):
  ```rust
  pub struct StructureInfo { pub struct_name: NameId, pub field_names: Vec<NameId>,
      pub field_info: Vec<StructureFieldInfo>, pub parent_info: Vec<StructureParentInfo> }
  pub struct StructureFieldInfo { pub field_name: NameId, pub proj_fn: NameId,
      pub subobject: Option<NameId>, pub binder_info: leanr_kernel::BinderInfo }
  pub struct StructureParentInfo { pub struct_name: NameId, pub subobject: bool, pub proj_fn: NameId }
  // ModuleData gains:
  pub structures: Vec<StructureInfo>,
  ```
  All three derive `Debug, Clone`. `field_info` keeps the decoded order: `Name.quickLt`-sorted, which `getPathToBaseStructure?`'s `fieldInfo.firstM` depends on. Never re-sort it.

- [ ] **Step 1: Write the failing test** (in `module_data.rs`'s `mod tests`, next to `projection_fn_info_decodes`)

```rust
/// `structureExt` decodes (M4b-4a P1). The extension is registered
/// under a PRIVATE name — `_private.Lean.Structure.0.Lean.structureExt`
/// (probed with `readModuleData` on `Elab0.olean`), since
/// `Structure.lean:87` declares it `private builtin_initialize`. The
/// full oracle comparison lives in `leanr_meta/tests/structures.rs`;
/// this pins the three shapes the decoder must get right.
#[test]
fn structure_info_decodes() {
    let bytes = fixture("elab/Elab0.olean");
    let mut env = Environment::default();
    let md = ModuleData::parse(&bytes, env.store_mut()).expect("decode");
    let st = env.store();
    let render = |n: NameId| st.to_name(None, Some(n)).to_string();
    let find = |s: &str| {
        md.structures
            .iter()
            .find(|i| render(i.struct_name) == s)
            .unwrap_or_else(|| panic!("no StructureInfo for {s}; decoded {}", md.structures.len()))
    };
    // Constructor order, subobject field first.
    let s3 = find("S3");
    let fields: Vec<String> = s3.field_names.iter().map(|&n| render(n)).collect();
    assert_eq!(fields, ["toS2", "c"]);
    let to_s2 = s3.field_info.iter().find(|f| render(f.field_name) == "toS2").unwrap();
    assert_eq!(to_s2.subobject.map(render).as_deref(), Some("S2"));
    assert_eq!(render(to_s2.proj_fn), "S3.toS2");
    // Diamond: D2 is a non-subobject parent.
    let d3 = find("D3");
    let parents: Vec<(String, bool)> =
        d3.parent_info.iter().map(|p| (render(p.struct_name), p.subobject)).collect();
    assert_eq!(parents, [("D1".to_string(), true), ("D2".to_string(), false)]);
    // A class is a structure too, with an instImplicit-free field list.
    assert!(md.structures.iter().any(|i| render(i.struct_name) == "Add"));
}
```

- [ ] **Step 2: Run it and watch it fail**

Run: `cargo test -p leanr_olean --lib structure_info_decodes`
Expected: compile error (`no field structures on ModuleData`).

- [ ] **Step 3: Add the types and the `ModuleData` field** (`module_data.rs`, after `ProjectionFnInfo`)

```rust
/// One decoded `structureExt` entry: oracle `Lean.StructureInfo`
/// (`Structure.lean:60-67`, pinned toolchain v4.33.0-rc1):
///
/// ```text
/// structure StructureInfo where
///   structName : Name                       -- 0
///   fieldNames : Array Name                 -- 1 (constructor order)
///   fieldInfo  : Array StructureFieldInfo   -- 2 (sorted by Name.quickLt)
///   parentInfo : Array StructureParentInfo  -- 3 (`extends` order)
/// ```
///
/// `structureExt` (`Structure.lean:87-92`) is a plain
/// `registerPersistentEnvExtension` exporting a bare, `StructureInfo.lt`-
/// sorted array — no `ScopedEnvExtension.Entry` wrapper. It is declared
/// `private`, so its entries are keyed by the mangled
/// `_private.Lean.Structure.0.Lean.structureExt`. Every `structure` AND
/// every `class` registers one.
#[derive(Debug, Clone)]
pub struct StructureInfo {
    pub struct_name: NameId,
    pub field_names: Vec<NameId>,
    /// Decoded order, which is the oracle's `Name.quickLt` order.
    /// `getPathToBaseStructure?` walks it with `firstM`, so it must
    /// never be re-sorted.
    pub field_info: Vec<StructureFieldInfo>,
    pub parent_info: Vec<StructureParentInfo>,
}

/// oracle: `Lean.StructureFieldInfo` (`Structure.lean:25-36`). Four
/// pointer fields (`fieldName`, `projFn`, `subobject?`, `autoParam?`)
/// and one scalar byte (`binderInfo`, a 4-constructor enum packed into
/// the scalar tail — the same mechanism as `ProjectionFnInfo.fromClass`).
/// The deprecated `autoParam? : Option Expr` is shape-checked and dropped.
#[derive(Debug, Clone)]
pub struct StructureFieldInfo {
    pub field_name: NameId,
    pub proj_fn: NameId,
    pub subobject: Option<NameId>,
    pub binder_info: leanr_kernel::BinderInfo,
}

/// oracle: `Lean.StructureParentInfo` (`Structure.lean:48-55`). Two
/// pointer fields (`structName`, `projFn`) and one scalar byte
/// (`subobject : Bool`).
#[derive(Debug, Clone)]
pub struct StructureParentInfo {
    pub struct_name: NameId,
    pub subobject: bool,
    pub proj_fn: NameId,
}
```

Add `pub structures: Vec<StructureInfo>,` to `ModuleData` (doc: `/// Typed decode of the structureExt entries (M4b-4a P1). All other extension entries stay opaque.`). In the multi-part merge's `Ok(ModuleData { … })`, add `structures: std::mem::take(&mut base.structures),`. Re-export the three types from `lib.rs:217`.

- [ ] **Step 4: Write the decoder** (`interp_id.rs`, after `projection_fn_pair`)

```rust
/// `Lean.StructureInfo` — see `crate::StructureInfo`'s doc for the
/// layout and the private extension name.
fn structure_info(&mut self, r: &Raw) -> Result<crate::StructureInfo, OleanError> {
    let (f, _) = ctor(r, 0, 4, "StructureInfo")?;
    Ok(crate::StructureInfo {
        struct_name: self.name_req(&f[0])?,
        field_names: array(&f[1])?
            .iter()
            .map(|n| self.name_req(n))
            .collect::<Result<_, _>>()?,
        field_info: array(&f[2])?
            .iter()
            .map(|e| self.structure_field_info(e))
            .collect::<Result<_, _>>()?,
        parent_info: array(&f[3])?
            .iter()
            .map(|e| self.structure_parent_info(e))
            .collect::<Result<_, _>>()?,
    })
}

/// `Lean.StructureFieldInfo` (`Structure.lean:25-36`): 4 pointer
/// fields + `binderInfo` in the scalar tail. `BinderInfo`'s constructor
/// order is `default, implicit, strictImplicit, instImplicit`, the
/// same byte mapping `Expr`'s binder decode above uses.
fn structure_field_info(&mut self, r: &Raw) -> Result<crate::StructureFieldInfo, OleanError> {
    let (f, s) = ctor(r, 0, 4, "StructureFieldInfo")?;
    let field_name = self.name_req(&f[0])?;
    let proj_fn = self.name_req(&f[1])?;
    let subobject = self.opt_name(&f[2])?;
    // `autoParam? : Option Expr` — deprecated (`Structure.lean:34-35`),
    // shape-checked so a malformed entry is still a decode error, then
    // dropped.
    match &*f[3] {
        RawValue::Scalar(0) => {}
        RawValue::Ctor { tag: 1, fields, .. } if fields.len() == 1 => {}
        _ => return Err(bad("StructureFieldInfo.autoParam?")),
    }
    let binder_info = match s.first().copied() {
        Some(0) => BinderInfo::Default,
        Some(1) => BinderInfo::Implicit,
        Some(2) => BinderInfo::StrictImplicit,
        Some(3) => BinderInfo::InstImplicit,
        _ => return Err(bad("StructureFieldInfo.binderInfo")),
    };
    Ok(crate::StructureFieldInfo { field_name, proj_fn, subobject, binder_info })
}

/// `Lean.StructureParentInfo` (`Structure.lean:48-55`): 2 pointer
/// fields + `subobject : Bool` in the scalar tail.
fn structure_parent_info(&mut self, r: &Raw) -> Result<crate::StructureParentInfo, OleanError> {
    let (f, s) = ctor(r, 0, 2, "StructureParentInfo")?;
    Ok(crate::StructureParentInfo {
        struct_name: self.name_req(&f[0])?,
        proj_fn: self.name_req(&f[1])?,
        subobject: boolean(s.first(), "StructureParentInfo.subobject")?,
    })
}
```

In `module_data`, add `let mut structures = Vec::new();`, pass `structures,` into the `ModuleData` literal, and add this arm before `_ => continue`:

```rust
// Plain `registerPersistentEnvExtension` (`Structure.lean:87-92`):
// bare `StructureInfo` ctors, no scoped wrapper. PRIVATE, hence the
// mangled key — see `crate::StructureInfo`'s doc.
"_private.Lean.Structure.0.Lean.structureExt" => {
    for e in array(&pf[1])? {
        structures.push(self.structure_info(e)?);
    }
}
```

`BinderInfo` and `RawValue` are already in scope in `interp_id.rs`, because the `Expr` decode uses them. If `self.st.to_name(..).to_string()` renders the numeric component differently from `0`, the test fails with `decoded 0`. In that case print the key once (throwaway `eprintln!`, deleted before commit) and use its exact rendering.

- [ ] **Step 5: Run it and watch it pass**

Run: `cargo test -p leanr_olean --lib structure_info_decodes`
Expected: PASS. Then `cargo test -p leanr_olean` also passes: every other fixture decodes unchanged, and the `Mutations*.olean` decodes still fail or pass exactly as before.

If it fails with `BadShape { expected: "StructureFieldInfo" }` (or the parent variant), the pointer-field count is off. Probe `fields.len()` and `scalars` once with a throwaway `eprintln!`, fix the count, and record the observed layout in the struct doc.

- [ ] **Step 6: Mutation check**

Swap the `Some(0)`/`Some(1)` arms of the `binderInfo` match. `structure_info_decodes` still passes (it does not assert binder infos); Task 3's oracle comparison is what catches this. Record that and revert. Then change the key string to `"Lean.structureExt"`, confirm `structure_info_decodes` fails (`decoded 0`), and revert.

- [ ] **Step 7: Commit**

```bash
git add crates/leanr_olean
git commit -m "olean: decode structureExt (StructureInfo)"
```

---

### Task 3: Structure accessors in `leanr_meta`

**Files:**
- Create: `crates/leanr_meta/src/structure.rs`
- Modify: `crates/leanr_meta/src/lib.rs` (`mod structure;`)
- Modify: `crates/leanr_meta/src/metactx.rs`: `EnvExtensions` (line ~299) gains `structures`; `MetaCtx` gains `pub(crate) structures: StructureTable` (built in `new`); two `pub` wrappers at the end of `impl MetaCtx`
- Modify: `crates/leanr_meta/tests/support/mod.rs` (`Replayed` gains `structures`)
- Modify every `EnvExtensions { … }` literal and every exhaustive `Replayed { … }` destructure:
  - `crates/leanr_meta/src/test_support.rs:185,235,391,439,654`
  - `crates/leanr_meta/tests/oracle_synth.rs:65,154,489,583`
  - `crates/leanr_meta/tests/oracle_fast.rs:88`
  - `crates/leanr_elab/tests/oracle_elab.rs:29,95`
  - `crates/leanr_elab/tests/binder_smoke.rs:20,47`
  - `crates/leanr_elab/tests/support/mod.rs:46,75,730,760`
- Create: `crates/leanr_meta/tests/structures.rs`

**Interfaces:**
- Consumes: `leanr_olean::{StructureInfo, StructureFieldInfo}` (Task 2), `structures.jsonl` (Task 1).
- Produces, all `pub` on `MetaCtx` and all read-only:
  ```rust
  pub fn get_structure_info(&self, s: NameId) -> Option<&StructureInfo>
  pub fn is_structure(&self, s: NameId) -> bool
  pub fn get_structure_fields(&self, s: NameId) -> &[NameId]            // [] when not a structure
  pub fn get_field_info(&self, s: NameId, field: NameId) -> Option<&StructureFieldInfo>
  pub fn get_structure_subobjects(&self, s: NameId) -> Vec<NameId>
  pub fn find_field(&self, s: NameId, field: NameId) -> Option<NameId>
  pub fn get_path_to_base_structure(&self, base: NameId, s: NameId) -> Option<Vec<NameId>>
  pub fn unfold_definition_pub(&mut self, e: ExprId) -> Result<Option<ExprId>, MetaError>
  pub fn instantiate1(&mut self, body: ExprId, val: ExprId) -> Result<ExprId, MetaError>
  ```
  `EnvExtensions` gains `pub structures: &'a [StructureInfo]`, and `Replayed` gains `pub structures: Vec<StructureInfo>`.

- [ ] **Step 1: Write the failing test** (`crates/leanr_meta/tests/structures.rs`)

```rust
//! M4b-4a P1: `MetaCtx`'s structure accessors against the oracle's own
//! answers (`tests/fixtures/elab/structures.jsonl`, written by
//! `dump_structs.lean`). Every value compared here was computed by the
//! pinned oracle, none by hand (design spec § Testing).

mod support;

use leanr_kernel::bank::Store;
use leanr_meta::{Config, EnvExtensions, MetaCtx};
use serde_json::Value;
use support::*;

#[test]
fn structure_accessors_match_the_oracle_dump() {
    let r = replay_fixture_in("elab", "Elab0.olean");
    let view = r.env.view();
    let mut scratch = Store::scratch();
    let base = Some(view.store);
    let text = std::fs::read_to_string(fixture_in("elab", "structures.jsonl")).unwrap();
    // Intern every name we will look up BEFORE building the MetaCtx,
    // which borrows `scratch` mutably for its lifetime.
    let recs: Vec<Value> = text.lines().map(|l| serde_json::from_str(l).unwrap()).collect();
    let mut name = |s: &str| decode_name(&mut scratch, base, s);
    let mut probes = Vec::new();
    for rec in &recs {
        let s = rec["s"].as_str().unwrap();
        let sid = name(s);
        let finds: Vec<_> = rec["find"].as_array().unwrap().iter()
            .map(|f| (name(f["f"].as_str().unwrap()), f["in"].as_str().map(str::to_string)))
            .collect();
        let paths: Vec<_> = rec["paths"].as_array().unwrap().iter()
            .map(|p| (name(p["base"].as_str().unwrap()),
                      p["path"].as_array().map(|a| a.iter().map(|x| x.as_str().unwrap().to_string()).collect::<Vec<_>>())))
            .collect();
        probes.push((s.to_string(), sid, finds, paths, rec.clone()));
    }
    let nat = name("Nat");
    let ctx = MetaCtx::new(view, &mut scratch, Config::default(), EnvExtensions {
        structures: &r.structures,
        ..Default::default()
    });
    let render = |n| name_to_string(ctx.store(), base, Some(n));
    assert!(probes.len() >= 20, "expected every Elab0 structure, got {}", probes.len());
    for (s, sid, finds, paths, rec) in probes {
        assert!(ctx.is_structure(sid), "{s}: not a structure");
        let fields: Vec<String> = ctx.get_structure_fields(sid).iter().map(|&n| render(n)).collect();
        let want: Vec<String> = rec["fields"].as_array().unwrap().iter().map(|x| x.as_str().unwrap().to_string()).collect();
        assert_eq!(fields, want, "{s}: fields");
        let info = ctx.get_structure_info(sid).unwrap();
        let got_info: Vec<Value> = info.field_info.iter().map(|fi| serde_json::json!({
            "f": render(fi.field_name), "proj": render(fi.proj_fn),
            "sub": fi.subobject.map(render), "bi": encode_bi(fi.binder_info)})).collect();
        assert_eq!(Value::Array(got_info), rec["info"], "{s}: fieldInfo (order included)");
        let got_parents: Vec<Value> = info.parent_info.iter().map(|p| serde_json::json!({
            "s": render(p.struct_name), "sub": p.subobject, "proj": render(p.proj_fn)})).collect();
        assert_eq!(Value::Array(got_parents), rec["parents"], "{s}: parentInfo");
        for (f, want) in finds {
            assert_eq!(ctx.find_field(sid, f).map(render), want, "{s}: findField? {}", render(f));
        }
        for (b, want) in paths {
            let got = ctx.get_path_to_base_structure(b, sid)
                .map(|p| p.into_iter().map(render).collect::<Vec<_>>());
            assert_eq!(got, want, "{s}: getPathToBaseStructure? {}", render(b));
        }
    }
    // A non-structure answers "no" without panicking (the oracle's
    // `getStructureInfo` panics; untrusted input forbids that here).
    assert!(!ctx.is_structure(nat));
    assert!(ctx.get_structure_fields(nat).is_empty());
    assert!(ctx.find_field(nat, nat).is_none());
    assert!(ctx.get_path_to_base_structure(nat, nat).is_some()); // base == s: `[]`, as the oracle
}
```

`encode_bi` must render `BinderInfo` as `"default"`/`"implicit"`/`"strictImplicit"`/`"instImplicit"`; check `support::encode_bi` (`tests/support/mod.rs:453`) and adapt the `json!` if its spelling differs from the dumper's `biStr`.

- [ ] **Step 2: Run it and watch it fail**

Run: `cargo test -p leanr_meta --test structures`
Expected: compile errors (`no field structures`, `no method is_structure`).

- [ ] **Step 3: Implement `structure.rs`**

```rust
//! Structure accessors — M4b-4a P1. Oracle: `Lean/Structure.lean`
//! (pinned v4.33.0-rc1). Additive and TCB-neutral: read-only views over
//! decoded `structureExt` rows. Where the oracle `panic!`s on a
//! non-structure (`getStructureInfo`, `:143-155`), these return an
//! empty answer instead — `.olean` input is untrusted and the elaborator
//! only ever asks after an `is_structure` guard anyway.

use std::collections::{HashMap, HashSet};

use leanr_kernel::bank::NameId;
use leanr_olean::{StructureFieldInfo, StructureInfo};

use crate::MetaCtx;

/// Keyed by structure name. The oracle binary-searches per-module
/// sorted arrays (`getStructureInfo?`, `:126-129`); a point-lookup map
/// answers the same question (names are unique per environment).
#[derive(Default)]
pub(crate) struct StructureTable {
    by_name: HashMap<NameId, StructureInfo>,
}

impl StructureTable {
    pub(crate) fn build(entries: &[StructureInfo]) -> Self {
        StructureTable {
            by_name: entries.iter().map(|i| (i.struct_name, i.clone())).collect(),
        }
    }
}

impl<'e> MetaCtx<'e> {
    /// oracle: `getStructureInfo?` (`Structure.lean:126-129`).
    pub fn get_structure_info(&self, s: NameId) -> Option<&StructureInfo> {
        self.structures.by_name.get(&s)
    }

    /// oracle: `isStructure` (`:270-271`).
    pub fn is_structure(&self, s: NameId) -> bool {
        self.structures.by_name.contains_key(&s)
    }

    /// oracle: `getStructureFields` (`:157-158`), constructor order.
    pub fn get_structure_fields(&self, s: NameId) -> &[NameId] {
        self.get_structure_info(s).map_or(&[], |i| &i.field_names)
    }

    /// oracle: `getFieldInfo?` (`:161-165`).
    pub fn get_field_info(&self, s: NameId, field: NameId) -> Option<&StructureFieldInfo> {
        self.get_structure_info(s)?.field_info.iter().find(|f| f.field_name == field)
    }

    /// oracle: `getStructureSubobjects` (`:189-190`) — the subobject
    /// parents, in FIELD (constructor) order.
    pub fn get_structure_subobjects(&self, s: NameId) -> Vec<NameId> {
        self.get_structure_fields(s)
            .iter()
            .filter_map(|&f| self.get_field_info(s, f)?.subobject)
            .collect()
    }

    /// oracle: `findField?` (`:197-201`).
    pub fn find_field(&self, s: NameId, field: NameId) -> Option<NameId> {
        if self.get_structure_fields(s).contains(&field) {
            return Some(s);
        }
        self.get_structure_subobjects(s)
            .into_iter()
            .find_map(|p| self.find_field(p, field))
    }

    /// oracle: `getPathToBaseStructure?` (`:338-356`). Subobject fields
    /// first, in `fieldInfo` (`Name.quickLt`) order — NOT constructor
    /// order — then other parents in `extends` order, with a visited set
    /// shared across the whole search (the oracle's `StateM NameSet`).
    pub fn get_path_to_base_structure(&self, base: NameId, s: NameId) -> Option<Vec<NameId>> {
        let mut visited = HashSet::new();
        let mut path = Vec::new();
        if self.path_go(base, s, &mut path, &mut visited) {
            Some(path)
        } else {
            None
        }
    }

    fn path_go(
        &self,
        base: NameId,
        s: NameId,
        path: &mut Vec<NameId>,
        visited: &mut HashSet<NameId>,
    ) -> bool {
        if base == s {
            return true;
        }
        if !visited.insert(s) {
            return false;
        }
        let Some(info) = self.get_structure_info(s) else {
            return false;
        };
        for f in &info.field_info {
            if let Some(parent) = f.subobject {
                path.push(f.proj_fn);
                if self.path_go(base, parent, path, visited) {
                    return true;
                }
                path.pop();
            }
        }
        for p in &info.parent_info {
            path.push(p.proj_fn);
            if self.path_go(base, p.struct_name, path, visited) {
                return true;
            }
            path.pop();
        }
        false
    }
}
```

**Check the visited-set semantics against the oracle before trusting this.** In `getPathToBaseStructure?`, `modify (·.insert structName)` happens inside the `OptionT (StateM NameSet)`, and `<|>` on `OptionT` over `StateM` does **not** roll back state on failure. So a node visited on a failed branch stays visited, and the port above matches that. The `diamond` rows of `structures.jsonl` are the arbiter: if a path mismatches, re-read `:338-356` and fix the port, not the test.

- [ ] **Step 4: Wire it into `MetaCtx` and `EnvExtensions`**

In `metactx.rs`:
- Add `pub structures: &'a [StructureInfo],` to `EnvExtensions`, with the doc `/// Decoded structureExt entries (M4b-4a P1) — see crate::structure.` and a `leanr_olean::StructureInfo` import.
- Add a field `pub(crate) structures: crate::structure::StructureTable,` to `MetaCtx`.
- In `new`, add `let structures = crate::structure::StructureTable::build(exts.structures);` and put `structures` in the literal.

Append to `impl MetaCtx`:

```rust
/// `unfold_definition` (`whnf.rs`), exposed for `leanr_elab`'s
/// `resolveLValLoop` retry (`App.lean:1690`) — the M4b elab→meta
/// accessor precedent: additive, no new state, no behaviour change.
pub fn unfold_definition_pub(&mut self, e: ExprId) -> Result<Option<ExprId>, MetaError> {
    self.unfold_definition(e)
}

/// oracle: `Expr.instantiate1` — substitute `val` for `#0` in `body`,
/// with NO beta step (unlike `instantiate_beta_rev_range`).
/// `consumeImplicits` (`App.lean:1665`) needs exactly this.
pub fn instantiate1(&mut self, body: ExprId, val: ExprId) -> Result<ExprId, MetaError> {
    let base = Some(self.view.store);
    let out = leanr_kernel::subst::instantiate(self.scratch, base, body, val, &mut self.guard)?;
    Ok(out)
}
```

Adapt `instantiate1` to however `metactx.rs` already calls `leanr_kernel::subst::instantiate_rev` (it has a caller in `instantiate_beta_rev_range`). Copy that call's `store`/`base`/`guard` arguments exactly. Do not invent new ones.

Plumbing:
- Add `pub structures: Vec<StructureInfo>` to `Replayed`, filled with `structures: md.structures,`.
- At every `EnvExtensions { … }` literal listed under **Files**, add `structures: &structures,`, binding it in the matching `Replayed { … }` destructure.
- Where a site destructures `Replayed` exhaustively but does not need structures (the `leanr_meta` ones), add `structures: _,`.
- Let the compiler find any missed site: `cargo build --workspace --tests`.

- [ ] **Step 5: Run it and watch it pass**

Run: `cargo test -p leanr_meta --test structures`, then `cargo test -p leanr_meta -p leanr_elab`.
Expected: PASS, and every existing test passes (plumbing only).

- [ ] **Step 6: Mutation checks**

For each mutation below, confirm `structures` fails with a message naming a real structure, then revert:
- (a) In `path_go`, swap the two loops (parents before subobjects).
- (b) In `find_field`, drop the subobject recursion.
- (c) Task 2's binder-info byte swap: `fieldInfo` fails on a class field.

Record the three failure lines.

- [ ] **Step 7: Commit**

```bash
git add crates/leanr_meta crates/leanr_elab/tests
git commit -m "meta: structure accessors over structureExt (M4b-4a P1)"
```

---

### Task 4: Restructure `elabAppFn` to own `elabAppArgs` (no behaviour change)

The oracle's `elabAppFn` (`App.lean:2060-2139`) threads an `lvals` list and itself calls `elabAppLVals`, which calls `elabAppArgs`. Its generic arm returns an already-elaborated term that must not be re-applied. leanr's `elab_app_fn` returns a bare head and lets `elab_app_aux` call `args::main`, and that shape cannot express either behaviour. This task changes the shape and nothing else.

**Files:**
- Modify: `crates/leanr_elab/src/app/mod.rs` (`AppCall`, `elab_app_args`, `elab_app_aux`, `pub mod lval;`)
- Modify: `crates/leanr_elab/src/app/head.rs` (`elab_app_fn` signature; `mk_const` extracted from `elab_ident_head`)
- Create: `crates/leanr_elab/src/app/lval.rs` (the `LVal` type and a pass-through `elab_app_lvals`)

**Interfaces:**
- Produces:
  ```rust
  // app/mod.rs
  pub struct AppCall { pub named_args: Vec<NamedArg>, pub args: Vec<Arg>,
      pub expected: Option<ExprId>, pub explicit: bool, pub ellipsis: bool, pub stx: SynElem }
  pub(crate) fn elab_app_args(elab: &mut TermElabM, f: ExprId, call: AppCall, kinds: &KindInterner)
      -> Result<ExprId, ElabError>          // oracle `elabAppArgs`, App.lean:1351-1394
  // app/head.rs
  pub fn elab_app_fn(elab: &mut TermElabM, f: &SynElem, kinds: &KindInterner,
      explicit_levels: &[LevelId], lvals: Vec<LVal>, call: AppCall) -> Result<Vec<ExprId>, ElabError>
  pub(crate) fn mk_const(elab: &mut TermElabM, cname: NameId, explicit_levels: &[LevelId],
      display: &str) -> Result<ExprId, ElabError>   // oracle `mkConst`, TermElabM.lean:2117-2126
  // app/lval.rs
  pub enum LVal { FieldName { r#ref: SynElem, name: String, levels: Vec<LevelId> },
                  FieldIdx  { r#ref: SynElem, idx: usize,  levels: Vec<LevelId> } }
  pub fn elab_app_lvals(elab: &mut TermElabM, f: ExprId, lvals: Vec<LVal>, call: AppCall,
      kinds: &KindInterner) -> Result<ExprId, ElabError>
  ```
  `elab_app_fn` now returns **finished** candidates (the oracle's `TermElabResult` array), and `elab_app_aux` only picks the single one.

- [ ] **Step 1: Pin today's behaviour**

Run: `cargo test -p leanr_elab 2>&1 | tail -3`. Record the pass count. This task is a pure refactor, so it adds no test: the full suite plus `oracle_elab_gate` are the test, and they must stay green with identical counts.

- [ ] **Step 2: Extract `mk_const`** (`head.rs`)

Move the tail of `elab_ident_head` into `mk_const`, from `let n_params = …` through the `expr_const` call. Keep every comment with the code it describes. `display` replaces `raw` in the `TooManyUniverseLevels` error. `elab_ident_head` then ends with `mk_const(elab, cname, explicit_levels, raw)`.

- [ ] **Step 3: Add `AppCall` and extract `elab_app_args`** (`mod.rs`)

```rust
/// The arguments of one application, as `elabAppFn` threads them
/// (`App.lean:2060-2061`: `namedArgs args expectedType? explicit
/// ellipsis`). Grouped so the recursion in `head::elab_app_fn` and the
/// LVal loop in `lval::elab_app_lvals` pass one value, not six.
/// `stx` is `Context::stx` (the WHOLE application — see that field's doc).
pub struct AppCall {
    pub named_args: Vec<NamedArg>,
    pub args: Vec<Arg>,
    pub expected: Option<ExprId>,
    pub explicit: bool,
    pub ellipsis: bool,
    pub stx: SynElem,
}
```

Move everything in `elab_app_aux` after `let f = overload::expect_single(candidates)?;` into `pub(crate) fn elab_app_args(elab, f, call, kinds)`, reading `call.*` where it read the locals. Keep every comment. The `elabAsElim` block stays attached to it. `elab_app_aux` becomes:

```rust
fn elab_app_aux(
    elab: &mut TermElabM,
    head: &SynElem,
    kinds: &KindInterner,
    named_args: Vec<NamedArg>,
    args: Vec<Arg>,
    ellipsis: bool,
    expected: Option<ExprId>,
    stx: SynElem,
) -> Result<ExprId, ElabError> {
    let (head, explicit, explicit_levels) = peel_head(elab, head, kinds)?;
    let call = AppCall { named_args, args, expected, explicit, ellipsis, stx };
    let candidates = head::elab_app_fn(elab, &head, kinds, &explicit_levels, Vec::new(), call)?;
    overload::expect_single(candidates)
}
```

Check `overload::expect_single`'s signature. If it returns `Result<ExprId, _>` already, this compiles as written.

- [ ] **Step 4: Create `lval.rs` with the type and a pass-through**

```rust
//! M4b-4a: the LVal machinery — dot notation's field and index
//! projections. Oracle: `Lean/Elab/App.lean:1435-1897` (pinned
//! v4.33.0-rc1). Design: docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md.

use leanr_kernel::bank::{ExprId, LevelId};
use leanr_syntax::kind::KindInterner;

use crate::app::AppCall;
use crate::dispatch::SynElem;
use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `inductive LVal` (`TermElabM.lean:662-672`). The
/// `suffix?`/`fullRef` fields of `fieldName` only feed the
/// unknown-name error of an identifier-embedded field, which is P4's
/// (`resolveName`'s field split); they are added there.
#[derive(Debug, Clone)]
pub enum LVal {
    FieldName { r#ref: SynElem, name: String, levels: Vec<LevelId> },
    FieldIdx { r#ref: SynElem, idx: usize, levels: Vec<LevelId> },
}

/// oracle: `elabAppLVals` / `elabAppLValsAux` (`App.lean:1843-1897`).
pub fn elab_app_lvals(
    elab: &mut TermElabM,
    f: ExprId,
    lvals: Vec<LVal>,
    call: AppCall,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    if lvals.is_empty() {
        return crate::app::elab_app_args(elab, f, call, kinds);
    }
    Err(ElabError::UnsupportedSyntax(
        "field projection — M4b-4a P1 (lval.rs)".to_string(),
    ))
}
```

The non-empty arm is unreachable in this task: no producer of a non-empty `lvals` exists yet. Task 5 replaces it.

- [ ] **Step 5: Rewire `elab_app_fn`**

Change the signature to the one in **Interfaces**. The `<ident>` arm becomes:

```rust
("<ident>", leanr_syntax::tree::NodeOrToken::Token(tok)) => {
    // `elabAsElim?` runs inside `elabAppArgs` on the FINAL head
    // (`App.lean:1373`). With LVals pending, the identifier is not
    // that head — `resolveLVal` consumes it first — so the recursor
    // guard must not fire (plan § Review Focus 1).
    let heed = !call.explicit && !call.ellipsis && lvals.is_empty();
    let f = elab_ident_head(elab, tok.text(), explicit_levels, heed)?;
    Ok(vec![crate::app::lval::elab_app_lvals(elab, f, lvals, call, kinds)?])
}
```

The other two arms keep their seam errors unchanged. Update the module doc's first paragraph: `elab_app_fn` now returns finished candidates, as the oracle's `elabAppFn` does.

- [ ] **Step 6: Run the suite**

Run: `cargo test -p leanr_elab 2>&1 | tail -3 && cargo clippy -p leanr_elab --all-targets -- -D warnings`
Expected: same pass count as Step 1, `oracle_elab_gate` green, no clippy warnings.

- [ ] **Step 7: Commit**

```bash
git add crates/leanr_elab/src
git commit -m "elab: elab_app_fn owns elabAppArgs and threads LVals (refactor, no behaviour change)"
```

---

### Task 5: Index projections, the resolution loop, and general heads

**Files:**
- Modify: `crates/leanr_elab/src/error.rs` (new variants)
- Modify: `crates/leanr_elab/src/app/lval.rs` (resolution machinery; the `ProjIdx` path)
- Modify: `crates/leanr_elab/src/app/head.rs` (`proj`, `explicitUniv`, `hole` and generic arms)
- Modify: `crates/leanr_elab/src/dispatch.rs` (route `Lean.Parser.Term.proj` to `app::elab_atom`, register it in `elaborator_name_for`)
- Modify: `crates/leanr_elab/src/elab.rs:563` (`fn is_mvar_app` → `pub(crate)`)
- Create: `crates/leanr_elab/tests/lval_smoke.rs`
- Modify: `crates/leanr_elab/tests/seam_audit.rs` (cases that now elaborate or error)
- Modify: `tests/fixtures/elab/dump_elab.lean` (+ `lvalIdxQueries`), regenerate `elab-queries.jsonl`

**Interfaces:**
- Consumes: `AppCall`, `elab_app_args`, `LVal`, `mk_const` (Task 4); `MetaCtx::{is_structure, get_structure_fields, find_field, unfold_definition_pub, instantiate1}` (Task 3).
- Produces (in `error.rs`):
  ```rust
  InvalidProjection { e: ExprId, e_type: ExprId, reason: InvalidProjectionReason },
  InvalidField { e: ExprId, e_type: ExprId, field: String, reason: InvalidFieldReason },
  PlaceholderAsFunction,
  Internal(String),
  pub enum InvalidProjectionReason { IndexZero, IndexOutOfRange { idx: usize, num_fields: usize },
      NoFields, NotOneCtor, OnFunction, TypeUnknown, NotConstApp, ExplicitUnivsOnInductive, NonPropFromProp }
  pub enum InvalidFieldReason { NotFound { full_name: String }, TypeUnknown, NotConstApp }
  ```
  Also, in `lval.rs`: `enum LValResolution { ProjFn{..}, ProjIdx{ struct_name: NameId, idx: usize } }`, `fn resolve_lval`, `fn resolve_lval_loop`, `fn resolve_lval_aux`, `fn consume_implicits`, `fn mk_proj_and_check`. Task 6 fills `ProjFn`.

- [ ] **Step 1: Write the failing corpus records and smoke tests**

In `dump_elab.lean`, add after `nondepQueries` and append `++ lvalIdxQueries` to `main`'s `for` list:

```lean
/-- M4b-4a P1 task 5: `projIdx` (one-constructor `inductive`,
`App.lean:1532-1540`) and `elabAppFn`'s generic arm
(`App.lean:2120-2138`). Every one checked against the pinned oracle. -/
def lvalIdxQueries : List (String × String) :=
  [ ("lval/idx-one-second",       "fun (o : One) => o.2")
  , ("lval/idx-one-first",        "fun (o : One) => o.1")
  , ("lval/generic-paren-head",   "(Nat.succ) Nat.zero")
  , ("lval/generic-fun-head",     "(fun (x : Nat) => x) Nat.zero")
  ]
```

Run `mise run fixtures:regen-elab`, then `git diff tests/fixtures/elab/elab-queries.jsonl`. Expected: exactly four added lines. `o.2`'s record has `"k":"proj"` with `"s":"One","i":1`.

Create `crates/leanr_elab/tests/lval_smoke.rs`:

```rust
//! M4b-4a: dot-notation rejections and seams. The corpus
//! (`oracle_elab.rs`) is success-only, so every oracle ERROR this
//! slice ports is pinned here by variant and reason. Each case was run
//! on the pinned oracle (`lean` on a prelude-mode scratch file importing
//! `Elab0`, `LEAN_PATH=tests/fixtures/elab`) before it was written; the
//! oracle's message is quoted beside it.

mod support;

use leanr_elab::{ElabError, InvalidFieldReason, InvalidProjectionReason};

fn proj_reason(src: &str) -> InvalidProjectionReason {
    match support::elab_and_synthesize(src) {
        Err(ElabError::InvalidProjection { reason, .. }) => reason,
        other => panic!("{src}: expected InvalidProjection, got {other:?}"),
    }
}

fn seam(src: &str) -> String {
    match support::elab_and_synthesize(src) {
        Err(ElabError::UnsupportedSyntax(m)) => m,
        other => panic!("{src}: expected a named seam, got {other:?}"),
    }
}

#[test]
fn projection_rejections_match_the_oracle() {
    // "…which is not a one-constructor inductive type."
    assert_eq!(proj_reason("(Nat.zero).1"), InvalidProjectionReason::NotOneCtor);
    // "Index `3` is invalid for this structure; it must be between 1 and 2"
    assert_eq!(
        proj_reason("fun (o : One) => o.3"),
        InvalidProjectionReason::IndexOutOfRange { idx: 3, num_fields: 2 }
    );
    // "Projections cannot be used on functions"
    assert_eq!(proj_reason("fun (f : Nat -> Nat) => f.1"), InvalidProjectionReason::OnFunction);
    // "Projection operates on types of the form `C ...`" — a sort, and an fvar.
    assert_eq!(proj_reason("fun (x : Type) => x.1"), InvalidProjectionReason::NotConstApp);
    assert_eq!(proj_reason("fun (a : Type) (x : a) => x.1"), InvalidProjectionReason::NotConstApp);
    // "Explicit universe levels are only supported for inductive types
    // defined using the `structure` command."
    assert_eq!(
        proj_reason("fun (o : One) => o.1.{0}"),
        InvalidProjectionReason::ExplicitUnivsOnInductive
    );
    // Review Focus 4 — lean.projNonPropFromProp.
    assert_eq!(proj_reason("fun (h : PBox) => h.1"), InvalidProjectionReason::NonPropFromProp);
}

#[test]
fn field_rejections_match_the_oracle() {
    // "The environment does not contain `Function.zzz`"
    match support::elab_and_synthesize("fun (f : Nat -> Nat) => (f).zzz") {
        Err(ElabError::InvalidField { reason: InvalidFieldReason::NotFound { full_name }, .. }) => {
            assert_eq!(full_name, "Function.zzz")
        }
        other => panic!("expected InvalidField NotFound, got {other:?}"),
    }
    // "Field projection operates on types of the form `C ...`"
    match support::elab_and_synthesize("fun (a : Type) (x : a) => (x).foo") {
        Err(ElabError::InvalidField { reason: InvalidFieldReason::NotConstApp, .. }) => {}
        other => panic!("expected InvalidField NotConstApp, got {other:?}"),
    }
}

#[test]
fn placeholder_head_is_rejected() {
    // "A placeholder `_` cannot be used where a function is expected"
    assert!(matches!(
        support::elab_and_synthesize("_ Nat.zero"),
        Err(ElabError::PlaceholderAsFunction)
    ));
}

#[test]
fn p2_p3_p4_constructs_are_named_seams() {
    // tryPostponeIfMVar (App.lean:1680) — P2 owns postponement.
    assert!(seam("fun x => x.1").contains("M4b-4a P2"));
    // `.const` resolution via findMethod? — P3.
    assert!(seam("(Nat.zero).succ").contains("M4b-4a P3"));
    // Review Focus 2: a seam is NOT retried through `unfoldDefinition?`
    // — S3Alias must seam, never report S3's InvalidField.
    assert!(seam("fun (s : S3Alias) => (s).zzz").contains("M4b-4a P3"));
}
```

Export `InvalidFieldReason` and `InvalidProjectionReason` from `crates/leanr_elab/src/lib.rs` next to `ElabError`, and derive `Debug, Clone, PartialEq, Eq` on both.

- [ ] **Step 2: Run and watch them fail**

Run: `cargo test -p leanr_elab --test lval_smoke; cargo test -p leanr_elab --test oracle_elab`
Expected: `lval_smoke` fails to compile (no such variants). `oracle_elab_gate` fails on `lval/*` with `UnsupportedSyntax("Lean.Parser.Term.proj")` and the head seam.

- [ ] **Step 3: Add the error variants** (`error.rs`)

```rust
/// oracle: `resolveLValAux`'s `fieldIdx` throws (`App.lean:1520-1551`,
/// `:1589-1591`, `:1601-1603`, `:1614-1617`) and `mkProjAndCheck`'s
/// `lean.projNonPropFromProp` (`:65-73`). Prose deferred (design spec
/// § Errors); `reason` identifies the throw site.
InvalidProjection { e: ExprId, e_type: ExprId, reason: InvalidProjectionReason },
/// oracle: `resolveLValAux`'s `fieldName` throws (`:1578`, `:1588`,
/// `:1593-1600`, `:1609-1612`).
InvalidField { e: ExprId, e_type: ExprId, field: String, reason: InvalidFieldReason },
/// oracle: `elabAppFn`'s `` `(_) `` arm (`App.lean:2119`).
PlaceholderAsFunction,
/// An oracle `panic!`/`unreachable!` site (`mkBaseProjections`,
/// `App.lean:1704`, `:1708`): unreachable on a well-formed environment,
/// an error rather than a panic here because `.olean` input is untrusted.
Internal(String),
```

Define the two reason enums below `ElabError`, with one `///` line per variant citing its oracle line from the table above. `IndexZero`'s doc notes that it is unreachable from source, because the `fieldIdx` token rejects `0`: `(o).0` is a parse error in both implementations.

- [ ] **Step 4: Implement the resolution machinery** (`lval.rs`)

Add these imports: `leanr_kernel::bank::{NameId}`, `leanr_kernel::bank::terms::Node`, `leanr_kernel::{BinderInfo, Nat}`, `crate::error::{InvalidFieldReason, InvalidProjectionReason}`.

```rust
impl LVal {
    fn r#ref(&self) -> &SynElem {
        match self {
            LVal::FieldName { r#ref, .. } | LVal::FieldIdx { r#ref, .. } => r#ref,
        }
    }
}

/// oracle: `LValResolution` (`App.lean:1435-1447`). P1 ports the two
/// arms that need no namespace search; `const` is P3's and `localRec`
/// needs `auxDeclToFullName`, which has no leanr producer (the
/// `let rec` slice).
enum LValResolution {
    ProjFn { base: NameId, struct_name: NameId, field: NameId, levels: Vec<LevelId> },
    ProjIdx { struct_name: NameId, idx: usize },
}

fn node(elab: &TermElabM, e: ExprId) -> Node {
    elab.mctx.store().expr_node(Some(elab.view.store), e)
}

fn app_fn(elab: &TermElabM, mut e: ExprId) -> ExprId {
    while let Node::App { f, .. } = node(elab, e) {
        e = f;
    }
    e
}

fn app_args(elab: &TermElabM, mut e: ExprId) -> Vec<ExprId> {
    let mut out = Vec::new();
    while let Node::App { f, arg } = node(elab, e) {
        out.push(arg);
        e = f;
    }
    out.reverse();
    out
}

fn render(elab: &TermElabM, n: NameId) -> String {
    elab.mctx.store().to_name(Some(elab.view.store), Some(n)).to_string()
}

fn mk_app(elab: &mut TermElabM, f: ExprId, a: ExprId) -> Result<ExprId, ElabError> {
    let base = elab.view.store;
    Ok(elab.mctx.store_mut().expr_app(Some(base), f, a).map_err(leanr_meta::MetaError::from)?)
}

/// oracle: `Expr.getOptParamDefault?` — `optParam α default`, arity 2.
fn opt_param_default(elab: &TermElabM, ty: ExprId) -> Option<ExprId> {
    let args = app_args(elab, ty);
    match node(elab, app_fn(elab, ty)) {
        Node::Const { name: Some(n), .. } if args.len() == 2 && render(elab, n) == "optParam" => {
            Some(args[1])
        }
        _ => None,
    }
}

/// oracle: `consumeImplicits` (`App.lean:1659-1676`) — `whnfCore`, then
/// fill leading implicit / (with args) strict-implicit / inst-implicit
/// binders and `optParam` defaults. `autoParam` is left alone, as in the
/// oracle ("TODO: we do not handle autoParams here").
fn consume_implicits(
    elab: &mut TermElabM,
    stx: &SynElem,
    mut e: ExprId,
    e_type: ExprId,
    has_args: bool,
) -> Result<(ExprId, ExprId), ElabError> {
    let mut e_type = elab.mctx.whnf_core(e_type)?;
    loop {
        let Node::Forall { binder_type: d, body: b, binder_info: bi, .. } = node(elab, e_type) else {
            return Ok((e, e_type));
        };
        let arg = match bi {
            BinderInfo::Implicit => Some(natural_hole(elab, d, stx)?),
            BinderInfo::StrictImplicit if has_args => Some(natural_hole(elab, d, stx)?),
            BinderInfo::InstImplicit => Some(elab.mk_inst_mvar(d, stx.clone())?),
            _ => opt_param_default(elab, d),
        };
        let Some(arg) = arg else { return Ok((e, e_type)) };
        e = mk_app(elab, e, arg)?;
        let next = elab.mctx.instantiate1(b, arg)?;
        e_type = elab.mctx.whnf_core(next)?;
    }
}

/// `mkFreshExprMVar d` + `registerMVarErrorHoleInfo` (`App.lean:1664-1665`).
fn natural_hole(elab: &mut TermElabM, d: ExprId, stx: &SynElem) -> Result<ExprId, ElabError> {
    let (m, id) = elab.mk_fresh_expr_mvar_of_kind(d, leanr_meta::MVarKind::Natural)?;
    elab.register_mvar_error_hole_info(id, stx.clone());
    Ok(m)
}
```

The oracle's inst-implicit arm also calls `registerMVarErrorImplicitArgInfo mvar stx r`. `elab.mk_inst_mvar` returns only the `ExprId`. Read the id back with `Node::MVar { id: Some(n) }` → `MVarId(n)` and call `elab.register_mvar_error_implicit_arg_info(id, stx.clone(), e_after_app)`, matching the oracle's `r := mkApp e mvar`.

```rust
/// oracle: `matchConstStructure` (`MonadEnv.lean:153-160`): a constant
/// naming an inductive with exactly one constructor. Returns its
/// `numFields`.
fn match_const_structure(elab: &TermElabM, s: NameId) -> Option<usize> {
    let leanr_kernel::ConstantInfo::Induct(ind) = elab.view.get(s)? else { return None };
    let [ctor] = ind.ctors.as_slice() else { return None };
    let leanr_kernel::ConstantInfo::Ctor(c) = elab.view.get(*ctor)? else { return None };
    c.num_fields.to_usize()
}

/// `Name.mkSimple` over a field token component.
fn simple_name(elab: &mut TermElabM, s: &str) -> Result<NameId, ElabError> {
    crate::app::head::intern_dotted(elab, s)
}

/// oracle: `resolveLValAux` (`App.lean:1517-1627`), P1's arms.
fn resolve_lval_aux(
    elab: &mut TermElabM,
    e: ExprId,
    e_type: ExprId,
    lval: &LVal,
) -> Result<LValResolution, ElabError> {
    let head = node(elab, app_fn(elab, e_type));
    let proj_err = |reason| ElabError::InvalidProjection { e, e_type, reason };
    match (head, lval) {
        (Node::Const { name: Some(s), .. }, LVal::FieldIdx { idx, levels, .. }) => {
            if *idx == 0 {
                return Err(proj_err(InvalidProjectionReason::IndexZero));
            }
            let Some(num_fields) = match_const_structure(elab, s) else {
                return Err(proj_err(InvalidProjectionReason::NotOneCtor));
            };
            if idx - 1 < num_fields {
                if elab.mctx.is_structure(s) {
                    let field = elab.mctx.get_structure_fields(s)[idx - 1];
                    Ok(LValResolution::ProjFn { base: s, struct_name: s, field, levels: levels.clone() })
                } else if !levels.is_empty() {
                    Err(proj_err(InvalidProjectionReason::ExplicitUnivsOnInductive))
                } else {
                    Ok(LValResolution::ProjIdx { struct_name: s, idx: idx - 1 })
                }
            } else if num_fields == 0 {
                Err(proj_err(InvalidProjectionReason::NoFields))
            } else {
                Err(proj_err(InvalidProjectionReason::IndexOutOfRange { idx: *idx, num_fields }))
            }
        }
        (Node::Const { name: Some(s), .. }, LVal::FieldName { name, levels, .. }) => {
            let field = simple_name(elab, name)?;
            if elab.mctx.is_structure(s) {
                if let Some(base) = elab.mctx.find_field(s, field) {
                    return Ok(LValResolution::ProjFn { base, struct_name: s, field, levels: levels.clone() });
                }
            }
            // `:1557-1568`: the local-context search for an aux decl
            // (`LValResolution.localRec`). leanr's local context never
            // holds an aux decl (no `let rec` / `where` producer), so
            // the oracle's loop finds nothing here too — nothing to port.
            Err(ElabError::UnsupportedSyntax(format!(
                "`.{name}` on `{}` needs generalized field notation \
                 (`findMethod?`, App.lean:1453-1478 / :1569-1570) — M4b-4a P3",
                render(elab, s)
            )))
        }
        (Node::Forall { .. }, LVal::FieldName { name, .. }) => {
            let full = format!("Function.{name}");
            let full_id = crate::app::head::intern_dotted(elab, &full)?;
            if elab.view.get(full_id).is_some() {
                return Err(ElabError::UnsupportedSyntax(format!(
                    "`.{name}` on a function resolves to `{full}` (App.lean:1580-1583) — M4b-4a P3"
                )));
            }
            Err(ElabError::InvalidField { e, e_type, field: name.clone(),
                reason: InvalidFieldReason::NotFound { full_name: full } })
        }
        (Node::Forall { .. }, LVal::FieldIdx { .. }) => Err(proj_err(InvalidProjectionReason::OnFunction)),
        (Node::MVar { .. }, LVal::FieldName { name, .. }) => Err(ElabError::InvalidField {
            e, e_type, field: name.clone(), reason: InvalidFieldReason::TypeUnknown }),
        (Node::MVar { .. }, LVal::FieldIdx { .. }) => Err(proj_err(InvalidProjectionReason::TypeUnknown)),
        (_, LVal::FieldName { name, .. }) => Err(ElabError::InvalidField {
            e, e_type, field: name.clone(), reason: InvalidFieldReason::NotConstApp }),
        (_, LVal::FieldIdx { .. }) => Err(proj_err(InvalidProjectionReason::NotConstApp)),
    }
}
```

The `(_, FieldName)` arm skips the oracle's `c ++ suffix` sub-arm (`:1606-1608`). That sub-arm needs `suffix?`, which only P4 produces. Leave a one-line comment saying so.

```rust
/// Which errors `resolveLValLoop`'s `catch` retries (`App.lean:1687-1694`:
/// `.error` retries, `.internal` rethrows). Named seams are NOT oracle
/// errors — retrying one would report an error for a path leanr never
/// ran (plan § Review Focus 2) — and `Meta` errors are leanr's
/// internal/budget failures.
fn is_retryable(e: &ElabError) -> bool {
    !matches!(e, ElabError::UnsupportedSyntax(_) | ElabError::Meta(_))
}

/// oracle: `resolveLValLoop` (`App.lean:1678-1694`).
fn resolve_lval_loop(
    elab: &mut TermElabM,
    lval: &LVal,
    e: ExprId,
    e_type: ExprId,
    has_args: bool,
    kinds: &KindInterner,
) -> Result<(ExprId, LValResolution), ElabError> {
    let (e, e_type) = consume_implicits(elab, lval.r#ref(), e, e_type, has_args)?;
    // `tryPostponeIfMVar eType` then `if isMVarApp eType then
    // synthesizeSyntheticMVarsUsingDefault` (`:1680-1684`). The first
    // throws only when `mayPostpone`, and leanr cannot postpone yet.
    if crate::elab::is_mvar_app(elab, e_type)? {
        if elab.may_postpone {
            return Err(ElabError::UnsupportedSyntax(
                "field notation on a term whose type is still a metavariable: the oracle \
                 postpones (`tryPostponeIfMVar`, App.lean:1680) — M4b-4a P2"
                    .to_string(),
            ));
        }
        elab.synthesize_synthetic_mvars_using_default(kinds)?;
    }
    let e_type = elab.mctx.instantiate_mvars(e_type)?;
    match resolve_lval_aux(elab, e, e_type, lval) {
        Ok(r) => Ok((e, r)),
        Err(err) if is_retryable(&err) => match elab.mctx.unfold_definition_pub(e_type)? {
            Some(t) => resolve_lval_loop(elab, lval, e, t, has_args, kinds),
            None => Err(err),
        },
        Err(err) => Err(err),
    }
}

/// oracle: `resolveLVal` (`App.lean:1696-1698`).
fn resolve_lval(
    elab: &mut TermElabM,
    e: ExprId,
    lval: &LVal,
    has_args: bool,
    kinds: &KindInterner,
) -> Result<(ExprId, LValResolution), ElabError> {
    let e_type = elab.mctx.infer_type(e)?;
    resolve_lval_loop(elab, lval, e, e_type, has_args, kinds)
}

/// oracle: `mkProjAndCheck` (`App.lean:65-73`).
fn mk_proj_and_check(elab: &mut TermElabM, s: NameId, idx: usize, e: ExprId) -> Result<ExprId, ElabError> {
    let base = elab.view.store;
    let r = elab.mctx.store_mut()
        .expr_proj(Some(base), Some(s), &Nat::from(idx as u64), e)
        .map_err(leanr_meta::MetaError::from)?;
    let e_type = elab.mctx.infer_type(e)?;
    if elab.mctx.is_prop(e_type)? {
        let r_type = elab.mctx.infer_type(r)?;
        if !elab.mctx.is_prop(r_type)? {
            return Err(ElabError::InvalidProjection { e, e_type,
                reason: InvalidProjectionReason::NonPropFromProp });
        }
    }
    Ok(r)
}
```

Replace `elab_app_lvals` with the oracle's loop (`App.lean:1845-1895`). `ProjFn` stays a Task 6 seam for now:

```rust
pub fn elab_app_lvals(
    elab: &mut TermElabM,
    mut f: ExprId,
    lvals: Vec<LVal>,
    call: AppCall,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    // `hasArgs` reads the OUTER application's arguments on every
    // iteration (`:1850`), not the ones a non-final step passes on.
    let has_args = !call.named_args.is_empty() || !call.args.is_empty();
    for lval in lvals {
        let (e, res) = resolve_lval(elab, f, &lval, has_args, kinds)?;
        f = match res {
            LValResolution::ProjIdx { struct_name, idx } => mk_proj_and_check(elab, struct_name, idx, e)?,
            LValResolution::ProjFn { .. } => {
                return Err(ElabError::UnsupportedSyntax(
                    "structure projection function — M4b-4a P1 task 6".to_string(),
                ))
            }
        };
    }
    crate::app::elab_app_args(elab, f, call, kinds)
}
```

This matches the oracle's control flow: `projIdx` does `loop f lvals`, and the empty list ends in `elabAppArgs f namedArgs args …`. Check `crate::elab::is_mvar_app`'s visibility (Step: `elab.rs:563`, `fn` → `pub(crate) fn`), and that `may_postpone` and `synthesize_synthetic_mvars_using_default` are reachable (`pub` on `TermElabM`, per `elab.rs:71` and `synthetic/ladder.rs:429`).

`is_mvar_app` is leanr's documented approximation of `isMVarApp` (instantiate plus a spine walk, no `whnfR`; see its doc at `elab.rs:545-562`). P2 owns making it exact. Say so in a comment at the call.

- [ ] **Step 5: Head arms** (`head.rs`)

Add `fn proj_parts(elem) -> Result<(SynElem, SynElem), ElabError>`, returning `(base, field)` from a `Lean.Parser.Term.proj` node's non-trivia children `[base, ".", field]`. The field is either a `fieldIdx` node (text is digits) or an `<ident>` token. Confirm the layout with one throwaway probe test printing `non_trivia_children` for `(Nat.zero).1` and `(s).toS2.toS1` (never committed; same precedent as `expand.rs`'s recorded shapes), and record it in the doc comment.

Then add these arms to `elab_app_fn`, before the `is_lval_head` arm:

```rust
// oracle: `` `($(e).$idx:fieldIdx) `` / `` `($(e).$field:ident) ``
// and their `.{us}` forms (`App.lean:2084-2097`). The explicit levels
// peeled off a `.{us}` wrapper belong to the FIELD (the last
// component), never to `e`.
("Lean.Parser.Term.proj", _) => {
    let (base, field) = proj_parts(elem)?;
    let mut new: Vec<LVal> = match kinds.name(field.kind()) {
        "fieldIdx" => {
            let text = field.to_string();
            let idx = text.trim().parse::<usize>().map_err(|_| {
                ElabError::IllFormedSyntax(format!("fieldIdx `{text}`"))
            })?;
            vec![LVal::FieldIdx { r#ref: field.clone(), idx, levels: explicit_levels.to_vec() }]
        }
        // `field.identComponents` (`:2071`): ONE token, one LVal per
        // component (plan § Review Focus 5).
        _ => {
            let text = field.to_string();
            let comps: Vec<&str> = text.trim().split('.').collect();
            let last = comps.len() - 1;
            comps.iter().enumerate().map(|(i, c)| LVal::FieldName {
                r#ref: field.clone(),
                name: c.to_string(),
                levels: if i == last { explicit_levels.to_vec() } else { Vec::new() },
            }).collect()
        }
    };
    new.extend(lvals);
    elab_app_fn(elab, &base, kinds, &[], new, call)
}
// oracle: `` `($id:ident.{$us,*}) `` reached by recursion (`:2103-2105`)
// — a `.{us}` on the proj's own base, e.g. `Poly.mk.{0} …`.
("Lean.Parser.Term.explicitUniv", _) => {
    let (inner, lvls) = crate::app::explicit_univ_parts(elem)?;
    let levels = elab_explicit_univs(elab, &lvls, kinds)?;
    elab_app_fn(elab, &inner, kinds, &levels, lvals, call)
}
// oracle: `` `(_) `` (`App.lean:2119`).
("Lean.Parser.Term.hole", _) => Err(ElabError::PlaceholderAsFunction),
```

Make `explicit_univ_parts` in `mod.rs` `pub(crate)`. Remove `"Lean.Parser.Term.proj"` from `is_lval_head`. Retarget that arm's message to name the remaining owners: `pipeProj`/`dotIdent`/`namedPattern` → `M4b-4a P4`, `choice` → `the overloading slice (resolve_global)`. Split it into two arms if one message cannot name both honestly.

Replace the generic catch-all arm with the oracle's (`App.lean:2120-2138`):

```rust
// oracle: `elabAppFn`'s generic arm. With nothing to apply, the term
// is elaborated against the expected type and returned AS IS — not
// re-applied through `elabAppArgs`. Otherwise it is elaborated with
// no expected type and handed to `elabAppLVals`.
_ => {
    if lvals.is_empty() && call.named_args.is_empty() && call.args.is_empty() {
        Ok(vec![elab.elab_term(elem, kinds, call.expected)?])
    } else {
        let f = elab.elab_term(elem, kinds, None)?;
        Ok(vec![crate::app::lval::elab_app_lvals(elab, f, lvals, call, kinds)?])
    }
}
```

The `catchPostpone` argument (`:2121-2129`) is P2's, since leanr cannot postpone yet. Note it in a comment.

- [ ] **Step 6: Route `proj`** (`dispatch.rs`)

Add `"Lean.Parser.Term.proj" => Some("proj"),` to `elaborator_name_for`, and add this `dispatch` arm next to `explicitUniv`:

```rust
// oracle: `@[builtin_term_elab proj] elabProj := elabAtom`
// (`App.lean:2274`) — a zero-argument application whose head carries
// the LVal; `app::head::elab_app_fn`'s proj arm peels it.
("Lean.Parser.Term.proj", NodeOrToken::Node(_)) => {
    crate::app::elab_atom(elab, elem, kinds, expected)
}
```

- [ ] **Step 7: Reconcile `seam_audit.rs`**

- In `deferred_constructs_are_named_seams`, remove `("(Nat.zero).1 Nat.zero", "M4b-4")`, `("(Nat.succ) Nat.zero", "M4b-4")`, `("(fun (x : Nat) => x) Nat.zero", "M4b-4")` and `("(Nat.succ : Nat -> Nat) Nat.zero Nat.zero", "M4b-4")`.
- Keep `".succ Nat.zero"` and retarget its marker to `"M4b-4a P4"`.
- Add `over_application_through_a_general_head_reports_function_expected`, asserting that `(Nat.succ : Nat -> Nat) Nat.zero Nat.zero` is now `Err(ElabError::FunctionExpected { .. })`. That's the oracle's answer too; run it on the oracle and quote the message.
- In `unregistered_kinds_are_named_by_kind`, remove the `("Nat.zero.1", "Lean.Parser.Term.proj")` case (it now elaborates to `InvalidProjection NotOneCtor`, pinned in `lval_smoke.rs`).

- [ ] **Step 8: Run everything**

Run: `cargo test -p leanr_elab 2>&1 | tail -5`
Expected: `lval_smoke` passes (4 tests), `oracle_elab_gate` passes including the four `lval/*` records, and `seam_audit` passes.

- [ ] **Step 9: Mutation checks** (run each, confirm red, revert, record)

- `is_retryable` → `true` for everything: `p2_p3_p4_constructs_are_named_seams` fails on `S3Alias` (Review Focus 2).
- In `mk_proj_and_check`, delete the `is_prop` block: `NonPropFromProp` fails.
- In the generic arm, drop the `lvals.is_empty() && …` short-circuit, so a bare paren term always goes through `elab_app_lvals`/`elab_app_args`. Record whether any corpus record catches it. If none does, add `("lval/generic-bare-paren", "(fun (x : Nat) => x)")` to `lvalIdxQueries`, regenerate, and re-run the mutation until one does.
- In `resolve_lval_aux`, swap `IndexOutOfRange`'s `idx`/`num_fields`: `projection_rejections_match_the_oracle` fails.

- [ ] **Step 10: Commit**

```bash
git add crates/leanr_elab tests/fixtures/elab/dump_elab.lean tests/fixtures/elab/elab-queries.jsonl
git commit -m "elab: index projections, the LVal resolution loop, and general application heads"
```

---

### Task 6: Structure projection functions

**Files:**
- Modify: `crates/leanr_elab/src/app/lval.rs` (`mk_base_projections`, the `ProjFn` arm)
- Modify: `crates/leanr_elab/src/app/args.rs:365-376` (the `numImplicitParams` arm)
- Modify: `crates/leanr_elab/tests/lval_smoke.rs`
- Modify: `tests/fixtures/elab/dump_elab.lean` (+ `lvalFnQueries`), regenerate `elab-queries.jsonl`

**Interfaces:**
- Consumes: `LValResolution::ProjFn`, `MetaCtx::{get_path_to_base_structure, get_field_info}`, `head::mk_const`, `elab_app_args`, `expand::NamedArg`.
- Produces: the finished `elab_app_lvals` for P1.

- [ ] **Step 1: Write the failing corpus records and tests**

Add after `lvalIdxQueries`, and add `++ lvalFnQueries` to `main`:

```lean
/-- M4b-4a P1 task 6: `projFn` (`App.lean:1857-1872`) — structure
fields by index and by name, inherited through subobjects
(`mkBaseProjections`), chained, with explicit universes, after
`consumeImplicits`, and through `resolveLValLoop`'s unfold retry. -/
def lvalFnQueries : List (String × String) :=
  [ ("lval/prod-fst-idx",        "fun (p : Prod Nat Nat) => p.1")
  , ("lval/prod-snd-idx",        "fun (p : Prod Nat Nat) => p.2")
  , ("lval/prod-fst-name",       "fun (p : Prod Nat Nat) => (p).fst")
  , ("lval/prod-mk-idx",         "(Prod.mk Nat.zero Nat.zero).1")
  , ("lval/subobject-idx",       "fun (s : S3) => s.1")
  , ("lval/inherited-field",     "fun (s : S3) => (s).a")
  , ("lval/idx-then-name",       "fun (s : S3) => (s).1.b")
  , ("lval/chain-idx",           "fun (s : S3) => s.1.1.1")
  , ("lval/dotted-field-token",  "fun (s : S3) => (s).toS2.toS1")
  , ("lval/diamond-direct",      "fun (d : D3) => (d).z")
  , ("lval/diamond-subobject",   "fun (d : D3) => (d).x")
  , ("lval/unfold-alias",        "fun (s : S3Alias) => (s).a")
  , ("lval/poly-idx",            "fun (q : Poly Nat) => q.1")
  , ("lval/poly-univ",           "fun (q : Poly Nat) => (q).val.{0}")
  , ("lval/field-univ-partial",  "fun (p : Prod Nat Nat) => (p).fst.{0}")
  , ("lval/consume-implicits",   "(@dflt).1")
  ]
```

Expected oracle terms (from the `#check` probes run while writing this plan; the regenerated records must agree):
- `p.1` → `@Prod.fst.{0,0} Nat Nat p`
- `(s).a` → `S1.a (S2.toS1 (S3.toS2 s))`
- `(s).1.b` → `S2.b (S3.toS2 s)`
- `(d).z` → `D3.z d`
- `(d).x` → `D1.x (D3.toD1 d)`
- `(@dflt).1` → `@Prod.fst.{0,0} Nat Nat (@dflt ?m)`

Append to `lval_smoke.rs`:

```rust
#[test]
fn projection_function_rejections_match_the_oracle() {
    // "too many explicit universe levels for `Poly.val`"
    assert!(matches!(
        support::elab_and_synthesize("fun (q : Poly Nat) => (q).val.{0, 0}"),
        Err(ElabError::TooManyUniverseLevels(_))
    ));
    // Review Focus 3 — "Argument `self` was already set" (addNamedArg,
    // Arg.lean:55-59, called at App.lean:1869).
    match support::elab_and_synthesize("fun (s : S3) => (s).a (self := s)") {
        Err(ElabError::DuplicateNamedArg(n)) => assert_eq!(n, "self"),
        other => panic!("expected DuplicateNamedArg(self), got {other:?}"),
    }
}

#[test]
fn recursor_head_with_a_projection_is_not_an_eliminator() {
    // Review Focus 1: `Nat.rec.1` resolves the LVal on `Nat.rec`'s
    // type — consumeImplicits fills `motive`, the next binder is
    // explicit, so `.forallE` + fieldIdx = OnFunction. It must NOT hit
    // the `elabAsElim` recursor seam.
    assert_eq!(proj_reason("Nat.rec.1"), InvalidProjectionReason::OnFunction);
}
```

**Before trusting `Nat.rec.1`, run it on the oracle** (scratch file as in Task 5, `#check Nat.rec.1`). If the oracle says anything other than the projections-on-functions error, replace the assertion with what it does say and explain it in the comment. Record the oracle output in the task report.

- [ ] **Step 2: Run and watch them fail**

Run: `mise run fixtures:regen-elab && cargo test -p leanr_elab --test oracle_elab --test lval_smoke`
Expected: the `lval/*` records fail with the `M4b-4a P1 task 6` seam, and so do the two new smoke tests.

- [ ] **Step 3: `mk_base_projections` and the `ProjFn` arm** (`lval.rs`)

```rust
/// oracle: `mkBaseProjections` (`App.lean:1700-1710`): walk
/// `getPathToBaseStructure?`, applying each parent projection to the
/// structure's own type parameters — with the universe levels of the
/// TYPE's head constant, reused as is.
fn mk_base_projections(
    elab: &mut TermElabM,
    base_struct: NameId,
    struct_name: NameId,
    mut e: ExprId,
) -> Result<ExprId, ElabError> {
    let Some(path) = elab.mctx.get_path_to_base_structure(base_struct, struct_name) else {
        return Err(ElabError::Internal(
            "Failed to access field in parent structure (App.lean:1704)".to_string(),
        ));
    };
    let store = elab.view.store;
    for proj_fn in path {
        let ty = elab.mctx.infer_type(e)?;
        let ty = elab.mctx.whnf(ty)?;
        let Node::Const { levels, .. } = node(elab, app_fn(elab, ty)) else {
            return Err(ElabError::Internal(
                "Type of structure value cannot be reduced to a constant application (App.lean:1708)"
                    .to_string(),
            ));
        };
        let params = app_args(elab, ty);
        let mut f = elab.mctx.store_mut()
            .expr_const(Some(store), Some(proj_fn), levels)
            .map_err(leanr_meta::MetaError::from)?;
        for p in params {
            f = mk_app(elab, f, p)?;
        }
        e = mk_app(elab, f, e)?;
    }
    Ok(e)
}
```

In `elab_app_lvals`, the loop must know whether an LVal is the last one (`:1864`: `if lvals.isEmpty`). Rewrite it to iterate with `let n = lvals.len(); for (i, lval) in lvals.into_iter().enumerate() { let last = i + 1 == n; … }`. Because the final `ProjFn` step consumes `call`, restructure so `call` is moved only in the `last` branch (e.g. keep `let mut call = Some(call);` and `call.take()` there; the loop's tail `elab_app_args` runs only when no `ProjFn` consumed it). The arm:

```rust
LValResolution::ProjFn { base, struct_name, field, levels } => {
    let e = mk_base_projections(elab, base, struct_name, e)?;
    let Some(info) = elab.mctx.get_field_info(base, field).cloned() else {
        return Err(ElabError::Internal("getFieldInfo? after findField? (App.lean:1859)".into()));
    };
    // `isInaccessiblePrivateName` (`:1860-1861`). leanr does not model
    // private-name accessibility; a private projection is a seam, not a
    // guess (design spec § Errors).
    let proj_name = render(elab, info.proj_fn);
    if proj_name.starts_with("_private.") {
        return Err(ElabError::UnsupportedSyntax(format!(
            "private field `{proj_name}` — accessibility needs the slice that models private names"
        )));
    }
    let proj_fn = crate::app::head::mk_const(elab, info.proj_fn, &levels, &proj_name)?;
    let num_params = match elab.view.get(base) {
        Some(leanr_kernel::ConstantInfo::Induct(ind)) => ind.num_params.to_usize().unwrap_or(0),
        _ => return Err(ElabError::Internal("getConstInfoInduct base (App.lean:1864)".into())),
    };
    let self_arg = NamedArg { name: "self".to_string(), val: Arg::Expr(e), num_implicit_params: num_params };
    if last {
        let mut call = call.take().expect("final step consumes the call once");
        // `addNamedArg` (`Arg.lean:55-59`): a user-supplied `(self := …)`
        // is a duplicate (plan § Review Focus 3).
        if call.named_args.iter().any(|n| n.name == "self") {
            return Err(ElabError::DuplicateNamedArg("self".to_string()));
        }
        call.named_args.push(self_arg);
        return crate::app::elab_app_args(elab, proj_fn, call, kinds);
    }
    // Non-final (`:1871-1872`): apply `self` alone, no expected type,
    // `explicit := false`, `ellipsis := false`.
    let stx = call.as_ref().expect("call still owned").stx.clone();
    f = crate::app::elab_app_args(elab, proj_fn, AppCall {
        named_args: vec![self_arg], args: Vec::new(), expected: None,
        explicit: false, ellipsis: false, stx,
    }, kinds)?;
}
```

Add `use crate::app::expand::{Arg, NamedArg};`. Check that `NamedArg`'s name comparison in `args.rs` (`find_named_arg`) matches a binder named `self` by its rendered string. `Prod.fst`'s binder is `self`; the `lval/prod-fst-idx` record is the check.

- [ ] **Step 4: The `numImplicitParams` arm** (`args.rs:370-376`)

Replace the seam with the oracle's (`App.lean:767-802`):

```rust
if app.param_idx() < app.ctx.num_implicit_params {
    // oracle: `processExplicitArg`'s first branch (`App.lean:767-802`)
    // — the structure's own parameters are implicit when projecting
    // via `(self := s)`, so `s.val` is `@C.val params s`, not
    // `fun params => …` (issue #1851 in the oracle's own comment).
    add_implicit_arg(app)?;
    return Ok(true);
}
```

Check `add_implicit_arg`'s signature (`args.rs:657`: `fn add_implicit_arg(app: &mut AppElab) -> Result<(), ElabError>`) and what `process_explicit_arg`'s other arms return after adding an argument (`Ok(true)` means "continue the main loop"). Match that. `propagate.rs:227` already simulates this branch.

- [ ] **Step 5: Run everything**

Run: `mise run fixtures:regen-elab && cargo test -p leanr_elab 2>&1 | tail -5`
Expected: every `lval/*` record passes, and `lval_smoke` passes (6 tests).

- [ ] **Step 6: Mutation checks** (run each, confirm red, revert, record)

- Set `num_implicit_params: 0` on `self_arg`: `lval/prod-fst-idx` fails (leanr eta-expands instead).
- In `mk_base_projections`, reverse `path`: `lval/inherited-field` fails.
- In the head proj arm, skip the `split('.')` (one LVal for the whole token): `lval/dotted-field-token` fails.
- In `elab_app_fn`'s ident arm, drop `&& lvals.is_empty()` from `heed`: `recursor_head_with_a_projection_is_not_an_eliminator` fails.
- Drop the duplicate-`self` check: `projection_function_rejections_match_the_oracle` fails. Otherwise `elab_app_args`'s own duplicate handling catches it first; if so, delete the redundant check here and say so in the report.
- Give levels to every component (not only the last): `lval/poly-univ` or `lval/field-univ-partial` fails.

- [ ] **Step 7: Commit**

```bash
git add crates/leanr_elab tests/fixtures/elab/dump_elab.lean tests/fixtures/elab/elab-queries.jsonl
git commit -m "elab: structure projection functions (projFn, mkBaseProjections, numImplicitParams)"
```

---

### Task 7: `@` on projection heads, seam reconciliation, and the landed record

**Files:**
- Modify: `crates/leanr_elab/src/app/mod.rs` (`elab_explicit` and `peel_head` proj arms; module-doc seam table)
- Modify: `crates/leanr_elab/src/dispatch.rs` (deferral table doc)
- Modify: `crates/leanr_elab/src/lib.rs` (deferral list)
- Modify: `crates/leanr_elab/src/elab.rs:369-377` (retarget the `.postpone` seam to `M4b-4a P2`)
- Modify: `crates/leanr_elab/tests/seam_audit.rs` (`@(Nat.zero).1` case; `implicit_lambda_postpone_is_a_named_seam` marker; `no_seam_message_names_a_completed_slice` needle)
- Modify: `tests/fixtures/elab/dump_elab.lean` (+ one record)
- Modify: `docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md` (new `## Landed` section, P1 entry)

**Interfaces:**
- Consumes: everything above.
- Produces: no stale `M4b-4` seam message left that P1 closed; every remaining one names its precise owner.

- [ ] **Step 1: Write the failing record and test**

Add `("lval/explicit-proj", "@(Prod.mk Nat.zero Nat.zero).1")` to `lvalFnQueries`. The oracle gives `@Prod.fst.{0,0} Nat Nat (@Prod.mk.{0,0} Nat Nat Nat.zero Nat.zero)`. Regenerate. In `seam_audit.rs`'s `deferred_constructs_are_named_seams`, replace `("@(Nat.zero).1", "M4b-4")` with `("@.succ", "M4b-4a P4")` (`@` on a `dotIdent`, still P4). In `implicit_lambda_postpone_is_a_named_seam`, change the marker from `"M4b-4"` to `"M4b-4a P2"`.

Run: `cargo test -p leanr_elab --test oracle_elab --test seam_audit`
Expected: `lval/explicit-proj` fails with the `@`-on-projection seam. The two retargeted seam assertions fail because the messages still say `M4b-4`.

- [ ] **Step 2: Route `@` on projections**

In `elab_explicit`, split the `"Lean.Parser.Term.proj" | "Lean.Parser.Term.dotIdent"` arm:
- `proj` joins the `<ident>` / `explicitUniv` arm (→ `elab_atom`), per the oracle's `` `(@$(_).$_:fieldIdx) `` / `` `(@$(_).$_:ident) `` rows (`App.lean:2262-2266`).
- `dotIdent` keeps a seam naming `M4b-4a P4`.

In `peel_head`, same split: `proj` is accepted alongside `<ident>` / `explicitUniv` (`App.lean:2110-2117`), and `dotIdent` seams with `M4b-4a P4`. Update both functions' doc comments. The "`.field` forms are the LVal machinery (M4b-4)" sentence is now wrong.

Retarget `elab.rs:369-377`'s message to `M4b-4a P2`, and the recursor seam in `head.rs` (`elab_ident_head`) from `M4b-4` to `M4b-4c` (the `elabAsElim` spec).

- [ ] **Step 3: Sweep every remaining `M4b-4` mention**

Run: `grep -rn "M4b-4" crates/leanr_elab/src crates/leanr_elab/tests`

For each hit, do one of the following:
- **Delete it:** the seam is closed by P1 (proj, generic head, `numImplicitParams`, `@`-proj).
- **Retarget it:**
  - `pipeProj` / `dotIdent` / `namedPattern` → `M4b-4a P4`
  - postponement → `M4b-4a P2`
  - `.const` / `Function` → `M4b-4a P3`
  - `elabAsElim` → `M4b-4c`
  - `⟨⟩` → `M4b-4b`
  - `binop%` → `the macro-expansion slice`
  - match / `inPattern` / `withLocalInstances` → `the match slice`
  - `choice` → `the overloading slice`
- **Keep it:** it is historical prose inside a doc comment. Leave it, but make sure it does not claim anything is still open that P1 closed.

Update these tables to match:
- `app/mod.rs`'s module-doc seam table: "dot notation, LVal machinery" → `P1 SHIPPED (proj, fieldIdx, projFn/projIdx) — lval.rs`, plus rows for what P2–P4 still own; "numImplicitParams" → shipped.
- `dispatch.rs`'s deferral block (`Term.proj` out, a ninth "Reconciled" sentence in the house style).
- `lib.rs`'s deferral list.

Add `"M4b-4a P1"` to `no_seam_message_names_a_completed_slice`'s `needles` and to its assertion text. Then **measure it non-vacuous** (the test's own doc demands this): temporarily add a live line `let _ = "M4b-4a P1";` to `lval.rs`, confirm the test fails, remove it, and record both runs.

- [ ] **Step 4: Run the full gate**

Run: `mise run ci`, blocking, to completion. Do not background it.
Expected: fmt, clippy and the full suite green, including `oracle_elab_gate` with every `lval/*` record.

- [ ] **Step 5: The landed record**

Append a `## Landed` section to the spec, in the style of `2026-09-29-nondep-local-decls-design.md` § Landed:

```markdown
## Landed

### P1 — structures and projections (PR #<n>)

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
- Corpus: <N> records under `lval/`. Rejections: `tests/lval_smoke.rs`.
- Seams left, each naming its owner: postponement (P2), `.const` /
  `Function` (P3), `pipeProj` / `dotIdent` / `namedPattern` (P4),
  `choice` (overloading slice), private projections (private-names
  slice), `LocalRec` (`let rec` slice).
- Known approximation carried forward: `is_mvar_app` has no `whnfR`
  (P2 owns making it exact).
```

Fill `<N>` from `grep -c '"id":"lval/' tests/fixtures/elab/elab-queries.jsonl`. Leave `#<n>` for the PR step.

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_elab tests/fixtures/elab docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md
git commit -m "elab: @ on projection heads; reconcile M4b-4 seams to their owners; P1 landed record"
```
