# M4a Reduction, Inference & Oracle Harness (plan 2 of 4) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `whnf` and `infer_type` in `leanr_meta`, verified against the oracle by a committed, hermetic tier-1 corpus behind `mise run meta:fast` — plus the `Lean.Meta.Match.Extension.extension` (matcher) decode in `leanr_olean` and the `Config` fields the reduction rules consult.

**Architecture:** All traversal is `ExprId`-native over the term bank (the `tc.rs` idiom; spec § Scope decisions — plan 1's deferred question, now answered). A `MetaCtx` struct holds all shared state; each module contributes an `impl MetaCtx` block. `leanr_kernel` is not modified. Reduction and inference are transcribed from the pinned Lean source, rule by rule, with a citation per rule.

**Tech Stack:** Rust 2021, `leanr_kernel` (term bank, `EnvView`, `replay`, `subst::*`), `leanr_olean` (extension decode), `stacker` (already pinned). One **dev-dependency** addition to `leanr_meta`: `serde_json` (already in the workspace's dependency tree — verify with `grep -rn serde_json crates/*/Cargo.toml` and mirror the existing version pin; justification: parsing committed oracle fixtures in tests only, never shipped code).

**Spec:** [docs/superpowers/specs/2026-07-20-m4a-reduction-inference-harness-design.md](../specs/2026-07-20-m4a-reduction-inference-harness-design.md)

## Global Constraints

- **Oracle pin:** `leanprover/lean4:v4.33.0-rc1`, Mathlib `c732b96d05efdb1fb84511dfdc24a8f70005ae99`. Never bump outside a milestone boundary.
- **Oracle source is local:** `$(lean --print-prefix)/src/lean/Lean/...` is the pinned toolchain's source. **Lean's source is the specification.** Where this plan's transcription and Lean's source disagree, Lean's source wins — fix the transcription and record the correction in the commit message. Never transcribe from memory; open the cited file.
- **Kernel TCB:** `leanr_kernel` must not be modified by this plan (verify with `git status --short crates/leanr_kernel` before every commit).
- **Untrusted input:** `.olean` bytes are untrusted. Every new decode path returns `OleanError`, never panics (`docs/THREAT_MODEL.md`).
- **Workflows:** named mise tasks; CI runs `mise run ci`.
- **Failure semantics:** every `leanr_meta` failure is incompleteness, never unsoundness.
- **Signature reconciliation rule (from plan 1, it worked):** if the compiler reports a mismatch between this plan's code and the real kernel/olean API, read the real signature (`crates/leanr_kernel/src/bank/`, `crates/leanr_kernel/src/lib.rs:35-71`) and adjust **this plan's code**, never the kernel.
- **Named seams:** several oracle behaviors are deliberately stubbed this plan (see "What this plan does NOT build"). Every seam must be a named function with a doc comment citing the oracle line it will implement and the plan that implements it. No silent divergence.

## Prerequisites (verify, do not redo)

Plan 1 is merged: `leanr_meta` exists with `MetaError`, `TransparencyMode`/`can_unfold`, `Config` (11 fields) + `cache_key`, `MetavarContext`; `leanr_olean` decodes `reducibilityCore`/`reducibilityExtra`.

```bash
cat lean-toolchain && cargo test -p leanr_meta 2>&1 | tail -1 && cargo test -p leanr_olean --lib reducibility 2>&1 | tail -1
```

Expected: `leanprover/lean4:v4.33.0-rc1`, then two green test summaries.

---

### Task 1: Decode the matcher environment extension

**Files:**
- Create: `tests/fixtures/Matcher.lean`
- Modify: `mise.toml` (`fixtures:regen`, after the `Reducibility` line)
- Modify: `crates/leanr_olean/src/module_data.rs` (types + `ModuleData` field + `parse_parts` merge + tests)
- Modify: `crates/leanr_olean/src/interp_id.rs` (decoder + `module_data` loop arm)
- Modify: `crates/leanr_olean/src/lib.rs` (re-exports)

**Interfaces:**
- Consumes: `leanr_olean`'s `ctor`/`array`/`bad` helpers, `name_req`, the existing `Nat`/`Option`/`Bool` raw-decode helpers (find them next to `constant_info` in `interp_id.rs` — `RecursorVal`'s decode already reads `Nat` and `Bool` fields; reuse those exact helpers).
- Produces:
  - `leanr_olean::MatcherAltInfo { num_fields: Nat, num_overlaps: Nat, has_unit_thunk: bool }`
  - `leanr_olean::MatcherEntry { name: NameId, num_params: Nat, num_discrs: Nat, alt_infos: Vec<MatcherAltInfo>, u_elim_pos: Option<Nat>, discr_infos: Vec<Option<NameId>> }`
  - `ModuleData::matchers: Vec<MatcherEntry>`

**Background (verified against `v4.33.0-rc1`, `src/Lean/Meta/Match/MatcherInfo.lean`):**

The extension is declared `builtin_initialize extension : SimplePersistentEnvExtension Entry State ← registerSimplePersistentEnvExtension {..}` inside `namespace Lean.Meta.Match.Extension` (MatcherInfo.lean:125-135), so its serialized extension name is expected to be **`Lean.Meta.Match.Extension.extension`** — the probe step pins the exact string; do not hardcode it before the probe confirms it.

Entry (MatcherInfo.lean:113-115): `{ name : Name, info : MatcherInfo }` — a 2-field ctor, **no** `ScopedEnvExtension.Entry` wrapper (this is a `SimplePersistentEnvExtension`, like `reducibilityCore`).

`MatcherInfo` (MatcherInfo.lean:52-68), 5 fields in declaration order:

| field | type |
|---|---|
| `numParams` | `Nat` |
| `numDiscrs` | `Nat` |
| `altInfos` | `Array AltParamInfo` — `{ numFields : Nat, numOverlaps : Nat, hasUnitThunk : Bool }` (MatcherInfo.lean:38-45) |
| `uElimPos?` | `Option Nat` |
| `discrInfos` | `Array DiscrInfo` — `{ hName? : Option Name }` (MatcherInfo.lean:15-17) |

Note v4.33 has `altInfos : Array AltParamInfo`, **not** the older `altNumParams : Array Nat` (that is now a derived function, MatcherInfo.lean:106). The consumer-side arity per alternative is `numFields + numOverlaps + (hasUnitThunk ? 1 : 0) + numDiscrEqs` — Task 6 computes it; the decode stores the raw fields.

- [ ] **Step 1: Create the fixture**

Create `tests/fixtures/Matcher.lean`:

```lean
-- Fixture for the `Lean.Meta.Match.Extension.extension` decode (M4a
-- plan 2, task 1). `prelude`-mode and import-free (the Prelude0
-- pattern) so the committed .olean is hermetic. Each `match` below
-- makes the elaborator register one MatcherInfo entry in this module's
-- extension array; `plainId` uses no match and must contribute none.
prelude

inductive N where
  | zero : N
  | succ : N → N

-- One matcher, one discriminant, two alternatives.
def isZero (n : N) : N :=
  match n with
  | .zero => .succ .zero
  | .succ _ => .zero

-- Two discriminants (a distinct matcher shape: numDiscrs = 2).
def both (a b : N) : N :=
  match a, b with
  | .zero, .zero => .zero
  | _, _ => .succ .zero

def plainId (n : N) : N := n
```

- [ ] **Step 2: Verify the fixture compiles against the oracle**

Run: `cd tests/fixtures && lean Matcher.lean -o Matcher.olean && echo OK && cd ../..`

Expected: `OK`. If the elaborator rejects something in prelude mode, simplify the failing definition (keeping at least one `match`) and record what was dropped in the fixture's comment — do not add imports.

- [ ] **Step 3: Wire the fixture into regen**

In `mise.toml`, add to the `fixtures:regen` `run` array immediately after the `Reducibility` line:

```toml
  # M4a plan 2: matcher fixture for the Lean.Meta.Match.Extension
  # decode. prelude-mode/import-free (Prelude0 pattern) so the meta
  # gate stays hermetic. cd-first for the same module-name reason as
  # ModPriv.
  "sh -c 'cd tests/fixtures && lean Matcher.lean -o Matcher.olean'",
```

Run: `mise run fixtures:regen` — expect clean, with `tests/fixtures/Matcher.olean` new in `git status --short`.

- [ ] **Step 4: Empirically pin the raw shape**

Same playbook as plan 1's reducibility probe. In `crates/leanr_olean/src/interp_id.rs`, inside `module_data`, immediately after `let ext_name = self.name(&pf[0])?;` add:

```rust
        // TEMPORARY probe — remove before committing.
        {
            let n = self.st.to_name(None, ext_name).to_string();
            if n.contains("Match") {
                eprintln!("PROBE ext name: {n}");
                for e in array(&pf[1])? {
                    eprintln!("PROBE entry: {e:?}");
                }
            }
        }
```

And a temporary test in `module_data.rs`'s `mod tests`:

```rust
    #[test]
    fn probe_matcher_shape() {
        let bytes = fixture("Matcher.olean");
        let mut env = Environment::default();
        let _ = ModuleData::parse(&bytes, env.store_mut()).expect("decode");
    }
```

Run: `cargo test -p leanr_olean --lib probe_matcher_shape -- --nocapture 2>&1 | grep PROBE | head -30`

Expected: the exact extension name (record it — the decode arm matches on this string), and per entry a `Ctor { tag: 0, fields: 2 }` whose second field is a 5-field `MatcherInfo` ctor. Record where each `Nat` lands (scalar vs boxed — `Nat` fields in a monomorphic struct position are typically unboxed into `scalars`, unlike plan 1's polymorphic `Prod` case) and how `Option Nat` / `Array` / `Bool` arrive. **Write the observed shape into the decoder's doc comment in step 7.** If the array is empty, the elaborator did not register matchers for this shape — extend the fixture (e.g. a three-alternative match) until entries appear.

- [ ] **Step 5: Remove the probe**

Delete both temporary blocks. `cargo test -p leanr_olean --lib` still builds.

- [ ] **Step 6: Write the failing test**

Add to `module_data.rs` `mod tests`:

```rust
    /// The matcher extension decodes: every `match` in Matcher.lean
    /// registered one entry; `plainId` (no match) contributed none.
    #[test]
    fn matcher_entries_decode() {
        let bytes = fixture("Matcher.olean");
        let mut env = Environment::default();
        let md = ModuleData::parse(&bytes, env.store_mut()).expect("decode");

        assert!(
            md.matchers.len() >= 2,
            "isZero and both must each register a matcher: {:?}",
            md.matchers.len()
        );

        let render = |n| env.store().to_name(None, Some(n)).to_string();
        // Matcher aux names are `<decl>.match_<i>`-shaped.
        assert!(
            md.matchers.iter().any(|m| render(m.name).contains("match_")),
            "expected match_ aux names"
        );
        for m in &md.matchers {
            // Every matcher in this fixture has 2 alternatives, and
            // discrInfos has one entry per discriminant.
            assert_eq!(m.alt_infos.len(), 2, "unexpected alt count: {:?}", render(m.name));
            assert_eq!(
                leanr_kernel::Nat::from(m.discr_infos.len() as u64),
                m.num_discrs,
                "discrInfos length must equal numDiscrs: {:?}",
                render(m.name)
            );
        }
        // `isZero` has 1 discriminant, `both` has 2.
        assert!(md.matchers.iter().any(|m| m.num_discrs == leanr_kernel::Nat::from(1u64)));
        assert!(md.matchers.iter().any(|m| m.num_discrs == leanr_kernel::Nat::from(2u64)));
    }
```

(If `Nat` comparison helpers differ, reconcile per the Global Constraints rule — `leanr_kernel::Nat` implements `PartialEq`/`From<u64>`; see `decl.rs` usage.)

- [ ] **Step 7: Run to verify failure, then add types and decoder**

Run: `cargo test -p leanr_olean --lib matcher` — expect compile failure (`no field 'matchers'`).

In `module_data.rs`, above `pub struct ModuleData`:

```rust
/// oracle: `Lean.Meta.Match.AltParamInfo` (MatcherInfo.lean:38-45).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MatcherAltInfo {
    pub num_fields: Nat,
    pub num_overlaps: Nat,
    pub has_unit_thunk: bool,
}

/// One decoded matcher-extension entry: oracle
/// `Lean.Meta.Match.Extension.Entry` = `{ name, info : MatcherInfo }`
/// (MatcherInfo.lean:113-115, 52-68). v4.33 stores `altInfos`
/// (per-alternative field/overlap/thunk counts), NOT the older
/// `altNumParams`; the consumer derives per-alt arity
/// (`MatcherInfo.altNumParams`, MatcherInfo.lean:106-108).
#[derive(Debug, Clone)]
pub struct MatcherEntry {
    pub name: NameId,
    pub num_params: Nat,
    pub num_discrs: Nat,
    pub alt_infos: Vec<MatcherAltInfo>,
    /// `uElimPos?` — `some pos` when the matcher eliminates into
    /// polymorphic universes.
    pub u_elim_pos: Option<Nat>,
    /// `discrInfos[i].hName?` — the `h :` annotation name per
    /// discriminant, flattened (DiscrInfo has exactly one field).
    pub discr_infos: Vec<Option<NameId>>,
}
```

Add to `ModuleData` after `reducibility`:

```rust
    /// Typed decode of the `Lean.Meta.Match.Extension.extension`
    /// entries (M4a plan 2). All other extension entries stay opaque.
    pub matchers: Vec<MatcherEntry>,
```

and mirror the `reducibility` line in `parse_parts`'s merge: `matchers: std::mem::take(&mut base.matchers),`.

In `interp_id.rs`, next to `reducibility_pair`, add (adapting scalar-vs-boxed reads to the step-4 probe — this is the part the probe exists for):

```rust
    /// oracle: `Lean.Meta.Match.Extension.Entry` — 2-field ctor
    /// `{ name, info : MatcherInfo }`; `MatcherInfo` is a 5-field ctor
    /// (numParams, numDiscrs, altInfos, uElimPos?, discrInfos).
    /// Shape pinned empirically against Matcher.olean:
    /// <RECORD THE PROBE OUTPUT HERE — scalar/boxed placement per field.>
    fn matcher_entry(&mut self, r: &Raw) -> Result<crate::MatcherEntry, OleanError> {
        let (f, _) = ctor(r, 0, 2, "Match.Extension.Entry")?;
        let name = self.name_req(&f[0])?;
        let (mf, ms) = ctor(&f[1], 0, 5, "MatcherInfo")?;
        // Field reads below use the same Nat/Bool/Option helpers
        // RecursorVal's decode uses; reconcile names against the probe.
        let num_params = self.nat(&mf[0], ms, 0, "MatcherInfo.numParams")?;
        let num_discrs = self.nat(&mf[1], ms, 1, "MatcherInfo.numDiscrs")?;
        let mut alt_infos = Vec::new();
        for a in array(&mf[2])? {
            let (af, as_) = ctor(a, 0, 3, "AltParamInfo")?;
            alt_infos.push(crate::MatcherAltInfo {
                num_fields: self.nat(&af[0], as_, 0, "AltParamInfo.numFields")?,
                num_overlaps: self.nat(&af[1], as_, 1, "AltParamInfo.numOverlaps")?,
                has_unit_thunk: boolean(af.get(2), "AltParamInfo.hasUnitThunk")?,
            });
        }
        let u_elim_pos = self.opt_nat(&mf[3], "MatcherInfo.uElimPos?")?;
        let mut discr_infos = Vec::new();
        for d in array(&mf[4])? {
            let (df, _) = ctor(d, 0, 1, "DiscrInfo")?;
            discr_infos.push(self.name(&df[0])?);
        }
        Ok(crate::MatcherEntry { name, num_params, num_discrs, alt_infos, u_elim_pos, discr_infos })
    }
```

**The `self.nat(...)` / `self.opt_nat(...)` calls above are schematic against the probe**: `interp_id.rs` already decodes `Nat` and `Option` fields for `RecursorVal`/`ConstructorVal` — find those helpers (grep `num_params` in `constant_info`'s decode path) and use their exact names and calling convention, including whether small `Nat`s ride in the ctor's `scalars` area (`ms`). This is the one place in this task where the plan cannot pre-write final code, because the physical layout is what step 4 pins — same posture as plan 1's step 4/step 9 pair.

Add the arm in `module_data`'s extension loop, after `"reducibilityExtra"` (use the exact name the probe printed):

```rust
                // SimplePersistentEnvExtension: entries are bare
                // Entry ctors, no scoped wrapper (like reducibilityCore).
                "Lean.Meta.Match.Extension.extension" => {
                    for e in array(&pf[1])? {
                        matchers.push(self.matcher_entry(e)?);
                    }
                }
```

with `let mut matchers = Vec::new();` beside the other accumulators and `matchers,` in the final `ModuleData` literal.

Re-export in `lib.rs`: extend the `module_data::{...}` list with `MatcherAltInfo, MatcherEntry` (keep alphabetical).

- [ ] **Step 8: Run the tests, then the fuzzer**

Run: `cargo test -p leanr_olean` — expect PASS including `matcher_entries_decode` and the pre-existing never-panic proptests (the new path is inside `ModuleData::parse`, so they fuzz it automatically).

Run: `mise run fuzz:olean` — expect 60s, no crash artifact.

- [ ] **Step 9: Commit**

```bash
git status --short crates/leanr_kernel   # must be empty
git add tests/fixtures/Matcher.lean tests/fixtures/Matcher.olean mise.toml crates/leanr_olean
git commit -m "feat(olean): decode the matcher environment extension

whnf's matcher unfolding must identify matcher definitions and their
arities. That data lives in Lean.Meta.Match.Extension.extension entries
which ModuleData previously counted but kept opaque. A name-pattern
heuristic (.match_<n>) was rejected in the plan-2 spec: wrong in a way
that mostly works.

The full MatcherInfo payload is decoded, not an is-a-matcher bit,
because reduce_matcher needs numParams/numDiscrs/altInfos to check
saturation and select alternatives. v4.33 stores altInfos (per-alt
field/overlap/thunk counts), not the older altNumParams, which is now
derived downstream.

Shape pinned empirically against the new prelude-mode Matcher fixture,
per the parser-extension and reducibility precedents."
```

---

### Task 2: The Config fields whnf consults

**Files:**
- Modify: `crates/leanr_meta/src/config.rs`

**Interfaces:**
- Consumes: existing `Config`/`ProjReduction`.
- Produces: `Config` grows `iota: bool`, `zeta_unused: bool`, `zeta_have: bool` (all default `true`); `ProjReduction` grows `YesWithDeltaI`.

**Background:** oracle `Lean.Meta.Config` (Basic.lean:96-220): `iota := true` (:161-ish, "reduce recursor/matcher applications"), `zetaUnused := true`, `zetaHave := true` (final two fields), and `ProjReductionKind` has a fourth constructor `yesWithDeltaI` consulted by `whnfCore`'s proj arm (WHNF.lean:712, "if the current transparency is reducible, do not increase it to instances"). All three bools are in the oracle's `Config.toKey` (bits 12, 21, 22), so they belong in the cache key — which the derived-`Hash` design gives automatically. This trips `ASSERT_CONFIG_SIZE` by design: that is the guard doing its job.

- [ ] **Step 1: Extend the tests first**

In `config.rs` `mod tests`:
- In `flipping_any_single_field_changes_the_key`, add three mutations (`iota`, `zeta_unused`, `zeta_have`) and bump the count assertion from 11 to 14.
- In `proj_variants_are_distinct_in_the_key`, add a fourth key `d` for `ProjReduction::YesWithDeltaI` and assert it distinct from `a`, `b`, `c`.
- Add:

```rust
    // Plan-2 additions match the oracle defaults (Basic.lean): iota,
    // zetaUnused, zetaHave all default true.
    #[test]
    fn plan2_fields_default_on() {
        let c = Config::default();
        assert!(c.iota);
        assert!(c.zeta_unused);
        assert!(c.zeta_have);
    }
```

Run: `cargo test -p leanr_meta config` — expect compile failure (unknown fields/variant).

- [ ] **Step 2: Add the fields and variant**

In `Config` (keep field order stable, append after `unification_hints`):

```rust
    /// Reduce recursor/matcher applications (iota). oracle: Basic.lean,
    /// `iota : Bool := true`; consulted by whnfCore's app arm
    /// (WHNF.lean:685 `unless cfg.iota do return e`).
    pub iota: bool,
    /// Drop `let x := v; e` when `x` does not occur in `e`. oracle:
    /// `zetaUnused : Bool := true`; takes precedence over zeta/zetaHave.
    pub zeta_unused: bool,
    /// When `zeta`, also reduce nondependent lets (`have`). oracle:
    /// `zetaHave : Bool := true`.
    pub zeta_have: bool,
```

Add `YesWithDeltaI` after `YesWithDelta` in `ProjReduction` with doc comment: "like `YesWithDelta` but caps the discriminant whnf at `.instances` transparency (oracle `ProjReductionKind.yesWithDeltaI`)". Update `Default` (`iota: true, zeta_unused: true, zeta_have: true`). Update `ASSERT_CONFIG_SIZE` to the new `size_of` the compiler reports (expected 14 — three bools appended; take the compiler's number, that is the guard's designed workflow).

- [ ] **Step 3: Run tests, lint, commit**

Run: `cargo test -p leanr_meta && mise run lint` — expect PASS/clean.

```bash
git add crates/leanr_meta
git commit -m "feat(meta): Config fields consulted by whnf (iota, zetaUnused, zetaHave, yesWithDeltaI)

Plan 1 deliberately shipped Config as the 11-field subset consulted by
nothing, with ASSERT_CONFIG_SIZE forcing the cache-key decision when a
consumer arrives. whnfCore is that consumer: it consults iota (WHNF.lean
app arm), zetaUnused/zetaHave (letE arm), and the fourth
ProjReductionKind (yesWithDeltaI). All three bools are in the oracle's
toKey (bits 12/21/22) and join our derived-Hash key automatically;
tripping the size assertion here is the guard working as designed."
```

---

### Task 3: `MetaCtx` — shared state, budgets, traversal helpers

**Files:**
- Create: `crates/leanr_meta/src/metactx.rs`
- Modify: `crates/leanr_meta/src/lib.rs`, `crates/leanr_meta/src/error.rs`

**Interfaces:**
- Consumes: `leanr_kernel::{EnvView, ConstantInfo, RecGuard, MAX_REC_DEPTH, LocalContext, FVarIdGen, Nat, KernelError}`, `leanr_kernel::bank::{Store, ExprId, NameId}`, `leanr_kernel::bank::terms::Node` — **check**: `Node` is `crate::bank::terms::Node` inside the kernel; confirm it is reachable from outside (`leanr_kernel::bank::terms::Node`). If `terms` is not `pub`, the decoded one-level view must be obtained another way — look at how `leanr_check` reads nodes and mirror it; if nothing external reads nodes today, raising this is a *kernel API question*: do NOT patch the kernel; instead build a local `enum MetaNode` decoded via public `Store` accessors if they exist, and if they do not, STOP and surface the gap (spec constraint: kernel unmodified — an API export decision belongs to a human).
- Consumes: `leanr_olean::{ReducibilityStatus, ReducibilityEntry, MatcherEntry, EntryScope}` (Tasks 1, plan 1).
- Produces:
  - `leanr_meta::MetaCtx<'e>` with `MetaCtx::new(view: EnvView<'e>, scratch: &'e mut Store, cfg: Config, reducibility: &[ReducibilityEntry], matchers: &[MatcherEntry]) -> MetaCtx<'e>`
  - accessors used by every later task: `node(&self, e) -> Node`, `data(&self, e) -> ExprData`, `get_app_fn`, `get_app_args`, `get_app_num_args`, `mk_app_spine(&mut self, f, &[ExprId])`, `guarded(&mut self, f)`, `step(&mut self) -> Result<(), MetaError>`, `status_of(&self, NameId) -> ReducibilityStatus`, `matcher_of(&self, NameId) -> Option<&MatcherEntry>`, `mctx(&self) -> &MetavarContext`, `mctx_mut(&mut self) -> &mut MetavarContext`, `cfg(&self) -> Config`, `set_transparency(&mut self, TransparencyMode)`
  - `MetaError::Infer(String)` (new variant; an inference failure is a caller/term problem, still incompleteness)

- [ ] **Step 1: Write the failing test**

Create `crates/leanr_meta/src/metactx.rs` with the struct, constructor, helpers, and tests. The struct (doc comments abbreviated here; write real ones citing the spec's § MetaCtx):

```rust
//! All shared `MetaM` state. Each concern module (`whnf`, `infer`, ...)
//! contributes an `impl MetaCtx` block — inherent impls split across
//! files, direct calls, no dynamic dispatch (spec § MetaCtx).
//!
//! Traversal is ExprId-native over the bank, the `tc.rs` idiom: nodes
//! decode one level at a time via `Store::expr_node`, caches key on
//! ids, and `Store::to_expr` is never called on a hot path.

use std::collections::HashMap;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId, Store};
use leanr_kernel::{EnvView, ExprData, FVarIdGen, LocalContext, RecGuard, MAX_REC_DEPTH};
use leanr_olean::{EntryScope, MatcherEntry, ReducibilityEntry, ReducibilityStatus};

use crate::{Config, MetaError, MetavarContext, TransparencyMode};

/// Stack-growth constants — the same values `tc.rs` uses (private
/// there, so restated; keep in sync by inspection).
const RED_ZONE: usize = 128 * 1024;
const STACK_CHUNK: usize = 4 * 1024 * 1024;

/// Deterministic step budget (spec § Determinism: a step counter, not
/// maxHeartbeats — machine-independent by construction, a knowing
/// divergence from the oracle). The value is leanr-specific; queries
/// that come near it must be excluded from the differential corpus.
pub const DEFAULT_STEP_BUDGET: u64 = 10_000_000;

pub struct MetaCtx<'e> {
    pub(crate) view: EnvView<'e>,
    pub(crate) scratch: &'e mut Store,
    pub(crate) cfg: Config,
    pub(crate) mctx: MetavarContext,
    pub(crate) lctx: LocalContext,
    pub(crate) fvar_gen: FVarIdGen,
    pub(crate) guard: RecGuard,
    guard_depth: u32,
    steps: u64,
    step_budget: u64,
    /// (config cache key, expr) -> whnf result. Permanent entries only
    /// (mvar- and fvar-free inputs); the transient side arrives with
    /// defeq in plan 3. See `cacheable` below.
    pub(crate) whnf_cache: HashMap<(u64, ExprId), ExprId>,
    pub(crate) whnf_core_cache: HashMap<(u64, ExprId), ExprId>,
    pub(crate) infer_cache: HashMap<(u64, ExprId), ExprId>,
    /// ReducibilityStatus per constant; absent => Semireducible.
    reducibility: HashMap<NameId, ReducibilityStatus>,
    matchers: HashMap<NameId, MatcherEntry>,
    /// The `smartUnfolding` option (oracle default: true).
    pub(crate) smart_unfolding: bool,
    /// Plan-3/4 seam: the `canUnfold?` override predicate channel
    /// (oracle: Meta.Context.canUnfold?). `whnf_matcher` (task 6) is
    /// its only setter this plan. When set, results are not cached
    /// (oracle useWHNFCache, WHNF.lean:1082-1088).
    pub(crate) can_unfold_override: bool,
}

impl<'e> MetaCtx<'e> {
    pub fn new(
        view: EnvView<'e>,
        scratch: &'e mut Store,
        cfg: Config,
        reducibility: &[ReducibilityEntry],
        matchers: &[MatcherEntry],
    ) -> MetaCtx<'e> {
        // Global entries only: scoped reducibility entries require the
        // M3b3-style activation model, out of scope for the meta core
        // (they are rare and Mathlib's are decoded but unconsulted
        // here; revisit when a corpus divergence implicates one).
        let reducibility = reducibility
            .iter()
            .filter(|e| matches!(e.scope, EntryScope::Global))
            .map(|e| (e.name, e.status))
            .collect();
        let matchers = matchers.iter().map(|m| (m.name, m.clone())).collect();
        MetaCtx {
            view,
            scratch,
            cfg,
            mctx: MetavarContext::new(),
            lctx: LocalContext::default(),
            fvar_gen: FVarIdGen::default(),
            guard: RecGuard::new(),
            guard_depth: 0,
            steps: 0,
            step_budget: DEFAULT_STEP_BUDGET,
            whnf_cache: HashMap::new(),
            whnf_core_cache: HashMap::new(),
            infer_cache: HashMap::new(),
            reducibility,
            matchers,
            smart_unfolding: true,
            can_unfold_override: false,
        }
    }

    pub fn cfg(&self) -> Config {
        self.cfg
    }

    pub fn set_transparency(&mut self, t: TransparencyMode) {
        self.cfg.transparency = t;
    }

    pub fn mctx(&self) -> &MetavarContext {
        &self.mctx
    }

    pub fn mctx_mut(&mut self) -> &mut MetavarContext {
        &mut self.mctx
    }

    pub fn status_of(&self, n: NameId) -> ReducibilityStatus {
        // Absent => Semireducible (getReducibilityStatusCore's
        // fallback; plan-1 Global Constraint).
        self.reducibility
            .get(&n)
            .copied()
            .unwrap_or(ReducibilityStatus::Semireducible)
    }

    pub fn matcher_of(&self, n: NameId) -> Option<&MatcherEntry> {
        self.matchers.get(&n)
    }

    /// One deterministic step. Every whnf_core / whnf / infer entry
    /// calls this once; exhaustion is a distinct error, never a
    /// verdict (spec § Error handling).
    pub(crate) fn step(&mut self) -> Result<(), MetaError> {
        self.steps += 1;
        if self.steps > self.step_budget {
            return Err(MetaError::StepBudgetExhausted);
        }
        Ok(())
    }

    /// Depth guard + stack growth, the tc.rs `guarded` idiom.
    pub(crate) fn guarded<R>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<R, MetaError>,
    ) -> Result<R, MetaError> {
        if self.guard_depth >= MAX_REC_DEPTH {
            return Err(MetaError::DepthBudgetExhausted);
        }
        self.guard_depth += 1;
        let r = stacker::maybe_grow(RED_ZONE, STACK_CHUNK, || f(self));
        self.guard_depth -= 1;
        r
    }

    // -- ExprId-native traversal helpers (tc.rs idiom) --

    pub(crate) fn node(&self, e: ExprId) -> Node {
        self.scratch.expr_node(Some(self.view.store), e)
    }

    pub(crate) fn data(&self, e: ExprId) -> ExprData {
        self.scratch.expr_data(Some(self.view.store), e)
    }

    pub(crate) fn get_app_fn(&self, e: ExprId) -> ExprId {
        let mut cur = e;
        while let Node::App { f, .. } = self.node(cur) {
            cur = f;
        }
        cur
    }

    pub(crate) fn get_app_args(&self, e: ExprId) -> Vec<ExprId> {
        let mut args = Vec::new();
        let mut cur = e;
        while let Node::App { f, arg } = self.node(cur) {
            args.push(arg);
            cur = f;
        }
        args.reverse();
        args
    }

    pub(crate) fn get_app_num_args(&self, e: ExprId) -> usize {
        let mut n = 0;
        let mut cur = e;
        while let Node::App { f, .. } = self.node(cur) {
            n += 1;
            cur = f;
        }
        n
    }

    pub(crate) fn mk_app_spine(&mut self, f: ExprId, args: &[ExprId]) -> Result<ExprId, MetaError> {
        let mut r = f;
        for &a in args {
            r = self.scratch.expr_app(Some(self.view.store), r, a)?;
        }
        Ok(r)
    }

    /// Permanent-cache predicate: closed, mvar-free, no override
    /// predicate active. oracle: useWHNFCache (WHNF.lean:1082-1088)
    /// — "cache only closed terms without expr metavars", plus the
    /// canUnfold? escape. The transient side of the spec's cache
    /// split arrives with defeq (plan 3); until then non-cacheable
    /// terms are simply recomputed, which is correct and slow, never
    /// wrong.
    pub(crate) fn cacheable(&self, e: ExprId) -> bool {
        let d = self.data(e);
        !d.has_fvar() && !d.has_expr_mvar() && !self.can_unfold_override
    }
}
```

Note the `KernelError -> MetaError` conversion already exists (`error.rs`), so `?` on `expr_app` works once `mk_app_spine` returns `MetaError` — if the compiler disagrees, add `.map_err(MetaError::from)`.

Add `Infer(String)` to `MetaError` in `error.rs` with doc: "inference met a term it cannot type (loose bvar, unknown constant, non-forall function type). Incompleteness, never unsoundness — the kernel is the checker."

Tests in the same file (`mod tests`). They need an `EnvView` over an empty environment — mirror the construction at `leanr_check/src/schedule.rs:324` (a `ConstSource` over empty `CheckedConstants`, `extra: None`, `quot_initialized: false`, `store` = the persistent store); wrap it in a local helper so each test reads clean. Add a test-only budget setter `#[cfg(test)] pub(crate) fn set_step_budget(&mut self, n: u64)`.

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::MetaError;

    // Reconcile against schedule.rs:324 — the shape, not the letter:
    // an EnvView over an empty persistent store and no constants.
    fn with_ctx<R>(f: impl FnOnce(&mut MetaCtx) -> R) -> R {
        let base = Store::persistent();
        let mut scratch = Store::scratch();
        let empty = leanr_kernel::CheckedConstants::default();
        let view = EnvView {
            consts: (&empty).into(), // reconcile: however schedule.rs builds ConstSource
            extra: None,
            quot_initialized: false,
            store: &base,
        };
        let mut ctx = MetaCtx::new(view, &mut scratch, Config::default(), &[], &[]);
        f(&mut ctx)
    }

    #[test]
    fn step_budget_exhausts_as_its_own_error() {
        with_ctx(|ctx| {
            ctx.set_step_budget(2);
            assert!(ctx.step().is_ok());
            assert!(ctx.step().is_ok());
            assert_eq!(ctx.step(), Err(MetaError::StepBudgetExhausted));
        });
    }

    #[test]
    fn status_defaults_to_semireducible() {
        with_ctx(|ctx| {
            let s = ctx.scratch.intern_str(None, "ghost").expect("intern");
            let n = ctx.scratch.name_str(None, None, s).expect("name");
            assert_eq!(ctx.status_of(n), ReducibilityStatus::Semireducible);
        });
    }

    #[test]
    fn app_helpers_roundtrip() {
        with_ctx(|ctx| {
            let s = ctx.scratch.intern_str(None, "f").expect("intern");
            let n = ctx.scratch.name_str(None, None, s).expect("name");
            let f = ctx.scratch.expr_fvar(None, Some(n)).expect("fvar");
            let z = ctx.scratch.level_zero(None).expect("level");
            let a = ctx.scratch.expr_sort(None, z).expect("sort");
            let app = ctx.mk_app_spine(f, &[a, a]).expect("spine");
            assert_eq!(ctx.get_app_fn(app), f);
            assert_eq!(ctx.get_app_args(app), vec![a, a]);
            assert_eq!(ctx.get_app_num_args(app), 2);
        });
    }
}
```

(`Store::scratch()` may take the base store — reconcile against `bank/mod.rs:107-125`; likewise `expr_fvar`'s exact name. Per the Global Constraints rule, adjust this crate, never the kernel.)

- [ ] **Step 2: Declare, run, commit**

Add `mod metactx;` + `pub use metactx::{MetaCtx, DEFAULT_STEP_BUDGET};` to `lib.rs`. Run `cargo test -p leanr_meta` (expect PASS), `git status --short crates/leanr_kernel` (empty), `mise run lint`, then:

```bash
git add crates/leanr_meta
git commit -m "feat(meta): MetaCtx shared state, deterministic budgets, id-native traversal

The struct the spec's mutual-recursion section calls for: every later
concern module contributes an impl MetaCtx block. Traversal is
ExprId-native over the bank (plan 1's deferred question, answered in
the plan-2 spec): one-level Node decode, id-keyed caches keyed jointly
on Config::cache_key, Store::to_expr never on a hot path.

Budgets are deterministic counters, not maxHeartbeats: a knowing
divergence from the oracle, chosen so the differential oracle itself
stays deterministic. Exhaustion is a distinct error, never a verdict.

The permanent whnf-cache predicate transcribes useWHNFCache (closed,
mvar-free, no override predicate); the transient side arrives with
defeq in plan 3."
```

---

### Task 4: Meta-level type inference (`infer.rs`)

**Files:**
- Create: `crates/leanr_meta/src/infer.rs`
- Modify: `crates/leanr_meta/src/lib.rs`

**Interfaces:**
- Consumes: `MetaCtx` and its helpers (Task 3); `leanr_kernel::subst::{instantiate, instantiate_rev, instantiate_level_params}`; `LocalContext::{mk_local_decl, get}`; `Store::{expr_sort, expr_forall, level_succ (or the real level-constructor names — reconcile), level_list_at, intern_level_list}`.
- Produces: `MetaCtx::infer_type(&mut self, e: ExprId) -> Result<ExprId, MetaError>`.
- **Ordering note:** matcher reduction (Task 6) calls `infer_type`; `infer_type`'s app arm calls `whnf` (Task 5). The two tasks are mutually recursive through `MetaCtx`, so this task compiles against a *temporary* private `fn whnf_for_infer` that only does what the app arm needs before Task 5 lands — see step 2. Task 5 deletes it.

**Background (oracle: `src/Lean/Meta/InferType.lean`):** `inferTypeImp` (:238-254) dispatches on the node; per-arm sources: `inferConstType` :121-127 (instantiate the declared type's level params; length mismatch is an error), `inferAppType` :106-119 (infer the head, then consume foralls across the args, whnf-ing when the type is not syntactically a forall; if whnf does not yield a forall, error), `inferProjType` :128-162, `inferForallType` :178-186 (telescope: sort of an imax chain), `inferLambdaType` :188-194 (telescope with fresh fvars, then rebuild the pi), `inferMVarType`/`inferFVarType` :196-204 (context lookups), `lit` returns the literal's type (`Nat`/`String` const), `sort l` returns `Sort (succ l)`, `mdata` recurses, `bvar` is an error. **Inference never checks** — no defeq of argument types (the kernel is the checker; spec § infer.rs).

- [ ] **Step 1: Write the failing tests**

Create `crates/leanr_meta/src/infer.rs` with tests first (same-file `mod tests`), building tiny terms directly through the `Store` API in a scratch region over an env containing `Prelude0.olean`'s replayed constants (mirror `check_fixtures.rs`'s `prelude0_replays_from_empty_env` to obtain a populated `Environment`, then `EnvView` per `schedule.rs:324`):

```rust
    // All tests reconcile Store constructor names against bank/terms.rs.
    // `with_prelude0_ctx` is this file's env helper: replay Prelude0.olean
    // per check_fixtures.rs::prelude0_replays_from_empty_env, build the
    // EnvView per schedule.rs:324, wrap in MetaCtx::new(view, scratch,
    // Config::default(), &md.reducibility, &md.matchers).
    // Exemplar (the rest follow this pattern — write every body in full
    // before implementing):
    #[test]
    fn sort_infers_to_succ() {
        with_prelude0_ctx(|ctx| {
            let z = ctx.scratch.level_zero(None).expect("level");
            let sort0 = ctx.scratch.expr_sort(None, z).expect("sort");
            let t = ctx.infer_type(sort0).expect("infer");
            let one = ctx.scratch.level_succ(None, z).expect("succ"); // reconcile name
            let sort1 = ctx.scratch.expr_sort(None, one).expect("sort");
            assert_eq!(t, sort1, "infer(Sort 0) must be Sort 1 (same interned id)");
        });
    }

    #[test]
    fn const_type_instantiates_levels() { /* infer(const N) == its declared type */ }

    #[test]
    fn lambda_infers_to_pi() { /* infer(fun (x : N) => x) == N -> N */ }

    #[test]
    fn app_consumes_foralls() { /* infer(N.succ N.zero) (via Prelude0's N) == N */ }

    #[test]
    fn mvar_infers_from_decl() { /* declare ?m : Sort 0; infer(?m expr) == Sort 0 */ }

    #[test]
    fn loose_bvar_is_an_error() { /* infer(bvar 0) => Err(MetaError::Infer(_)) */ }

    #[test]
    fn infer_caches_closed_terms() { /* infer twice; second hits infer_cache (probe via cache len) */ }
```

Each body is short; write them fully against the reconciled API before implementing.

- [ ] **Step 2: Implement**

`impl MetaCtx` in `infer.rs`. Structure (transcription targets cited above; reconcile constructor/accessor names):

```rust
impl<'e> MetaCtx<'e> {
    /// oracle: inferTypeImp (InferType.lean:238-254). Inference
    /// without checking — the kernel re-checks everything downstream.
    pub fn infer_type(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        self.step()?;
        self.guarded(|s| s.infer_core(e))
    }

    fn infer_core(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let key = (self.cfg.cache_key(), e);
        let use_cache = self.cacheable(e);
        if use_cache {
            if let Some(&t) = self.infer_cache.get(&key) {
                return Ok(t);
            }
        }
        let t = match self.node(e) {
            Node::Const { name, levels } => self.infer_const(name, levels)?,
            Node::Proj { .. } | Node::ProjBig { .. } => self.infer_proj(e)?,
            Node::App { .. } => self.infer_app(e)?,
            Node::MVar { id } => self.infer_mvar(id)?,
            Node::FVar { id } => self.infer_fvar(id)?,
            Node::BVar { .. } | Node::BVarBig { .. } => {
                return Err(MetaError::Infer("loose bound variable".into()))
            }
            Node::MData { expr, .. } => self.infer_core(expr)?,
            Node::LitNat { .. } => self.lit_type("Nat")?,
            Node::LitStr { .. } => self.lit_type("String")?,
            Node::Sort { level } => self.sort_succ(level)?,
            Node::Forall { .. } => self.infer_forall(e)?,
            Node::Lam { .. } | Node::LetE { .. } => self.infer_lambda(e)?,
        };
        if use_cache {
            self.infer_cache.insert(key, t);
        }
        Ok(t)
    }
}
```

Per-arm notes (each becomes a private method with its oracle citation in the doc comment):

- `infer_const` — env lookup via the region-correct pattern `tc.rs::env_get_with` documents (persistent-region ids only for `EnvView::get_with`); check `level_params.len() == level_list_at(levels).len()` (mismatch => `Infer`); `instantiate_level_params(self.scratch, Some(self.view.store), declared_type, &params, &levels, &mut self.guard)` — destructure `self` so the borrows are disjoint (the tc.rs porting rule).
- `infer_app` — `f = get_app_fn(e)`, `args = get_app_args(e)`; `ty = infer_core(f)`; loop over args: if `node(ty)` is `Forall`, collect the arg into a pending-substitution vec and step to the body; else `ty = instantiate_rev(pending)` then `whnf(ty)` (see the ordering note; until Task 5 this is `whnf_for_infer`) and require `Forall`, else `Infer("function expected")`. Finish with `instantiate_rev` of the remaining pending args. This is `inferAppType`'s exact shape (:106-119) — the batching via `instantiateBetaRevRange` becomes the pending-vec.
- `infer_proj` — transcribe `inferProjType` (:128-162): whnf the structure's inferred type to a `Const` head naming an inductive with one ctor; instantiate the ctor's type with the type's levels and args; walk `idx` forall-binders instantiating each with `Proj(i, s)`; the next domain is the answer. Any shape violation => `Infer`.
- `infer_mvar` — `MVarId(id)` lookup in `self.mctx` (`Infer` if undeclared; the `Option<NameId>`-anonymous case is also `Infer`).
- `infer_fvar` — `self.lctx.get(id)` (`Infer` if absent; same anonymous note).
- `infer_forall` — telescope: walk `Forall` bodies instantiating each binder with a fresh fvar (`self.lctx.mk_local_decl` + `self.fvar_gen` — mirror how `tc.rs`'s own `infer_forall` does this dance, WITHOUT copying its code: same bank API, independently written); `getLevel` of each domain and of the final body (infer + whnf to a `Sort`, else `Infer`); fold `imax` right-to-left via the store's level constructors; result `Sort(fold)`. Restore the lctx afterwards (save/truncate — see `LocalContext`'s API).
- `infer_lambda` — same telescope; infer the body; rebuild with `abstract_fvars` + `expr_forall` per binder (`mkForallFVars`'s effect). `LetE` takes this arm too (oracle :252).
- `lit_type` / `sort_succ` — intern `Nat`/`String` const / `Sort (succ l)` via store constructors.

Temporary `fn whnf_for_infer(&mut self, e: ExprId) -> Result<ExprId, MetaError>`: doc comment "Task-4 scaffold; Task 5 replaces every call site with the real `whnf` and deletes this." Body: loop { instantiate assigned head mvar; beta-reduce `(fun ..) args` heads via `instantiate`; else break } — enough for the tests above; the real `whnf` strictly extends it.

- [ ] **Step 3: Run tests, lint, kernel-untouched check, commit**

`cargo test -p leanr_meta` PASS; `mise run lint` clean; `git status --short crates/leanr_kernel` empty.

```bash
git add crates/leanr_meta
git commit -m "feat(meta): Meta-level infer_type

Transcribed from inferTypeImp and its per-arm helpers
(InferType.lean:106-254): mvar heads resolve through MetavarContext,
fvars through the LocalContext, apps consume foralls whnf-ing only when
the type is not syntactically a pi, lambdas/lets telescope with fresh
fvars. Inference never checks — the kernel is the independent checker,
so no defeq of argument types anywhere (spec § infer.rs).

Cached per (Config::cache_key, ExprId) for closed mvar-free terms."
```

---

### Task 5: `whnf_core` and delta `whnf` (`whnf.rs`)

**Files:**
- Create: `crates/leanr_meta/src/whnf.rs`
- Modify: `crates/leanr_meta/src/lib.rs`, `crates/leanr_meta/src/infer.rs` (delete `whnf_for_infer`)

**Interfaces:**
- Consumes: Tasks 3-4; `leanr_kernel::subst::{instantiate, instantiate_rev, instantiate_level_params}`; `ConstantInfo` variants (`Defn`, `Rec`, `Quot`, `Ctor`, `Induct`); `EnvView::is_structure_like`.
- Produces:
  - `MetaCtx::whnf(&mut self, e: ExprId) -> Result<ExprId, MetaError>`
  - `MetaCtx::whnf_core(&mut self, e: ExprId) -> Result<ExprId, MetaError>`
  - `pub(crate) enum ReduceMatcherResult { Reduced(ExprId), Stuck(ExprId), NotMatcher, PartialApp }` and a **seam** `MetaCtx::reduce_matcher(&mut self, e) -> Result<ReduceMatcherResult, MetaError>` returning `NotMatcher` (doc: "Task 6 replaces this body with the reduceMatcher? transcription, WHNF.lean:536-575")
  - seam `MetaCtx::unfold_definition(&mut self, e) -> Result<Option<ExprId>, MetaError>` — this task: plain delta (no smart unfolding, no matcher suppression); Task 7 extends it in place.

**Background (oracle: `src/Lean/Meta/WHNF.lean`; per-rule citations inline below).** The structure is: `whnfEasyCases` (:385-414) handles leaves and dispatches; `whnfCore` (:648-715) is the no-delta loop; `whnfImp` (:1102-1121) is easy-cases → cache → `whnfCore` → `reduceNat?` → `reduceNative?` → `unfoldDefinition?` → loop.

- [ ] **Step 1: Write the failing tests**

In `whnf.rs` `mod tests`, over a `Prelude0`-replayed env (Task 4's pattern) plus scratch-built terms:

```rust
    // Exemplar (Task 4's with_prelude0_ctx helper; the rest follow this
    // pattern — write every body in full before implementing):
    #[test]
    fn beta_reduces() {
        with_prelude0_ctx(|ctx| {
            let n_const = ctx.const_named("N"); // test helper: intern name, expr_const with no levels
            let zero = ctx.const_named("N.zero");
            // fun (x : N) => x, i.e. Lam(N, bvar 0)
            let bvar0 = ctx.scratch.expr_bvar(None, 0).expect("bvar");
            let lam = ctx
                .scratch
                .expr_lam(None, None, n_const, bvar0, leanr_kernel::BinderInfo::Default)
                .expect("lam"); // reconcile arg order against terms.rs
            let app = ctx.mk_app_spine(lam, &[zero]).expect("app");
            assert_eq!(ctx.whnf_core(app).expect("whnf_core"), zero);
        });
    }

    #[test]
    fn zeta_reduces_used_let() { /* whnf_core(let x := N.zero; N.succ x) == N.succ N.zero, cfg.zeta on */ }

    #[test]
    fn zeta_off_leaves_let() { /* same term, cfg.zeta = false, zeta_unused = false => unchanged */ }

    #[test]
    fn assigned_mvar_head_instantiates() { /* assign ?m := N.zero; whnf_core(?m) == N.zero */ }

    #[test]
    fn iota_reduces_recursor() { /* whnf(N.rec (motive) z s (N.succ N.zero)) steps once (Prelude0's N.rec) */ }

    #[test]
    fn delta_respects_transparency() {
        /* a Semireducible const unfolds at Default, not at Reducible;
           an Irreducible one only at All — drive status via a
           hand-inserted reducibility entry, not a fixture. */
    }

    #[test]
    fn nat_literals_fold() { /* whnf(Nat.add (lit 2) (lit 3)) == lit 5 — names interned by hand */ }

    #[test]
    fn whnf_caches_closed_terms_per_config() { /* same term, two transparencies => two cache keys */ }
```

Run `cargo test -p leanr_meta whnf` — compile failure (module absent).

- [ ] **Step 2: Implement `whnf.rs`**

One `impl MetaCtx` block. Every method carries its oracle citation. The skeleton to transcribe (adjusting `Expr` pattern matches to `Node` and monadic recursion to `self.guarded`):

```rust
impl<'e> MetaCtx<'e> {
    /// oracle: whnfImp (WHNF.lean:1102-1121).
    pub fn whnf(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        self.step()?;
        self.guarded(|s| s.whnf_imp(e))
    }

    fn whnf_imp(&mut self, e: ExprId) -> Result<ExprId, MetaError> {
        let e = self.whnf_easy_cases(e)?;
        if !self.is_head_candidate(e) {
            return Ok(e); // easy cases returned a leaf
        }
        let key = (self.cfg.cache_key(), e);
        let use_cache = self.cacheable(e);
        if use_cache {
            if let Some(&r) = self.whnf_cache.get(&key) {
                return Ok(r);
            }
        }
        let e1 = self.whnf_core(e)?;
        let r = if let Some(v) = self.reduce_nat(e1)? {
            v
        } else if let Some(e2) = self.unfold_definition(e1)? {
            self.guarded(|s| s.whnf_imp(e2))?
        } else {
            e1
        };
        if use_cache {
            self.whnf_cache.insert(key, r);
        }
        Ok(r)
    }
```

Notes for the implementer, per method:

- `whnf_easy_cases` (oracle :385-414): `Forall`/`Lam`/`Sort`/`LitNat`/`LitStr` return as-is; `BVar` is `MetaError::Infer("loose bvar in whnf")` (the oracle panics; we never panic — Global Constraints); `MData` recurses into its expr; `FVar` consults `self.lctx.get`: a let-decl value is followed only under `cfg.zeta_delta` (the `isImplementationDetail` and `zetaDeltaSet`/`trackZetaDelta` channels are elaborator context that does not exist yet — record as a seam comment citing :399-407, arriving with the term elaborator in M4b); `MVar` follows `self.mctx.assignment` (unassigned returns as-is; the *delayed*-assignment channel is a plan-3 seam, :585-607); `Const`/`App`/`Proj`/`LetE` fall through to the caller. Since Rust has no `k` continuation, implement as a loop returning an enum `Easy(ExprId) | Hard(ExprId)`, and let `whnf_imp`/`whnf_core` match on it (`is_head_candidate` above tests the `Hard` case — implement however reads best, but keep the easy/hard split explicit).
- `whnf_core` (oracle :648-715): loop with the three hard arms:
  - `LetE` (:657-663): `cfg.zeta && (!nondep || cfg.zeta_have)` → `expand_let` (transcribe `expandLet` :617-624 with `instantiate_rev` over the accumulated values); else `cfg.zeta_unused && body has no loose bvars` → `consume_unused_let` (:634-637, use `data(body).loose_bvar_range() == 0`); else return.
  - `App` (:664-703): reduce the head via recursive `whnf_core`; beta when `f'` is a lambda and (`cfg.beta` or the head was not syntactically a lambda) — transcribe the `betaRev` loop with `instantiate_rev` over the reversed args, consuming as many lambda binders as args (partial-application: consume what matches, re-apply the rest); then the delayed-assignment seam (returns `None` this plan); then `unless cfg.iota return`; then `self.reduce_matcher(e)` (the Task-6 seam — `NotMatcher` now); then head-const dispatch: `Rec` → `reduce_rec` (:228-267), `Quot` → `reduce_quot_rec` (:270-290), `Defn` → unfold **only** when `is_aux_def` — which is `isAuxRecursor` data the environment does not carry typed; **seam**: return `e` unchanged with a doc comment citing :697-701 and noting aux-recursor (`casesOn`/`brecOn`-style) unfolding in `whnf_core` lands with the extension that identifies them; plain-definition unfolding still happens in `whnf` via delta, which is what the tier-1 corpus exercises. `Axiom`/others → return.
  - `Proj` (:704-712): dispatch on `cfg.proj`: `No` → return; `Yes` → discriminant via `whnf_core`; `YesWithDelta` → via `whnf`; `YesWithDeltaI` → via `whnf` with transparency temporarily capped: `let saved = cfg.transparency; set to min(saved, Instances) by rank; restore after` (oracle `whnfAtMostI`). Then `project_core` (:565-575): `to_ctor_if_lit` the discriminant (:23-29 — `LitNat 0` → `Nat.zero` const, `LitNat n` → `Nat.succ (lit n-1)`; the `LitStr` arm needs `String.ofList` + a char-list build — **seam**: return unchanged, cite :27-28, no tier-1 string-proj queries); require a `Ctor` head; answer is arg `ctor.num_params + idx` (via `nat_to_usize`-style conversion — write a local one, the kernel's is private).
  - `whnf_core` results go through the `whnf_core_cache` under the same `cacheable` predicate.
- `reduce_rec` (oracle :228-267): major premise at `get_major_idx` (compute from `RecursorVal`: `num_params + num_motives + num_minors + num_indices` — check the kernel's `RecursorVal` for an existing major-idx helper and reconcile); whnf the major (the `isWFRec` `.all`-bump for `Acc.rec`/`WellFounded.rec` at `.default`, :230-237 — transcribe: compare the recursor name against interned `Acc.rec`/`WellFounded.rec` names, bump transparency for that whnf only); `to_ctor_when_k` **seam** for `k` recursors: this plan compares the K-major's inferred type against the recursor's expected type **structurally** (`ExprId` equality after `whnf`) instead of by `isDefEq` — doc comment citing :150-170 and "plan 3 upgrades this comparison to is_def_eq"; `to_ctor_if_lit`; `cleanup_nat_offset_major` **seam** (return unchanged; cite :218-226; offset constraints are a plan-3 concern with `offsetCnstrs`); `to_ctor_when_structure` (:171-196): when the major's type is structure-like (`view.is_structure_like`) and the major is not a ctor app, eta-expand via `Proj` fields — transcribe; then rule lookup by ctor name (`RecursorRule { ctor, nfields, rhs }`), instantiate rule levels, apply params+motives+minors, then the major's trailing `nfields` args, then the remaining rec args (:246-263, the three `mkAppRange` calls — transcribe with index arithmetic on the args vec, `Nat`→usize conversions checked).
- `reduce_quot_rec` (oracle :270-290): `Quot.lift` (majorPos 5, argPos 3) / `Quot.ind` (majorPos 4, argPos 3); whnf the major; require the 3-deep app shape ending in a `Quot` ctor-kind const; apply.
- `reduce_nat` (oracle :1054-1078): head-const dispatch over the interned names `Nat.add/sub/mul/div/mod/gcd/beq/ble/land/lor/xor/shiftLeft/shiftRight/pow/succ`; operands via `with_nat_value` (:1020-1030: closed, mvar-free, whnf to `LitNat` or `Nat.zero` const); compute with `leanr_kernel::Nat` arithmetic (check which ops `Nat` exposes — it wraps a bignum; reconcile, and for `pow` port the kernel's `REDUCE_POW_MAX_EXP` exponent guard, returning `None` past it); `beq`/`ble` produce `Bool.true`/`Bool.false` consts. Intern the needed names once in `MetaCtx::new` (the `tc.rs` constructor idiom).
- `unfold_definition` (this task's version): `Const` head only (both bare and applied): env lookup; require `Defn` with a value (`Thm` also unfolds at `.all` only — transcribe `getUnfoldableConst`'s actual arms from `GetUnfoldableConst.lean`, which also consults `can_unfold(self.cfg.transparency, self.status_of(name))`); level-param length check; `instantiate_level_params`; applied case beta-reduces the args into the value (`deltaBetaDefinition`, :417-424). Task 7 wraps this with smart unfolding and matcher suppression.

Delete `whnf_for_infer` in `infer.rs` and point its call sites at `self.whnf`.

- [ ] **Step 3: Run all tests, lint, kernel check, commit**

`cargo test -p leanr_meta` PASS (all tasks so far); `mise run lint`; `git status --short crates/leanr_kernel` empty.

```bash
git add crates/leanr_meta
git commit -m "feat(meta): whnf_core and delta whnf

Transcribed from WHNF.lean with a citation per rule: whnfEasyCases
(:385), whnfCore's let/app/proj arms (:648-715), reduceRec (:228),
reduceQuotRec (:270), reduceNat (:1054), expandLet/consumeUnusedLet
(:617/:634), and the whnfImp driver (:1102). Delta is gated on
can_unfold against decoded ReducibilityStatus.

Named seams (each a documented function citing its oracle line and
landing plan): matcher reduction (task 6), smart unfolding (task 7),
delayed mvar assignments (plan 3), to_ctor_when_k's defeq comparison
(structural until plan 3), nat-offset major cleanup (plan 3),
aux-recursor unfolding in whnf_core and string-literal projection
(later slices). No silent divergence: every seam is greppable."
```

---

### Task 6: Matcher reduction

**Files:**
- Modify: `crates/leanr_meta/src/whnf.rs` (replace the `reduce_matcher` seam body; add helpers)

**Interfaces:**
- Consumes: `MatcherEntry` via `MetaCtx::matcher_of` (Tasks 1, 3); `infer_type` (Task 4); `whnf` (Task 5); `LocalContext::mk_local_decl` + `abstract_fvars` for the bounded telescope.
- Produces: `reduce_matcher` returning real `Reduced`/`Stuck`/`NotMatcher`/`PartialApp` verdicts; `MetaCtx::get_stuck_mvar(&mut self, e) -> Result<Option<MVarId>, MetaError>`.

**Background (oracle: WHNF.lean:536-575 `reduceMatcher?`, :522-534 `whnfMatcher`, :498-520 `canUnfoldAtMatcher`, :322-383 `getStuckMVar?`).** Per-alternative arity is derived: `altNumParams[i] = numFields + numOverlaps + (hasUnitThunk ? 1 : 0) + numDiscrEqs` where `numDiscrEqs` counts `discrInfos` entries with a name (MatcherInfo.lean:94-108). `numAlts = altInfos.len()`.

- [ ] **Step 1: Write the failing test**

The committed `Matcher.olean` fixture (Task 1) replays like `Prelude0` (it is prelude-mode). Add to `whnf.rs` tests:

```rust
    /// isZero (N.succ N.zero) whnf-reduces through its matcher to
    /// N.zero at Default transparency.
    #[test]
    fn matcher_application_reduces() { /* replay Matcher.olean; build the app; whnf; expect N.zero */ }

    /// A matcher applied to a stuck (fvar) discriminant does not reduce.
    #[test]
    fn matcher_stuck_on_free_discriminant() { /* whnf leaves the application head intact */ }
```

Run: expect the first to FAIL (seam returns `NotMatcher`, so the matcher constant is delta-unfolded or left stuck — either way not `N.zero` in one clean matcher step... **verify the failure mode**: if plain delta at Default happens to fully reduce it, strengthen the test to `.reducible` transparency, where delta on the matcher aux is blocked and only the matcher path can reduce — that transparency split is exactly why matcher reduction exists, :470-495).

- [ ] **Step 2: Implement**

Replace the seam body with the `reduceMatcher?` transcription:

- `reduce_matcher(e)`: consume-mdata the head chain; head must be `Const(decl, lvls)` with `self.matcher_of(decl)` → else `NotMatcher`. `prefix_sz = num_params + 1 + num_discrs`; `args.len() < prefix_sz + num_alts` → `PartialApp`. Env-lookup the matcher's `Defn`, `instantiate_level_params`, then `unfold_nested_dite` when transparency is `Reducible | Instances | Implicit` (:552-553): transcribe :483-495 — a bank-row transform replacing any `Const dite` (the interned root name `dite`) with `dite`'s instantiated value; if `dite` is not in the env (the prelude fixture has none) the transform is the identity — that is oracle-faithful, `find?` just never hits. Apply the first `prefix_sz` args (`mk_app_spine`), `infer_type` it, then the **bounded telescope** (:555): walk `num_alts` foralls of that type, minting a fresh fvar per binder (`mk_local_decl`); apply the aux app to those fvars; `whnf_matcher` it; if its head equals one of the fvars `h_i`, the verdict is `Reduced`: alt = `args[prefix_sz + i]` applied to the whnf'd aux app's args, then the args beyond `prefix_sz + num_alts` re-applied, then a head-beta (`instantiate_rev` of consumable lambda binders) (:558-568). Otherwise `Stuck(aux_whnf)`. **Restore the lctx** (truncate to its pre-telescope length) on every exit path.
- `whnf_matcher(e)` (:522-534): when transparency is `Reducible | Instances | Implicit`, set `self.can_unfold_override = true` for the duration (restore after — this both routes `unfold_definition`'s gate through `can_unfold_at_matcher` and disables caching via `cacheable`); else plain `self.whnf(e)`. Thread the override into `unfold_definition`'s gate: `if self.can_unfold_override { can_unfold_at_matcher(...) } else { can_unfold(...) }`.
- `can_unfold_at_matcher(name, status)` (:498-520): `can_unfold(transparency, status)` first; then the transcribed allowlist of root names (`OfNat.ofNat`, `NatCast.natCast`, `Zero.zero`, `One.one`, `decEq`, `Nat.decEq`, `Char.ofNat`, `Char.ofNatAux`, `String.decEq`, `List.hasDecEq`, `Fin.ofNat`, `UInt8/16/32/64.ofNat`, `UInt8/16/32/64.decEq`, `HMod.hMod`, `Mod.mod`) — intern once, compare ids. The `hasMatchPatternAttribute` arm (:504-505) is a **seam** returning false (doc: the match-pattern attribute extension is undecoded; revisit when a corpus divergence implicates it — Mathlib-scale exposure arrives with the nightly in plan 4).
- `get_stuck_mvar(e)` (:322-383): transcribe the head-dispatch (mvar → itself; app of rec/matcher → recurse into the whnf'd major/discriminant; proj → recurse; else none). Needed by Task 7's smart-unfolding stuck path.

- [ ] **Step 3: Run tests, lint, kernel check, commit**

```bash
git add crates/leanr_meta
git commit -m "feat(meta): matcher reduction

reduceMatcher? transcribed (WHNF.lean:536-575) over the decoded matcher
table: saturation check against numParams + 1 + numDiscrs + numAlts,
bounded forall-telescope over the aux application's type, alternative
selection by stuck-head identity, and the reducible-transparency
channel (whnfMatcher + canUnfoldAtMatcher + eager dite unfolding,
:470-534) modelled as an explicit override predicate that also disables
caching, exactly the oracle's useWHNFCache escape.

Per-alternative arity is derived from altInfos + discrInfos
(MatcherInfo.altNumParams, MatcherInfo.lean:106) rather than stored.
The hasMatchPatternAttribute arm is a named seam returning false until
that extension is decoded."
```

---

### Task 7: Smart unfolding, full `unfold_definition`, the top loop completed

**Files:**
- Modify: `crates/leanr_meta/src/whnf.rs`

**Interfaces:**
- Consumes: Tasks 1-6; `Node::MData { data: KVMapId, .. }` + `Store::kvmap_at`/`to_kvmap` for annotations.
- Produces: `unfold_definition` in its final oracle shape; `MetaCtx::smart_unfolding_reduce(&mut self, e) -> Result<Option<ExprId>, MetaError>`.

**Background (oracle: WHNF.lean:747-775 `smartUnfoldingReduce?`, :871-957 `unfoldDefinition?`, :45-75 the `_sunfold` name convention and annotations).** `mkSmartUnfoldingNameFor n = n ++ "_sunfold"` (:50-51) — a name-convention env lookup, no extension. Annotations: `mkAnnotation kind e` = `MData` whose kvmap has the single key `kind := true` (Expr.lean:2090-2100); the two kinds are `` `sunfoldMatch `` and `` `sunfoldMatchAlt ``.

- [ ] **Step 1: Write the failing test**

`Matcher.lean` must gain a structurally recursive definition so the oracle emits a `_sunfold` auxiliary. Append to `tests/fixtures/Matcher.lean`:

```lean
-- Structural recursion => the equation compiler emits N.count._sunfold
-- with sunfoldMatch/sunfoldMatchAlt markers (WHNF.lean:718-745), which
-- task 7's smart unfolding consumes.
def count (n : N) : N :=
  match n with
  | .zero => .zero
  | .succ m => .succ (count m)
```

Re-run `mise run fixtures:regen`; verify with the probe-free decode test that a constant named `count._sunfold` now exists in `ModuleData.const_names` (extend `matcher_entries_decode` or add a one-line test in `module_data.rs`). Then in `whnf.rs` tests:

```rust
    /// count (N.succ N.zero) unfolds via the _sunfold auxiliary and
    /// reduces to N.succ (count N.zero) -> ... a ctor-headed result.
    #[test]
    fn smart_unfolding_reduces_structural_recursion() { /* whnf at Default; expect N.succ head */ }

    /// count applied to a stuck fvar does NOT unfold (the sunfold
    /// match is stuck, so unfoldDefinition? must return none rather
    /// than exposing brecOn internals).
    #[test]
    fn smart_unfolding_blocks_on_stuck_argument() { /* whnf leaves `count x` intact */ }
```

- [ ] **Step 2: Implement**

- Annotation reading: `fn annotation(&self, e: ExprId, kind: NameId) -> Option<ExprId>` — `Node::MData { data, expr }` whose kvmap is exactly `[(kind, true)]` (reconcile the `KVMap` value shape against `leanr_kernel::KVMap`). Intern `sunfoldMatch`/`sunfoldMatchAlt` names in `MetaCtx::new`.
- `smart_unfolding_reduce` (:747-775): the `go` traversal over let/lam/app/proj/mdata (each rebuilding via store constructors, `None` propagating), with `go_match`: `reduce_matcher` on the annotated match; `Reduced` → if the result carries the `sunfoldMatchAlt` annotation, return that alt, else recurse; `Stuck` → `get_stuck_mvar` and — **seam** — `synth_pending` returns false this plan (doc cite :769-772, plan 4), so stuck is `None`. The lam arm's `lambdaTelescope` = mint fvars per binder, recurse on the body, re-abstract (`abstract_fvars` + rebuild binders); restore lctx.
- `unfold_definition` final shape (:871-957):
  - App case: head const lookup **through the transparency gate** (`getUnfoldableConst` shape, as in Task 5) with the `can_unfold_override` channel from Task 6; if `self.smart_unfolding` and env contains `mkSmartUnfoldingNameFor(name)` (build the name id: `name_str(Some(parent), "_sunfold")` — reconcile against the bank's name-building API; note the oracle suffixes the *last* component: `Name.mkStr declName "_sunfold"` appends a component — match that exactly: `f._sunfold` is `f ++ "_sunfold"` as a **new component**): `deltaBetaDefinition` the aux (preserving mdata — our beta must not strip `MData` between binders; verify `instantiate_rev` keeps mdata nodes intact, it substitutes under them), then `smart_unfolding_reduce`; on `Some(r)`: the structural-rec-arg post-check (:885-905) — `get_structural_rec_arg_pos` is a **seam returning `None`** this plan, and the oracle's own `| recordUnfold; return some r` branch on `none` means our seam takes a real oracle branch (the Binport fallback), documented divergence only for constants where the oracle *has* the position; corpus keeps clear (the fixture's `count` recurses on its only argument — confirm during regen that the oracle still unfolds it; if the oracle records a rec-arg position and diverges, the acceptance diff of Task 9 will say so precisely, and the fix is corpus selection, not code).
  - On no `_sunfold`: if the head is a matcher (`matcher_of`), return `None` (whnfCore reduces those, :941-944); else plain delta (Task 5's body).
  - `Const` (bare) case (:945-957): if a `_sunfold` exists for it, return `None`; else delta.
  - The `unfoldProjInstWhenInstances?` fail-path (:874, :824-848) is a **seam returning `None`** (projection-fn-info extension undecoded; lands in plan 4 with the instance data — cite it).

- [ ] **Step 3: Run everything, lint, kernel check, commit**

`cargo test -p leanr_meta && cargo test -p leanr_olean && mise run lint`; kernel untouched.

```bash
git add crates/leanr_meta tests/fixtures/Matcher.lean tests/fixtures/Matcher.olean
git commit -m "feat(meta): smart unfolding and the full unfoldDefinition

The _sunfold channel transcribed from WHNF.lean:747-775 and :871-957:
equation-compiler definitions unfold through their auxiliary, the
sunfoldMatch/sunfoldMatchAlt annotations steer the traversal, and a
stuck inner match vetoes the unfold instead of exposing brecOn
internals. Annotations are read structurally from MData kvmaps
(Expr.lean:2090-2100).

Named seams: synthPending (plan 4), structural-rec-arg position
(undecoded; our None takes the oracle's own Binport fallback branch),
instance-projection unfolding at .instances (plan 4). Omitting smart
unfolding entirely would change what unfolds silently — the spec calls
it out as a named channel for exactly that reason."
```

---

### Task 8: The oracle corpus and dumper

**Files:**
- Create: `tests/fixtures/meta/Meta0.lean`
- Create: `tests/fixtures/meta/dump_defeq.lean`
- Modify: `mise.toml` (`fixtures:regen`)

**Interfaces:**
- Consumes: the pinned toolchain (regen-time only).
- Produces: committed `tests/fixtures/meta/Meta0.olean` and `tests/fixtures/meta/meta-queries.jsonl` — one JSON object per line:
  - `{"id":"<const>/<kind>/<n>","q":"whnf"|"infer","tr":"none|reducible|instances|implicit|default|all","in":<E>,"out":<E>}`
  - Expr encoding `<E>` (canonical, both sides emit/consume the same): `{"k":"sort","u":<L>}`, `{"k":"const","n":"N.succ","us":[<L>...]}`, `{"k":"app","f":<E>,"a":<E>}`, `{"k":"lam","bi":"d|i|s|c","t":<E>,"b":<E>}`, `{"k":"pi","bi":...,"t":<E>,"b":<E>}`, `{"k":"let","t":<E>,"v":<E>,"b":<E>,"nd":true|false}`, `{"k":"bvar","i":N}`, `{"k":"lit","n":"<decimal>"}`, `{"k":"str","v":"..."}`, `{"k":"proj","s":"S","i":N,"e":<E>}`, `{"k":"mvar","i":N}`, `{"k":"fvar","i":N}`; levels `<L>`: `{"k":"zero"}`, `{"k":"succ","u":<L>}`, `{"k":"max","a":<L>,"b":<L>}`, `{"k":"imax","a":<L>,"b":<L>}`, `{"k":"param","n":"u"}`.
  - Canonicalization rules (spec § Query records): binder names are **erased** (`bi` keeps only the binder kind); `MData` is **erased** on both sides; mvars/fvars are numbered in first-occurrence order within a query; literals print as decimal strings (no i64 truncation); query ids are `constant/kind/index`, never a global counter.

- [ ] **Step 1: Write the corpus fixture**

`tests/fixtures/meta/Meta0.lean` — prelude-mode, import-free, one section per reduction rule, each section commented with the rule it exists to exercise:

```lean
-- M4a plan-2 tier-1 corpus (spec § Acceptance harness). prelude-mode
-- and import-free (the Prelude0 pattern) so BOTH sides of the
-- differential gate see exactly this module and nothing else: the
-- oracle imports only Meta0; leanr replays only Meta0.olean. One
-- section per reduction rule; grow deliberately, like the parse
-- pass-list.
prelude

-- beta / plain delta at each status
inductive N where
  | zero : N
  | succ : N → N

@[reducible] def redId (n : N) : N := n
def semiDouble (n : N) : N := N.succ (N.succ n)
@[irreducible] def irredId (n : N) : N := n

-- zeta
def letChain : N := let a := N.zero; let b := N.succ a; N.succ b

-- proj (a structure-like single-ctor inductive)
structure P where
  fst : N
  snd : N

def mkP : P := ⟨N.zero, N.succ N.zero⟩
def useFst (p : P) : N := p.fst

-- iota (recursor application; noncomputable — recursors aren't compiled)
noncomputable def add (a b : N) : N :=
  N.rec a (fun _ ih => N.succ ih) b

-- matcher + smart unfolding (structural recursion)
def count (n : N) : N :=
  match n with
  | .zero => .zero
  | .succ m => .succ (count m)
```

If `structure`/anonymous-ctor syntax is rejected in prelude mode, fall back to an explicit single-ctor `inductive P | mk (fst snd : N)` with explicit `P.mk` / `P.fst` projections — record the substitution in the comment. Do not add imports.

- [ ] **Step 2: Verify it compiles, then write the dumper**

`cd tests/fixtures/meta && lean Meta0.lean -o Meta0.olean && echo OK`

Create `tests/fixtures/meta/dump_defeq.lean`. Shape (following `dump_decls.lean`'s style — a `main` run via `lean --run`; consult that file for the import/`IO` boilerplate the toolchain version wants):

```lean
/- Emits the tier-1 meta query corpus as canonical JSONL (plan-2 spec
§ Acceptance harness). Runs with LEAN_PATH set to this directory so
`import Meta0` resolves to the committed fixture and NOTHING else —
Meta0 is prelude-mode, so the oracle environment here is exactly the
environment leanr replays. Query ids are constant/kind/index (stable
across regen); mvars/fvars are numbered per query in first-occurrence
order; binder names and mdata are erased (canonicalization rules in
the plan header).
-/
import Meta0
open Lean Lean.Meta

-- <expr/level → Json encoders implementing the canonical scheme,
--  ~60 lines: a StateT (HashMap Name Nat) walk for mvar/fvar
--  numbering; erase binder names; skip mdata; levels per scheme>

def transparencies : List (String × TransparencyMode) :=
  [("reducible", .reducible), ("default", .default), ("all", .all)]

-- Handwritten whnf queries: (constant, index, expr-builder). Each
-- builder references Meta0 constants by name. The list is the corpus'
-- growth point — extend it alongside Meta0.lean.
def one : Expr := mkApp (mkConst `N.succ) (mkConst `N.zero)
def whnfQueries : List (Name × Nat × Expr) :=
  [ (`redId,   0, mkApp (mkConst `redId) one)
  , (`semiDouble, 0, mkApp (mkConst `semiDouble) (mkConst `N.zero))
  , (`irredId, 0, mkApp (mkConst `irredId) one)
  , (`letChain, 0, mkConst `letChain)
  , (`useFst,  0, mkApp (mkConst `useFst) (mkConst `mkP))
  , (`add,     0, mkApp (mkApp (mkConst `add) one) one)
  , (`count,   0, mkApp (mkConst `count) one)
  , (`count,   1, mkApp (mkConst `count) (mkConst `N.zero))
  ]

def emit (id : String) (q : String) (tr : String) (inE outE : Lean.Json) : IO Unit :=
  IO.println <| Lean.Json.compress <| Lean.Json.mkObj
    [("id", id), ("q", q), ("tr", tr), ("in", inE), ("out", outE)]

def main : IO Unit := do
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Meta0 }] {} (trustLevel := 0)
  let coreCtx : Core.Context := { fileName := "<dump_defeq>", fileMap := default }
  let go : MetaM Unit := do
    for (name, i, e) in whnfQueries do
      for (trName, tr) in transparencies do
        let r ← withTransparency tr <| whnf e
        emit s!"{name}/whnf{i}/{trName}" "whnf" trName (encodeExpr e) (encodeExpr r)
    for (cname, cinfo) in (← getEnv).constants.toList do
      if let some v := cinfo.value? then
        let t ← inferType v
        emit s!"{cname}/infer/0" "infer" "default" (encodeExpr v) (encodeExpr t)
  discard <| (go.run' {} {}).toIO coreCtx { env }
```

(The `Core.Context` / `MetaM.run'` / `toIO` plumbing above is the usual v4.33 shape but the exact record fields drift between releases — reconcile against what `lean --run` accepts, using `dump_decls.lean` and `dump_syntax_elab.lean` as the in-repo precedents for working boilerplate. `encodeExpr` is the canonical-scheme encoder from this file's header; the constant loop must filter to constants whose module is `Meta0` — imported-prelude internals do not exist here since `Meta0` is import-free, but elaborator-generated auxiliaries (`count._sunfold`, matchers, `recOn`s) DO appear and are wanted: they are real reduction-relevant constants. Skip any constant whose value fails to infer cleanly rather than aborting the dump — log it to stderr so the regen run shows what was skipped; a silent drop would shrink the corpus invisibly.)

The elided encoder and `main` bodies are ordinary metaprogramming against the pinned toolchain — write them fully in the file (the dumper is oracle-side code, so its "specification" is the JSONL contract above; iterate until `lean --run` produces valid JSONL, checking a line by eye). If `whnf` at `.reducible` leaves a query unchanged (e.g. `semiDouble` does not unfold there), that is a **correct record** — the corpus needs negative unfolding evidence too.

- [ ] **Step 3: Wire regen and commit the outputs**

Add to `mise.toml` `fixtures:regen` after the `Matcher` line:

```toml
  # M4a plan 2: tier-1 meta corpus. Meta0 is prelude-mode/import-free;
  # the dumper imports ONLY Meta0 (LEAN_PATH=$PWD) so the oracle env
  # equals the env leanr replays from the committed .olean.
  "sh -c 'cd tests/fixtures/meta && lean Meta0.lean -o Meta0.olean'",
  "sh -c 'cd tests/fixtures/meta && LEAN_PATH=$PWD lean --run dump_defeq.lean > meta-queries.jsonl'",
```

Run `mise run fixtures:regen`; inspect `tests/fixtures/meta/meta-queries.jsonl` by eye (ids stable? every record has `in`/`out`? no gensym'd `_uniq` names anywhere?).

```bash
git add tests/fixtures/meta mise.toml
git commit -m "feat(fixtures): tier-1 meta corpus and dump_defeq dumper

One prelude-mode module per the Prelude0 pattern, so both sides of the
differential gate see the identical environment: the oracle imports
only Meta0, leanr replays only Meta0.olean. Queries are handwritten
per reduction rule plus an infer_type record per value-carrying
constant, emitted as canonical JSONL: stable constant/kind/index ids,
first-occurrence mvar numbering, binder names and mdata erased —
verdict-only records were rejected in the parent spec because two
implementations can agree on every boolean while diverging in the
terms."
```

---

### Task 9: The acceptance test and `meta:fast`

**Files:**
- Create: `crates/leanr_meta/tests/oracle_fast.rs`
- Modify: `crates/leanr_meta/Cargo.toml` (dev-dependency `serde_json`)
- Modify: `mise.toml` (new task `meta:fast`)

**Interfaces:**
- Consumes: everything above; `leanr_olean::ModuleData::parse`; `leanr_kernel::{replay, Environment, EnvView}`; committed `Meta0.olean` + `meta-queries.jsonl`.
- Produces: `mise run meta:fast`; the same test also runs inside plain `cargo test`/`mise run test`, so CI gates it with no new CI wiring.

- [ ] **Step 1: Write the failing test**

`crates/leanr_meta/tests/oracle_fast.rs`:

```rust
//! Tier-1 differential gate (plan-2 spec § The gate): every committed
//! query must agree with the oracle byte-for-byte after
//! canonicalization. Hermetic — the committed .olean and .jsonl are
//! the entire input; CI never installs Lean (docs/ORACLE.md).
//!
//! This is a REGRESSION gate: "nothing that used to agree now
//! disagrees." Discovery at Mathlib scale is plan 4's nightly.

use std::collections::HashMap;
use std::path::PathBuf;

use leanr_kernel::bank::NameId;
use leanr_kernel::{ConstantInfo, Environment, EnvView};
use leanr_meta::{Config, MetaCtx, TransparencyMode};
use leanr_olean::ModuleData;

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/meta").join(name)
}

#[test]
fn oracle_fast_gate() {
    let bytes = std::fs::read(fixture("Meta0.olean")).expect("committed fixture");
    let mut env = Environment::default();
    let md = ModuleData::parse(&bytes, env.store_mut()).expect("decode");
    assert!(md.imports.is_empty(), "Meta0 must stay import-free");
    let constants: HashMap<NameId, ConstantInfo> =
        md.constants.iter().cloned().map(|c| (c.name(), c)).collect();
    leanr_kernel::replay(&mut env, constants).expect("replay");

    let queries = std::fs::read_to_string(fixture("meta-queries.jsonl")).expect("committed queries");
    let mut failures = Vec::new();
    for line in queries.lines().filter(|l| !l.trim().is_empty()) {
        let q: serde_json::Value = serde_json::from_str(line).expect("committed JSONL is valid");
        // decode_expr / encode_expr / transparency_of: helpers below,
        // implementing the canonical scheme from the task-8 header.
        // A fresh MetaCtx per query: queries must be independent
        // (caching across queries would make failures order-dependent).
        // <build EnvView per schedule.rs:324; MetaCtx::new with
        //  md.reducibility / md.matchers; set transparency; intern the
        //  "in" expr; run whnf or infer; encode; compare to "out">
        // on mismatch: failures.push(format!("{id}: leanr={got} oracle={want}"));
    }
    assert!(failures.is_empty(), "{} divergences:\n{}", failures.len(), failures.join("\n"));
}
```

The helper trio to write in the same file (fully — they are this task's real work, ~200 lines):
- `decode_expr(store, &serde_json::Value) -> ExprId` — recursive descent over the canonical scheme, interning through the store constructors; `mvar`/`fvar` indices intern names `?0`, `?1`… / `#f0`… deterministically; unknown `k` panics *in the test* (committed fixture, not untrusted input — the never-panic obligation is for `.olean` bytes, and a malformed committed fixture SHOULD fail loudly).
- `encode_expr(store, ExprId) -> serde_json::Value` — inverse walk with first-occurrence mvar/fvar numbering, binder-name and mdata erasure per the canonical rules.
- `transparency_of(&str) -> TransparencyMode`.

Add to `crates/leanr_meta/Cargo.toml`:

```toml
[dev-dependencies]
serde_json = "<the version already pinned elsewhere in the workspace — grep and match>"
```

Run: `cargo test -p leanr_meta --test oracle_fast` — expect FAIL (helpers unimplemented / first real divergences).

- [ ] **Step 2: Implement the helpers and burn down divergences**

Write the three helpers, then run the gate. **Every divergence is a finding**: either a transcription bug (fix the Rust, citing the oracle line in the fix commit) or a corpus query leaning on a named seam (move the query out of `whnfQueries` / regenerate, and record in the seam's doc comment that the corpus excludes it — never weaken the comparison). Iterate until zero divergences.

- [ ] **Step 3: The mise task**

Add to `mise.toml` after `parse:mathlib:fast`:

```toml
[tasks."meta:fast"]
description = "Tier-1 meta differential gate: every committed whnf/infer query agrees with the oracle. Hermetic, seconds; runs in the dev loop (also runs inside plain `mise run test`)."
run = ["cargo test --release -p leanr_meta --test oracle_fast"]
```

Run: `mise run meta:fast` — green, in seconds.

- [ ] **Step 4: Full gate and final commit**

Run: `mise run ci` — all green. `git status --short crates/leanr_kernel` — empty.

```bash
git add crates/leanr_meta mise.toml
git commit -m "feat(meta): the tier-1 oracle gate, wired as meta:fast

Decodes the committed Meta0 fixture, replays it through the kernel,
and runs every committed query through MetaCtx, comparing structurally
canonicalized terms against the oracle's recorded answers — not
verdicts, terms (parent spec: two implementations can agree on every
boolean while diverging in the assignments).

A fresh MetaCtx per query so failures are order-independent. Hermetic:
no Lean, no corpus walk, seconds — the meta analogue of
parse:mathlib:fast, and it also runs inside plain `mise run test`, so
CI gates it with no new workflow.

serde_json enters as a dev-dependency only (parsing committed oracle
fixtures in tests; already in the workspace tree)."
```

---

## What this plan does NOT build (the named-seam ledger)

Recorded so plan 3/4 authors — and anyone chasing a nightly divergence — can grep one list. Every entry exists in code as a documented function:

| seam | oracle | lands |
|---|---|---|
| delayed mvar assignments in whnf | WHNF.lean:585-607 | plan 3 (with delayed assignment in `MetavarContext`) |
| `to_ctor_when_k` compares structurally, not by defeq | WHNF.lean:150-170 | plan 3 (`is_def_eq`) |
| nat-offset major cleanup (`cleanupNatOffsetMajor`) | WHNF.lean:218-226 | plan 3 (`offsetCnstrs`) |
| `synth_pending` on stuck smart-unfold matches | WHNF.lean:769-772 | plan 4 (synthesis) |
| instance-projection unfolding at `.instances` | WHNF.lean:824-848 | plan 4 (projection-fn-info + instance data) |
| `hasMatchPatternAttribute` arm of `can_unfold_at_matcher` | WHNF.lean:504-505 | when that attribute extension is decoded |
| structural-rec-arg position check | WHNF.lean:885-905 | when that extension is decoded (our `None` takes the oracle's own fallback branch) |
| aux-recursor (`casesOn` etc.) unfolding inside `whnf_core` | WHNF.lean:697-701 | when aux-recursor identification is decoded |
| `reduce_native` | WHNF.lean:1008-1018 | later M4 slice (VM) |
| string-literal `toCtorIfLit` | WHNF.lean:27-28 | when a corpus query needs it |
| scoped reducibility entries (Global-only map) | ScopedEnvExtension semantics | when a corpus divergence implicates one |
| zetaDelta implementation-detail / tracking channels | WHNF.lean:399-407 | M4b (elaborator context) |

Also not here: `is_def_eq` beyond plan 1's stubs, the occurs check, the approximation flags in action, unification hints (plan 3); instance/default-instance decode, discrimination trees, tabled synthesis, `meta:nightly` (plan 4).

## Known risk, restated from the spec

The matcher raw shape (Task 1) and the prelude-mode elaboration surface (Tasks 1, 8) are pinned empirically, not assumed; both tasks front-load a verify step so a surprise is bounded to that task. The tier-1 corpus only catches divergence it contains — Mathlib-scale discovery is plan 4's nightly, and the seam ledger above is exactly the list of places it should aim at.
