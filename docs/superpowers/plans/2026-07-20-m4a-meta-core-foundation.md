# M4a Foundation (plan 1 of 4) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Stand up the `leanr_meta` crate with its transparency model, defeq configuration and cache key, and metavariable context — plus the `leanr_olean` reducibility-extension decode those depend on.

**Architecture:** `leanr_meta` is a new crate implementing the elaborator-level `MetaM` core, independent of `leanr_kernel`'s own `whnf`/`is_def_eq` (see the spec's § Scope decisions for why the kernel is not generalized). This plan builds only the foundation layer: no reduction, no unification, no synthesis. Those land in plans 2–4.

**Tech Stack:** Rust 2021, `leanr_kernel` (term bank, `Expr`, `Environment`), `leanr_olean` (decoded `.olean` extension data). No new third-party dependencies.

**Spec:** [docs/superpowers/specs/2026-07-20-m4a-meta-core-design.md](../specs/2026-07-20-m4a-meta-core-design.md)

## Global Constraints

- **Oracle pin:** `leanprover/lean4:v4.33.0-rc1`, Mathlib `c732b96d05efdb1fb84511dfdc24a8f70005ae99`. Never bump outside a milestone boundary.
- **Kernel TCB:** `leanr_kernel` must not be modified by this plan, and must keep depending on no other workspace crate.
- **Untrusted input:** `.olean` bytes are untrusted. Every new decode path must return `OleanError`, never panic, on arbitrary bytes (`docs/THREAT_MODEL.md`).
- **Dependencies:** app deps via cargo only; every new third-party dependency needs justification. This plan adds none.
- **Workflows:** use named mise tasks. CI runs `mise run ci`.
- **Failure semantics:** every `leanr_meta` failure is incompleteness, never unsoundness.
- **Default reducibility status** for a constant with no extension entry is `Semireducible`.

## Prerequisites (already done — verify, do not redo)

- `lean-toolchain` and `mathlib-pin` are at the versions above; fixtures regenerated; `mise run test`, `lint`, `lint:deps` green.
- `.mathlib` is re-fetched at `c732b96d`, toolchain-guard verified, and `mise run parse:mathlib:fast` reports 23/23 green, 0 regressions.

Verify with:

```bash
cat lean-toolchain && sed -n '3p' mathlib-pin && git -C .mathlib rev-parse HEAD
```

Expected: `leanprover/lean4:v4.33.0-rc1`, then the same SHA twice.

---

### Task 1: `leanr_meta` crate skeleton

**Files:**
- Create: `crates/leanr_meta/Cargo.toml`
- Create: `crates/leanr_meta/src/lib.rs`
- Create: `crates/leanr_meta/src/error.rs`
- Modify: `Cargo.toml:3` (workspace members)

**Interfaces:**
- Consumes: nothing.
- Produces: crate `leanr_meta`; `leanr_meta::MetaError` with variants `Kernel(leanr_kernel::KernelError)`, `Olean(String)`, `StepBudgetExhausted`, `DepthBudgetExhausted`.

- [ ] **Step 1: Add the crate to the workspace**

Edit `Cargo.toml`, replacing the `members` line so `leanr_meta` is included:

```toml
members = ["crates/leanr_kernel", "crates/leanr_check", "crates/leanr_cli", "crates/leanr_query", "crates/leanr_syntax", "crates/leanr_olean", "crates/leanr_grammar", "crates/leanr_build", "crates/leanr_fmt", "crates/leanr_meta"]
```

- [ ] **Step 2: Create the crate manifest**

Create `crates/leanr_meta/Cargo.toml`:

```toml
[package]
name = "leanr_meta"
version.workspace = true
edition.workspace = true
license.workspace = true
repository.workspace = true

[dependencies]
leanr_kernel = { path = "../leanr_kernel" }
leanr_olean = { path = "../leanr_olean" }
stacker = "0.1"
```

`stacker` matches `leanr_kernel`'s existing pin and is needed because Meta-level traversal recurses proportionally to term depth (spec § Error handling). It is not a new workspace dependency — the kernel already uses the same version.

- [ ] **Step 3: Write the failing test**

Create `crates/leanr_meta/src/error.rs`:

```rust
//! Every failure `leanr_meta` can report.
//!
//! All of them are INCOMPLETENESS, never unsoundness: the worst case is
//! that elaboration which should have succeeded does not, because the
//! kernel independently re-checks whatever this crate produces (spec
//! § Error handling & edge cases). Same posture as
//! `KernelError::BankExhausted`.

/// A Meta-level failure.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MetaError {
    /// A kernel-level operation failed (bank exhaustion, recursion cap).
    Kernel(leanr_kernel::KernelError),
    /// Decoded `.olean` data was not shaped as this crate expects.
    Olean(String),
    /// A metavariable-context invariant was violated: assigning an
    /// undeclared mvar, or reassigning an assigned one. Not a negative
    /// verdict — a caller bug.
    MVar(String),
    /// The deterministic step budget was exhausted (spec § Determinism).
    /// NOT a negative verdict — the question was never answered.
    StepBudgetExhausted,
    /// The synthesis-reentrancy depth budget was exhausted.
    DepthBudgetExhausted,
}

impl From<leanr_kernel::KernelError> for MetaError {
    fn from(e: leanr_kernel::KernelError) -> MetaError {
        MetaError::Kernel(e)
    }
}

#[cfg(test)]
mod tests {
    use super::MetaError;

    #[test]
    fn kernel_errors_convert() {
        let e: MetaError = leanr_kernel::KernelError::BankExhausted.into();
        assert_eq!(e, MetaError::Kernel(leanr_kernel::KernelError::BankExhausted));
    }

    // A budget exhaustion must be distinguishable from a negative
    // verdict. This is a type-level guarantee (a distinct variant), but
    // the test pins the intent so a later refactor to `bool` fails here.
    #[test]
    fn budget_exhaustion_is_its_own_variant() {
        assert_ne!(MetaError::StepBudgetExhausted, MetaError::DepthBudgetExhausted);
    }
}
```

Create `crates/leanr_meta/src/lib.rs`:

```rust
//! The elaborator-level `MetaM` core: reduction, definitional equality,
//! and typeclass synthesis over terms containing metavariables.
//!
//! This is NOT `leanr_kernel`'s `whnf`/`is_def_eq`. The kernel's is a
//! total question about closed, mvar-free terms and is an INDEPENDENT
//! check on what this crate produces; no reduction logic is shared in
//! either direction, even where the rules coincide. See the spec's
//! § Scope decisions for why the kernel is not generalized over a
//! trait.
//!
//! spec: docs/superpowers/specs/2026-07-20-m4a-meta-core-design.md

mod error;

pub use error::MetaError;
```

- [ ] **Step 4: Run the tests to verify they fail**

Run: `cargo test -p leanr_meta`

Expected: FAIL — `error: failed to load manifest` or `no targets` before step 2/3 files exist. If you created all files first, this step instead confirms compilation; re-order so you see red at least once.

- [ ] **Step 5: Run the tests to verify they pass**

Run: `cargo test -p leanr_meta`

Expected: PASS, `2 passed`.

- [ ] **Step 6: Verify lint is clean**

Run: `mise run lint`

Expected: no warnings; `cargo fmt --all --check` and `clippy -D warnings` both pass.

- [ ] **Step 7: Commit**

```bash
git add Cargo.toml Cargo.lock crates/leanr_meta
git commit -m "feat(meta): leanr_meta crate skeleton and MetaError

The elaborator-level MetaM core, independent of leanr_kernel's own
whnf/is_def_eq. Every MetaError variant is incompleteness, never
unsoundness, since the kernel re-checks whatever this crate produces.
Budget exhaustion is its own variant rather than a false verdict: 'the
question was not answered' and 'the answer is no' must not collapse."
```

---

### Task 2: Decode the reducibility environment extensions

**Files:**
- Create: `tests/fixtures/Reducibility.lean`
- Modify: `mise.toml` (`fixtures:regen` task, after the `ModPriv` line)
- Modify: `crates/leanr_olean/src/module_data.rs` (add types + `ModuleData` field + part merge)
- Modify: `crates/leanr_olean/src/interp_id.rs` (decode functions + `module_data` loop)
- Modify: `crates/leanr_olean/src/lib.rs:216` (re-export)

**Interfaces:**
- Consumes: `leanr_olean`'s existing `ctor`/`array`/`bad` helpers from `interp.rs`, `EntryScope`, `NameId`.
- Produces:
  - `leanr_olean::ReducibilityStatus` — `Reducible | Semireducible | Irreducible | ImplicitReducible | InstanceReducible`
  - `leanr_olean::ReducibilityEntry { scope: EntryScope, name: NameId, status: ReducibilityStatus }`
  - `ModuleData::reducibility: Vec<ReducibilityEntry>`

**Background (verified against `leanprover/lean4:v4.33.0-rc1`, `src/Lean/ReducibilityAttrs.lean`):**

Reducibility is **two** extensions, not one and not five:

| extension name | registration | olean entry type |
|---|---|---|
| `reducibilityCore` (line 53) | `registerPersistentEnvExtension` | `Name × ReducibilityStatus`, **no** `Entry` wrapper, **sorted ascending by `Name.quickLt`** |
| `reducibilityExtra` (line 73) | `registerSimpleScopedEnvExtension` | `ScopedEnvExtension.Entry (Name × ReducibilityStatus)` — usually empty |

Both names are un-namespaced backtick literals (`reducibilityCore`, not `Lean.reducibilityCore`).

`ReducibilityStatus` (`ReducibilityAttrs.lean:40-42`) is all-nullary, so its declaration order **is** its ctor tag order: `reducible`=0, `semireducible`=1, `irreducible`=2, `implicitReducible`=3, `instanceReducible`=4. The in-source comment states the last two were appended out of semantic order for bootstrapping — so tag order is **not** unfolding order. Task 3 depends on that distinction.

`ScopedEnvExtension.Entry`: tag 0 = `global(payload)` 1 field; tag 1 = `scoped(ns, payload)` 2 fields. There is no `local` constructor — local entries are never serialized.

- [ ] **Step 1: Create the fixture**

Create `tests/fixtures/Reducibility.lean`:

```lean
-- Fixture for the `reducibilityCore` / `reducibilityExtra` environment
-- extension decode (M4a plan 1, task 2). Each attribute below is one
-- of the five that funnel into `setReducibilityStatusCore`
-- (ReducibilityAttrs.lean:90); `plainDef` carries no attribute and must
-- therefore be ABSENT from the extension array, exercising the
-- `.semireducible` default rather than an explicit entry.
@[reducible] def redDef : Nat := 1
@[irreducible] def irredDef : Nat := 2
@[semireducible] def semiredDef : Nat := 3
@[instance_reducible] def instRedDef : Nat := 4
@[implicit_reducible] def implRedDef : Nat := 5
def plainDef : Nat := 6
```

- [ ] **Step 2: Verify the fixture compiles against the oracle**

Run:

```bash
cd tests/fixtures && lean Reducibility.lean -o /tmp/Reducibility.olean && echo OK
```

Expected: `OK`. If any attribute is rejected (e.g. `@[instance_reducible]` not applicable to a plain `def`), drop that line and record which one in the fixture's comment — do not invent a different attribute.

- [ ] **Step 3: Wire the fixture into regen**

Edit `mise.toml`, adding this line to the `fixtures:regen` `run` array immediately after the `ModPriv` `rm -f` line:

```toml
  # M4a: reducibility-attribute fixture for the reducibilityCore /
  # reducibilityExtra extension decode. Built from inside tests/fixtures
  # for the same reason ModPriv is (module name must not depend on the
  # invocation cwd).
  "sh -c 'cd tests/fixtures && lean Reducibility.lean -o Reducibility.olean'",
```

Then run: `mise run fixtures:regen`

Expected: finishes clean; `git status --short` shows `tests/fixtures/Reducibility.olean` as new.

- [ ] **Step 4: Empirically pin the raw shape**

The physical scalar-vs-boxed encoding of a nullary ctor in a *polymorphic* field position is not derivable from the Lean source — `Prod`'s fields are polymorphic, so `ReducibilityStatus` should arrive as a boxed immediate (`RawValue::Scalar(tag)`) rather than in the ctor's `scalars` area. That is the opposite of `CatBehavior` in `parser_entry`, which is monomorphic and therefore unboxed.

This codebase's established practice is to pin such shapes empirically before writing the decoder (see the `parser_entry` doc comment's "Empirical pin" note). Do that now.

Add this temporary probe to `crates/leanr_olean/src/interp_id.rs`, inside `module_data`, immediately after `let ext_name = self.name(&pf[0])?;`:

```rust
        // TEMPORARY probe — remove before committing.
        {
            let n = self.st.to_name(None, ext_name).to_string();
            if n == "reducibilityCore" || n == "reducibilityExtra" {
                for e in array(&pf[1])? {
                    eprintln!("PROBE {n}: {e:?}");
                }
            }
        }
```

Add a temporary test in `crates/leanr_olean/src/module_data.rs`'s `mod tests`:

```rust
    #[test]
    fn probe_reducibility_shape() {
        let bytes = fixture("Reducibility.olean");
        let mut env = Environment::default();
        let _ = ModuleData::parse(&bytes, env.store_mut()).expect("decode");
    }
```

Run: `cargo test -p leanr_olean --lib probe_reducibility_shape -- --nocapture 2>&1 | grep PROBE | head -20`

Expected: lines showing `Ctor { tag: 0, fields: 2, .. }` pairs whose second field prints as `RawValue::Scalar(n)` with `n` in `0..=4`. **Record the actual shape in a note** — if the status instead appears in `scalars`, adapt step 6's `reducibility_status` to read `scalars.first()` like `parser_entry` does, and say so in its doc comment.

- [ ] **Step 5: Remove the probe**

Delete both temporary blocks added in step 4. Re-run `cargo test -p leanr_olean --lib` to confirm the crate still builds.

- [ ] **Step 6: Write the failing test**

Add to `crates/leanr_olean/src/module_data.rs`, inside `mod tests`:

```rust
    /// The reducibility extensions decode, and a constant with no
    /// attribute is ABSENT (its status is the `.semireducible` default,
    /// not a stored entry).
    #[test]
    fn reducibility_entries_decode() {
        use crate::{EntryScope, ReducibilityStatus};

        let bytes = fixture("Reducibility.olean");
        let mut env = Environment::default();
        let md = ModuleData::parse(&bytes, env.store_mut()).expect("decode");

        let render = |env: &Environment, n: NameId| env.store().to_name(None, Some(n)).to_string();
        let got: Vec<(String, ReducibilityStatus)> = md
            .reducibility
            .iter()
            .map(|e| (render(&env, e.name), e.status))
            .collect();

        for (name, want) in [
            ("redDef", ReducibilityStatus::Reducible),
            ("irredDef", ReducibilityStatus::Irreducible),
            ("instRedDef", ReducibilityStatus::InstanceReducible),
            ("implRedDef", ReducibilityStatus::ImplicitReducible),
        ] {
            assert!(
                got.contains(&(name.to_string(), want)),
                "missing {name} => {want:?}; got {got:?}"
            );
        }

        assert!(
            !got.iter().any(|(n, _)| n == "plainDef"),
            "plainDef carries no attribute so it must not appear: {got:?}"
        );

        // reducibilityCore is unwrapped, so every entry from it is Global.
        assert!(md.reducibility.iter().all(|e| matches!(e.scope, EntryScope::Global)));
    }

    /// `reducibilityCore`'s array is sorted by `Name.quickLt` and
    /// `getReducibilityStatusCore` binary-searches it. We do not depend
    /// on the ordering, but a violation means the shape assumption is
    /// wrong, so assert the array is non-empty and every entry resolved.
    #[test]
    fn reducibility_entries_are_nonempty() {
        let bytes = fixture("Reducibility.olean");
        let mut env = Environment::default();
        let md = ModuleData::parse(&bytes, env.store_mut()).expect("decode");
        assert!(!md.reducibility.is_empty());
    }
```

- [ ] **Step 7: Run the test to verify it fails**

Run: `cargo test -p leanr_olean --lib reducibility`

Expected: FAIL to compile — `no field 'reducibility' on type 'ModuleData'` and `unresolved import crate::ReducibilityStatus`.

- [ ] **Step 8: Add the types and the `ModuleData` field**

In `crates/leanr_olean/src/module_data.rs`, add above `pub struct ModuleData`:

```rust
/// oracle: `ReducibilityStatus` (ReducibilityAttrs.lean:40-42). All
/// constructors are nullary, so DECLARATION order is ctor-tag order:
/// reducible=0, semireducible=1, irreducible=2, implicitReducible=3,
/// instanceReducible=4.
///
/// Tag order is deliberately NOT unfolding order — the in-source comment
/// records that the last two were appended out of semantic order for
/// bootstrapping. Consumers must not derive an ordering from this enum's
/// declaration order; see `leanr_meta::transparency`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReducibilityStatus {
    Reducible,
    Semireducible,
    Irreducible,
    ImplicitReducible,
    InstanceReducible,
}

/// One decoded reducibility-attribute entry, from either
/// `reducibilityCore` (always `Global`, unwrapped) or
/// `reducibilityExtra` (wrapped in `ScopedEnvExtension.Entry`).
///
/// A constant with no entry has status `Semireducible`
/// (`getReducibilityStatusCore`'s fallback, ReducibilityAttrs.lean:79-88).
#[derive(Debug, Clone)]
pub struct ReducibilityEntry {
    pub scope: EntryScope,
    pub name: NameId,
    pub status: ReducibilityStatus,
}
```

Add the field to `ModuleData`, after `parser_entries`:

```rust
    /// Typed decode of the `reducibilityCore` / `reducibilityExtra`
    /// extension entries (M4a). All other extension entries stay opaque
    /// (folded into `num_entries` only).
    pub reducibility: Vec<ReducibilityEntry>,
```

In `parse_parts`'s merge, alongside the existing `parser_entries` line, add:

```rust
            reducibility: std::mem::take(&mut base.reducibility),
```

- [ ] **Step 9: Add the decoder**

In `crates/leanr_olean/src/interp_id.rs`, add these two functions next to `scoped_parser_entry`:

```rust
    /// oracle: `ReducibilityStatus` (ReducibilityAttrs.lean:40-42).
    /// Arrives as a BOXED immediate, not in the ctor's scalar area:
    /// `Prod`'s fields are polymorphic, so a nullary ctor in that
    /// position is a `RawValue::Scalar(tag)`. (Contrast `parser_entry`'s
    /// `LeadingIdentBehavior`, which is a monomorphic field and so is
    /// unboxed into `scalars`.) Shape pinned empirically against
    /// Reducibility.olean.
    fn reducibility_status(r: &Raw) -> Result<crate::ReducibilityStatus, OleanError> {
        match &**r {
            RawValue::Scalar(0) => Ok(crate::ReducibilityStatus::Reducible),
            RawValue::Scalar(1) => Ok(crate::ReducibilityStatus::Semireducible),
            RawValue::Scalar(2) => Ok(crate::ReducibilityStatus::Irreducible),
            RawValue::Scalar(3) => Ok(crate::ReducibilityStatus::ImplicitReducible),
            RawValue::Scalar(4) => Ok(crate::ReducibilityStatus::InstanceReducible),
            _ => Err(bad("ReducibilityStatus")),
        }
    }

    /// `Name × ReducibilityStatus` — a bare 2-field `Prod` (tag 0).
    fn reducibility_pair(
        &mut self,
        r: &Raw,
    ) -> Result<(crate::NameId, crate::ReducibilityStatus), OleanError> {
        let (f, _) = ctor(r, 0, 2, "Name × ReducibilityStatus")?;
        Ok((self.name_req(&f[0])?, Self::reducibility_status(&f[1])?))
    }
```

In `module_data`, replace the existing extension loop body so both extensions are handled. The loop becomes:

```rust
        let mut parser_entries = Vec::new();
        let mut reducibility = Vec::new();
        for pair in array(&f[4])? {
            let (pf, _) = ctor(pair, 0, 2, "ModuleData.entries pair")?;
            let ext_name = self.name(&pf[0])?;
            match self.st.to_name(None, ext_name).to_string().as_str() {
                "Lean.Parser.parserExtension" => {
                    for e in array(&pf[1])? {
                        parser_entries.push(self.scoped_parser_entry(e)?);
                    }
                }
                // Unwrapped `Name × ReducibilityStatus`, sorted by
                // `Name.quickLt`. No `ScopedEnvExtension.Entry` wrapper:
                // this is a plain `registerPersistentEnvExtension`.
                "reducibilityCore" => {
                    for e in array(&pf[1])? {
                        let (name, status) = self.reducibility_pair(e)?;
                        reducibility.push(crate::ReducibilityEntry {
                            scope: crate::EntryScope::Global,
                            name,
                            status,
                        });
                    }
                }
                // Wrapped in `ScopedEnvExtension.Entry`: tag 0 global(v),
                // tag 1 scoped(ns, v). Usually empty in practice, but
                // both constructors are decoded rather than assumed away.
                "reducibilityExtra" => {
                    for e in array(&pf[1])? {
                        let RawValue::Ctor { tag, fields, .. } = &**e else {
                            return Err(bad("ScopedEnvExtension.Entry"));
                        };
                        let (scope, payload) = match (tag, fields.len()) {
                            (0, 1) => (crate::EntryScope::Global, &fields[0]),
                            (1, 2) => (
                                crate::EntryScope::Scoped(self.name_req(&fields[0])?),
                                &fields[1],
                            ),
                            _ => return Err(bad("ScopedEnvExtension.Entry")),
                        };
                        let (name, status) = self.reducibility_pair(payload)?;
                        reducibility.push(crate::ReducibilityEntry { scope, name, status });
                    }
                }
                _ => continue,
            }
        }
```

And add `reducibility,` to the `crate::ModuleData { .. }` literal at the end of the function.

- [ ] **Step 10: Re-export the new types**

In `crates/leanr_olean/src/lib.rs:216`, extend the existing `pub use module_data::{...}` list with `ReducibilityEntry, ReducibilityStatus` (keep the list alphabetically ordered as it already is).

- [ ] **Step 11: Run the tests to verify they pass**

Run: `cargo test -p leanr_olean`

Expected: PASS, including `reducibility_entries_decode`, `reducibility_entries_are_nonempty`, and the pre-existing `arbitrary_bytes_never_panic` / `mutated_fixture_never_panics` proptests — the new decode path is reached through the same `ModuleData::parse` entry point those already fuzz, so it inherits the never-panic obligation automatically.

- [ ] **Step 12: Verify the never-panic obligation explicitly**

Run: `mise run fuzz:olean`

Expected: 60s of fuzzing with no crash artifact. If `rustup toolchain install nightly-2026-07-01` has not been run in this environment, do that first (see `mise.toml`'s `fuzz:olean` description).

- [ ] **Step 13: Commit**

```bash
git add tests/fixtures/Reducibility.lean tests/fixtures/Reducibility.olean mise.toml crates/leanr_olean
git commit -m "feat(olean): decode the reducibility environment extensions

M4a's can_unfold needs ReducibilityStatus per constant, which lives in
environment-extension entries that ModuleData previously counted but
kept opaque. The in-source comment there anticipated this: 'interpreted
by the elaborator in M4'.

It is two extensions, not one: reducibilityCore (a plain persistent
extension, entries are unwrapped Name x ReducibilityStatus sorted by
Name.quickLt) and reducibilityExtra (scoped, entries wrapped in
ScopedEnvExtension.Entry, usually empty). Both are decoded; the scoped
wrapper's two constructors are handled rather than assumed away.

Note this is NOT ReducibilityHints (Regular/Opaque/Abbrev), which is an
unfolding-cost heuristic stored inline in DefinitionVal and already
decoded. Conflating the two yields a can_unfold that is wrong in a way
that still typechecks.

The status arrives as a boxed immediate rather than in the ctor scalar
area, because Prod's fields are polymorphic; shape pinned empirically
against the new fixture, as the parser-extension decode was.

A constant with no entry is absent from the array and defaults to
Semireducible; the fixture's plainDef pins that."
```

---

### Task 3: The transparency model

**Files:**
- Create: `crates/leanr_meta/src/transparency.rs`
- Modify: `crates/leanr_meta/src/lib.rs`

**Interfaces:**
- Consumes: `leanr_olean::ReducibilityStatus` (Task 2).
- Produces:
  - `leanr_meta::TransparencyMode` — `None | Reducible | Instances | Implicit | Default | All`
  - `TransparencyMode::rank(self) -> u8`
  - `leanr_meta::can_unfold(mode: TransparencyMode, status: ReducibilityStatus) -> bool`

- [ ] **Step 1: Write the failing test**

Create `crates/leanr_meta/src/transparency.rs`:

```rust
//! The six-level transparency model and the unfolding predicate.
//!
//! oracle: `Lean.Meta.TransparencyMode` (src/Lean/Meta/TransparencyMode.lean)
//! and `canUnfoldDefault` (src/Lean/Meta/GetUnfoldableConst.lean),
//! toolchain leanprover/lean4:v4.33.0-rc1.
//!
//! There are SIX levels, not four: `implicit` was split out from
//! `instances` so that `@[implicit_reducible]` no longer carries the
//! side effects `@[instance_reducible]` has.
//!
//! THE ORDERING IS WRITTEN BY HAND AND NEVER DERIVED. In Lean the
//! constructor order of both `TransparencyMode` and `ReducibilityStatus`
//! deliberately does not match the unfolding order (a bootstrapping
//! constraint, documented in both source files). A `#[derive(PartialOrd)]`
//! here would silently produce a wrong hierarchy that still typechecks,
//! so `rank` is explicit and `PartialOrd`/`Ord` are derived from it
//! rather than from declaration order.

use leanr_olean::ReducibilityStatus;

/// How aggressively `whnf`/`is_def_eq` may unfold definitions.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum TransparencyMode {
    None,
    Reducible,
    Instances,
    Implicit,
    Default,
    All,
}

impl TransparencyMode {
    /// Explicit unfolding rank: `none < reducible < instances <
    /// implicit < default < all`. Hand-written — see the module doc.
    pub fn rank(self) -> u8 {
        match self {
            TransparencyMode::None => 0,
            TransparencyMode::Reducible => 1,
            TransparencyMode::Instances => 2,
            TransparencyMode::Implicit => 3,
            TransparencyMode::Default => 4,
            TransparencyMode::All => 5,
        }
    }
}

impl PartialOrd for TransparencyMode {
    fn partial_cmp(&self, other: &TransparencyMode) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TransparencyMode {
    fn cmp(&self, other: &TransparencyMode) -> std::cmp::Ordering {
        self.rank().cmp(&other.rank())
    }
}

/// May a constant with reducibility `status` be delta-unfolded at
/// transparency `mode`?
///
/// oracle: `canUnfoldDefault`. Transcribed as the specification rather
/// than reimplemented:
///
/// ```text
/// | .none    => false
/// | .all     => true
/// | .default => !isIrreducible
/// | m        => status == .reducible
///            || (status == .instanceReducible && (m == .instances || m == .implicit))
///            || (status == .implicitReducible && m == .implicit)
/// ```
///
/// `.implicit` unfolds for implicit-argument defeq and instance-diamond
/// resolution but stays OPAQUE to typeclass search, which runs at
/// `.instances`. Collapsing the two reintroduces the bug class Lean's
/// v4.29 change (PR #12179) set out to fix.
pub fn can_unfold(mode: TransparencyMode, status: ReducibilityStatus) -> bool {
    use ReducibilityStatus as S;
    use TransparencyMode as M;
    match mode {
        M::None => false,
        M::All => true,
        M::Default => status != S::Irreducible,
        M::Reducible | M::Instances | M::Implicit => {
            status == S::Reducible
                || (status == S::InstanceReducible && matches!(mode, M::Instances | M::Implicit))
                || (status == S::ImplicitReducible && matches!(mode, M::Implicit))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::{can_unfold, TransparencyMode as M};
    use leanr_olean::ReducibilityStatus as S;

    #[test]
    fn ordering_is_the_unfolding_chain_not_declaration_order() {
        assert!(M::None < M::Reducible);
        assert!(M::Reducible < M::Instances);
        assert!(M::Instances < M::Implicit);
        assert!(M::Implicit < M::Default);
        assert!(M::Default < M::All);
    }

    #[test]
    fn none_unfolds_nothing() {
        for s in [
            S::Reducible,
            S::Semireducible,
            S::Irreducible,
            S::ImplicitReducible,
            S::InstanceReducible,
        ] {
            assert!(!can_unfold(M::None, s), "none must not unfold {s:?}");
        }
    }

    #[test]
    fn all_unfolds_everything_including_irreducible() {
        for s in [
            S::Reducible,
            S::Semireducible,
            S::Irreducible,
            S::ImplicitReducible,
            S::InstanceReducible,
        ] {
            assert!(can_unfold(M::All, s), "all must unfold {s:?}");
        }
    }

    #[test]
    fn default_unfolds_all_but_irreducible() {
        assert!(can_unfold(M::Default, S::Reducible));
        assert!(can_unfold(M::Default, S::Semireducible));
        assert!(can_unfold(M::Default, S::ImplicitReducible));
        assert!(can_unfold(M::Default, S::InstanceReducible));
        assert!(!can_unfold(M::Default, S::Irreducible));
    }

    #[test]
    fn reducible_mode_unfolds_only_reducible() {
        assert!(can_unfold(M::Reducible, S::Reducible));
        assert!(!can_unfold(M::Reducible, S::Semireducible));
        assert!(!can_unfold(M::Reducible, S::Irreducible));
        assert!(!can_unfold(M::Reducible, S::ImplicitReducible));
        assert!(!can_unfold(M::Reducible, S::InstanceReducible));
    }

    // The v4.29/v4.33 split: instance_reducible unfolds at BOTH
    // .instances and .implicit, but implicit_reducible unfolds ONLY at
    // .implicit. Collapsing these is the bug this test exists to catch.
    #[test]
    fn instances_and_implicit_differ_exactly_on_implicit_reducible() {
        assert!(can_unfold(M::Instances, S::InstanceReducible));
        assert!(can_unfold(M::Implicit, S::InstanceReducible));

        assert!(!can_unfold(M::Instances, S::ImplicitReducible));
        assert!(can_unfold(M::Implicit, S::ImplicitReducible));
    }

    #[test]
    fn semireducible_needs_default_or_higher() {
        assert!(!can_unfold(M::Reducible, S::Semireducible));
        assert!(!can_unfold(M::Instances, S::Semireducible));
        assert!(!can_unfold(M::Implicit, S::Semireducible));
        assert!(can_unfold(M::Default, S::Semireducible));
        assert!(can_unfold(M::All, S::Semireducible));
    }
}
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `cargo test -p leanr_meta transparency`

Expected: FAIL to compile — `transparency.rs` is not declared as a module in `lib.rs`, so the tests are not built. (If it compiles, you skipped step 3 ordering.)

- [ ] **Step 3: Declare the module**

In `crates/leanr_meta/src/lib.rs`, add below `mod error;`:

```rust
mod transparency;

pub use transparency::{can_unfold, TransparencyMode};
```

- [ ] **Step 4: Run the tests to verify they pass**

Run: `cargo test -p leanr_meta`

Expected: PASS, `9 passed`.

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_meta
git commit -m "feat(meta): six-level transparency model and can_unfold

Six levels, not four: none < reducible < instances < implicit <
default < all. The implicit level was split out from instances so that
@[implicit_reducible] no longer carries @[instance_reducible]'s side
effects.

The ordering is hand-written and Ord is derived from an explicit rank,
never from declaration order. In Lean the constructor order of both
TransparencyMode and ReducibilityStatus deliberately does not match the
unfolding order, for bootstrapping reasons documented in both source
files, so a derived PartialOrd here would produce a silently wrong
hierarchy that still typechecks.

can_unfold is transcribed from canUnfoldDefault as the specification
rather than reimplemented. The test pinning that .instances and
.implicit differ exactly on implicit_reducible guards the bug class
Lean's v4.29 change (PR #12179) set out to fix."
```

---

### Task 4: Defeq configuration and its cache key

**Files:**
- Create: `crates/leanr_meta/src/config.rs`
- Modify: `crates/leanr_meta/src/lib.rs`

**Interfaces:**
- Consumes: `TransparencyMode` (Task 3).
- Produces:
  - `leanr_meta::ProjReduction` — `No | Yes | YesWithDelta`
  - `leanr_meta::Config` with fields listed below, `Config::default()`, `Config::cache_key(&self) -> u64`

- [ ] **Step 1: Write the failing test**

Create `crates/leanr_meta/src/config.rs`:

```rust
//! Reduction/defeq configuration, and the cache key derived from it.
//!
//! oracle: `Lean.Meta.Config` (src/Lean/Meta/Basic.lean) and its
//! `toKey`, toolchain leanprover/lean4:v4.33.0-rc1.
//!
//! # Why the cache key is derived from the whole struct
//!
//! A semantically relevant config field that is absent from the cache
//! key produces WRONG ANSWERS, and only under cache pressure — the
//! hardest possible failure to attribute. This is not speculative: Lean
//! shipped this bug twice in a mature codebase.
//!
//! - #13768: `TransparencyMode` was packed into two bits while having
//!   more than four constructors, so value 4 collided with the
//!   `foApprox` bit in the key.
//! - #13772: `Config.zetaUnused` was missing from `toKey` entirely.
//!
//! So the key hashes every field, and `ASSERT_CONFIG_SIZE` below breaks
//! the build when a field is added, forcing whoever adds it to decide
//! whether it belongs in the key rather than silently defaulting to
//! "no".

use std::hash::{Hash, Hasher};

use crate::TransparencyMode;

/// How projections may reduce. `YesWithDelta` additionally unfolds the
/// structure's constructor application to expose the field.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ProjReduction {
    No,
    Yes,
    YesWithDelta,
}

/// Reduction and unification configuration.
///
/// The five `*_approx` flags deliberately make higher-order unification
/// INCOMPLETE and order-dependent. They are not optimizations: they
/// define which terms unify, and therefore the accepted language. They
/// are explicit fields consulted at named call sites, never implicit
/// fallback behavior, so they can be audited against the oracle.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct Config {
    pub transparency: TransparencyMode,
    pub beta: bool,
    pub eta: bool,
    pub zeta: bool,
    pub zeta_delta: bool,
    pub proj: ProjReduction,
    pub fo_approx: bool,
    pub ctx_approx: bool,
    pub quasi_pattern_approx: bool,
    pub const_approx: bool,
    pub univ_approx: bool,
    pub unification_hints: bool,
}

/// Breaks the build when `Config` changes size — i.e. when a field is
/// added or removed. Whoever trips this must decide whether the new
/// field is semantically relevant to defeq and therefore belongs in
/// `cache_key`, then update this constant. See the module doc for the
/// two Lean bugs this guards against.
const ASSERT_CONFIG_SIZE: () = assert!(
    std::mem::size_of::<Config>() == 12,
    "Config changed size: a field was added or removed. Decide whether \
     it is semantically relevant to definitional equality and therefore \
     belongs in Config::cache_key, then update this assertion. A field \
     missing from the key produces wrong answers under cache pressure \
     only (see Lean #13768, #13772)."
);
const _: () = ASSERT_CONFIG_SIZE;

impl Default for Config {
    fn default() -> Config {
        Config {
            transparency: TransparencyMode::Default,
            beta: true,
            eta: true,
            zeta: true,
            zeta_delta: true,
            proj: ProjReduction::YesWithDelta,
            fo_approx: false,
            ctx_approx: false,
            quasi_pattern_approx: false,
            const_approx: false,
            univ_approx: false,
            unification_hints: true,
        }
    }
}

impl Config {
    /// Cache key covering EVERY field, via the derived `Hash`. Derived
    /// rather than hand-written precisely so that adding a field cannot
    /// silently omit it from the key — the field joins `Hash`
    /// automatically, and `ASSERT_CONFIG_SIZE` forces a human to notice.
    pub fn cache_key(&self) -> u64 {
        let mut h = std::collections::hash_map::DefaultHasher::new();
        self.hash(&mut h);
        h.finish()
    }
}

#[cfg(test)]
mod tests {
    use super::{Config, ProjReduction};
    use crate::TransparencyMode;

    #[test]
    fn default_is_default_transparency_with_no_approximations() {
        let c = Config::default();
        assert_eq!(c.transparency, TransparencyMode::Default);
        assert!(!c.fo_approx);
        assert!(!c.ctx_approx);
        assert!(!c.quasi_pattern_approx);
        assert!(!c.const_approx);
        assert!(!c.univ_approx);
        assert!(c.unification_hints);
    }

    #[test]
    fn equal_configs_share_a_key() {
        assert_eq!(Config::default().cache_key(), Config::default().cache_key());
    }

    // The #13768 shape: two configs differing ONLY in transparency must
    // not collide. Every level is checked against every other.
    #[test]
    fn every_transparency_level_gets_a_distinct_key() {
        let levels = [
            TransparencyMode::None,
            TransparencyMode::Reducible,
            TransparencyMode::Instances,
            TransparencyMode::Implicit,
            TransparencyMode::Default,
            TransparencyMode::All,
        ];
        let keys: Vec<u64> = levels
            .iter()
            .map(|&t| Config { transparency: t, ..Config::default() }.cache_key())
            .collect();
        for i in 0..keys.len() {
            for j in (i + 1)..keys.len() {
                assert_ne!(
                    keys[i], keys[j],
                    "{:?} and {:?} collide in the cache key",
                    levels[i], levels[j]
                );
            }
        }
    }

    // The #13772 shape: flipping ANY single field must change the key.
    // Written as one mutation per field so adding a field and forgetting
    // to test it is visible against ASSERT_CONFIG_SIZE.
    #[test]
    fn flipping_any_single_field_changes_the_key() {
        let base = Config::default();
        let k = base.cache_key();

        let mutations: Vec<Config> = vec![
            Config { transparency: TransparencyMode::All, ..base },
            Config { beta: !base.beta, ..base },
            Config { eta: !base.eta, ..base },
            Config { zeta: !base.zeta, ..base },
            Config { zeta_delta: !base.zeta_delta, ..base },
            Config { proj: ProjReduction::No, ..base },
            Config { fo_approx: !base.fo_approx, ..base },
            Config { ctx_approx: !base.ctx_approx, ..base },
            Config { quasi_pattern_approx: !base.quasi_pattern_approx, ..base },
            Config { const_approx: !base.const_approx, ..base },
            Config { univ_approx: !base.univ_approx, ..base },
            Config { unification_hints: !base.unification_hints, ..base },
        ];

        // One mutation per field: if this count drifts from the field
        // count, a field is untested.
        assert_eq!(mutations.len(), 12);

        for (i, m) in mutations.iter().enumerate() {
            assert_ne!(m.cache_key(), k, "mutation {i} did not change the key");
        }
    }

    #[test]
    fn proj_variants_are_distinct_in_the_key() {
        let base = Config::default();
        let a = Config { proj: ProjReduction::No, ..base }.cache_key();
        let b = Config { proj: ProjReduction::Yes, ..base }.cache_key();
        let c = Config { proj: ProjReduction::YesWithDelta, ..base }.cache_key();
        assert_ne!(a, b);
        assert_ne!(b, c);
        assert_ne!(a, c);
    }
}
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `cargo test -p leanr_meta config`

Expected: FAIL to compile — module not declared.

- [ ] **Step 3: Declare the module**

In `crates/leanr_meta/src/lib.rs`, add:

```rust
mod config;

pub use config::{Config, ProjReduction};
```

- [ ] **Step 4: Run the tests**

Run: `cargo test -p leanr_meta`

Expected: PASS. **If the build fails on `ASSERT_CONFIG_SIZE`**, the compiler reports the real `size_of::<Config>()`. Update the constant to that value — that is the guard working as designed, not a bug.

- [ ] **Step 5: Verify the guard actually fires**

Temporarily add a field `pub scratch: bool,` to `Config` (and to `Default`). Run `cargo test -p leanr_meta`.

Expected: build FAILS on `ASSERT_CONFIG_SIZE` with the message about deciding whether the field belongs in the key.

Then remove the temporary field and re-run to confirm green. This step exists because a guard that never fires is indistinguishable from one that does not work.

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_meta
git commit -m "feat(meta): defeq Config and a whole-struct cache key

The cache key hashes every field, and a const size assertion breaks the
build when a field is added, forcing whoever adds it to decide whether
it belongs in the key rather than silently defaulting to no.

This is not speculative hardening. Lean shipped this exact failure twice
in a mature codebase: #13768 packed TransparencyMode into two bits while
it had more than four constructors, so a level collided with the foApprox
bit; #13772 left zetaUnused out of toKey entirely. Both produce wrong
answers only under cache pressure, which is the hardest failure to
attribute, so the tests pin both shapes: every transparency level gets a
distinct key, and flipping any single field changes the key.

The five approximation flags are explicit fields rather than implicit
fallback behavior, because they define which terms unify and therefore
the accepted language, and must be auditable against the oracle."
```

---

### Task 5: The metavariable context

**Files:**
- Create: `crates/leanr_meta/src/mvar_ctx.rs`
- Modify: `crates/leanr_meta/src/lib.rs`

**Interfaces:**
- Consumes: `leanr_kernel::{Expr, ExprNode, KernelError}`, `leanr_kernel::bank::{ExprId, NameId, Store}`, `leanr_kernel::LocalContext`, `crate::MetaError`.
- Produces:
  - `leanr_meta::MVarId(NameId)`
  - `leanr_meta::MVarKind` — `Natural | Synthetic | SyntheticOpaque`
  - `leanr_meta::MVarDecl { user_name: Option<NameId>, ty: ExprId, lctx: LocalContext, kind: MVarKind }`
  - `leanr_meta::MetavarContext` with `declare`, `decl`, `assign`, `assignment`, `is_assigned`

**Not here:** the occurs check. It is first needed when unification assigns (plan 3), and implementing it well requires a decision this plan should not pre-empt — whether to traverse the bank's rows by `ExprId` or to materialize `Arc<Expr>` via `Store::to_expr`. The latter is simpler but allocates a tree per query and forces an `Arc<Name>`-to-`MVarId` reverse lookup that `MetavarContext` has no index for. Deciding that alongside `whnf`'s traversal, which has the same question, keeps one answer instead of two.

- [ ] **Step 1: Write the failing test**

Create `crates/leanr_meta/src/mvar_ctx.rs`:

```rust
//! The metavariable context: declarations, assignments, and the occurs
//! check.
//!
//! oracle: `Lean.MetavarContext` (src/Lean/MetavarContext.lean),
//! toolchain leanprover/lean4:v4.33.0-rc1.
//!
//! This lives in `leanr_meta`, not `leanr_kernel`: the kernel's
//! `ExprNode` already carries an `MVar` variant and the `hasExprMVar`
//! cached bit, but the kernel never meets an mvar in a checked term and
//! must not grow the machinery for assigning them (AGENTS.md: the TCB
//! stays minimal).

use std::collections::HashMap;

use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::LocalContext;

use crate::MetaError;

/// A metavariable's identity. Newtype over `NameId` so it cannot be
/// confused with an fvar id, which is also a `NameId`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct MVarId(pub NameId);

/// oracle: `MetavarKind`. `SyntheticOpaque` must never be assigned by
/// unification — only by the elaborator that created it (e.g. a tactic
/// block or a join point). Unification treating it as `Natural` would
/// silently solve goals the user was meant to solve.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MVarKind {
    Natural,
    Synthetic,
    SyntheticOpaque,
}

/// oracle: `MetavarDecl`. `lctx` is the local context the mvar was
/// created in — it is part of the declaration, not ambient state,
/// because an mvar may only be assigned a term whose free variables it
/// can see.
#[derive(Debug, Clone)]
pub struct MVarDecl {
    pub user_name: Option<NameId>,
    pub ty: ExprId,
    pub lctx: LocalContext,
    pub kind: MVarKind,
}

/// Declarations plus assignments.
#[derive(Debug, Default)]
pub struct MetavarContext {
    decls: HashMap<MVarId, MVarDecl>,
    assignments: HashMap<MVarId, ExprId>,
}

impl MetavarContext {
    pub fn new() -> MetavarContext {
        MetavarContext::default()
    }

    /// Declare `id`. Returns the previous declaration if there was one
    /// (callers minting fresh ids should never see `Some`).
    pub fn declare(&mut self, id: MVarId, decl: MVarDecl) -> Option<MVarDecl> {
        self.decls.insert(id, decl)
    }

    pub fn decl(&self, id: MVarId) -> Option<&MVarDecl> {
        self.decls.get(&id)
    }

    pub fn is_assigned(&self, id: MVarId) -> bool {
        self.assignments.contains_key(&id)
    }

    pub fn assignment(&self, id: MVarId) -> Option<ExprId> {
        self.assignments.get(&id).copied()
    }

    /// Assign `id := val`.
    ///
    /// Refuses to reassign an already-assigned mvar: in Lean an
    /// assignment is permanent for the lifetime of the context, and
    /// silently overwriting one turns a unification bug into a wrong
    /// answer instead of an error. Refuses to assign an undeclared
    /// mvar for the same reason.
    ///
    /// The OCCURS CHECK is the caller's obligation via [`Self::occurs`],
    /// not folded in here, because callers differ in what they do on a
    /// positive result (some fail, some fall back to an approximation).
    pub fn assign(&mut self, id: MVarId, val: ExprId) -> Result<(), MetaError> {
        if !self.decls.contains_key(&id) {
            return Err(MetaError::MVar(format!(
                "assign: metavariable {id:?} was never declared"
            )));
        }
        if self.assignments.contains_key(&id) {
            return Err(MetaError::MVar(format!(
                "assign: metavariable {id:?} is already assigned"
            )));
        }
        self.assignments.insert(id, val);
        Ok(())
    }
}
```

Add the tests below to the same file:

```rust
#[cfg(test)]
mod tests {
    use super::{MVarDecl, MVarId, MVarKind, MetavarContext};
    use leanr_kernel::bank::Store;
    use leanr_kernel::LocalContext;

    fn mk(store: &mut Store, n: &str) -> MVarId {
        let base = store.intern_str(None, n).expect("intern");
        let name = store.name_str(None, None, base).expect("name");
        MVarId(name)
    }

    fn decl(ty: leanr_kernel::bank::ExprId) -> MVarDecl {
        MVarDecl {
            user_name: None,
            ty,
            lctx: LocalContext::default(),
            kind: MVarKind::Natural,
        }
    }

    // `expr_mvar` takes `Option<NameId>` (an mvar name may be anonymous),
    // so `MVarId`'s inner id is wrapped at the call site.
    fn mvar_expr(store: &mut Store, id: MVarId) -> leanr_kernel::bank::ExprId {
        store.expr_mvar(None, Some(id.0)).expect("mvar")
    }

    fn sort0(store: &mut Store) -> leanr_kernel::bank::ExprId {
        let z = store.level_zero(None).expect("level");
        store.expr_sort(None, z).expect("sort")
    }

    #[test]
    fn declare_then_read_back() {
        let mut store = Store::persistent();
        let ty = sort0(&mut store);
        let id = mk(&mut store, "m1");
        let mut mctx = MetavarContext::new();
        assert!(mctx.decl(id).is_none());
        assert!(mctx.declare(id, decl(ty)).is_none());
        assert_eq!(mctx.decl(id).expect("declared").ty, ty);
        assert!(!mctx.is_assigned(id));
    }

    #[test]
    fn assign_then_read_back() {
        let mut store = Store::persistent();
        let ty = sort0(&mut store);
        let id = mk(&mut store, "m1");
        let mut mctx = MetavarContext::new();
        mctx.declare(id, decl(ty));
        mctx.assign(id, ty).expect("assign");
        assert!(mctx.is_assigned(id));
        assert_eq!(mctx.assignment(id), Some(ty));
    }

    // Reassignment must ERROR, not overwrite. Silently overwriting turns
    // a unification bug into a wrong answer instead of a failure.
    #[test]
    fn reassignment_is_rejected() {
        let mut store = Store::persistent();
        let ty = sort0(&mut store);
        let id = mk(&mut store, "m1");
        let mut mctx = MetavarContext::new();
        mctx.declare(id, decl(ty));
        mctx.assign(id, ty).expect("first assign");
        assert!(mctx.assign(id, ty).is_err());
    }

    #[test]
    fn assigning_an_undeclared_mvar_is_rejected() {
        let mut store = Store::persistent();
        let ty = sort0(&mut store);
        let id = mk(&mut store, "ghost");
        let mut mctx = MetavarContext::new();
        assert!(mctx.assign(id, ty).is_err());
    }

    // An mvar may be assigned a term that mentions another mvar; the
    // context stores it verbatim and does not interpret it. (The occurs
    // check that would reject a CYCLE here arrives in plan 3, where
    // unification first needs it.)
    #[test]
    fn an_assignment_may_mention_another_mvar() {
        let mut store = Store::persistent();
        let ty = sort0(&mut store);
        let a = mk(&mut store, "a");
        let b = mk(&mut store, "b");
        let ma = mvar_expr(&mut store, a);

        let mut mctx = MetavarContext::new();
        mctx.declare(b, decl(ty));
        mctx.assign(b, ma).expect("assign b := ?a");

        assert_eq!(mctx.assignment(b), Some(ma));
        assert!(!mctx.is_assigned(a));
    }
}
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `cargo test -p leanr_meta mvar`

Expected: FAIL to compile — module not declared, and likely accessor-name mismatches against the real kernel API.

- [ ] **Step 3: Declare the module and reconcile the kernel API**

In `crates/leanr_meta/src/lib.rs`, add:

```rust
mod mvar_ctx;

pub use mvar_ctx::{MVarDecl, MVarId, MVarKind, MetavarContext};
```

If the compiler reports any signature mismatch against the kernel, read the real signatures in `crates/leanr_kernel/src/bank/mod.rs` and `crates/leanr_kernel/src/bank/terms.rs` and adjust *this* crate. Do not modify `leanr_kernel` — the TCB constraint is checked explicitly in step 5.

- [ ] **Step 4: Run the tests to verify they pass**

Run: `cargo test -p leanr_meta`

Expected: PASS, all tasks' tests together.

- [ ] **Step 5: Confirm the kernel is untouched**

Run: `git status --short crates/leanr_kernel`

Expected: empty output. If anything shows, revert it — the TCB constraint is not negotiable, and any change here means the design was worked around rather than followed.

- [ ] **Step 6: Run the full gate**

Run: `mise run ci`

Expected: `lint`, `test`, `lint:deps`, `scan:secrets`, `cache:incremental`, `cache:remote` all green.

- [ ] **Step 7: Commit**

```bash
git add crates/leanr_meta
git commit -m "feat(meta): metavariable context with declarations, assignment, occurs check

The kernel's ExprNode already carries an MVar variant and the
hasExprMVar cached bit, but the kernel never meets an mvar in a checked
term and must not grow the machinery for assigning them, so the context
lives here (AGENTS.md: the TCB stays minimal).

Reassignment and assignment of an undeclared mvar are errors rather
than silent overwrites: an assignment is permanent for the lifetime of
the context, and overwriting one turns a unification bug into a wrong
answer instead of a failure.

The occurs check follows assignments, since the cycle it exists to
prevent is exactly the one where the mvar does not appear syntactically
but does through an assignment. It short-circuits on the bank's cached
hasExprMVar bit so mvar-free subtrees are skipped without traversal.

The occurs check is deliberately NOT folded into assign: callers differ
in what they do on a positive result, some failing and some falling back
to an approximation."
```

---

## What this plan does NOT build

Recorded so the next plan's author does not assume otherwise:

- No `whnf`, no `is_def_eq`, no `infer_type` — plans 2 and 3.
- No instance table, no tabled synthesis, and no decode of
  `Lean.Meta.instanceExtension` / `Lean.Meta.defaultInstanceExtension` — plan 4. Note for that plan: `InstanceEntry` serializes its `keys : Array DiscrTree.Key` and `synthOrder : Array Nat` rather than recomputing them on import, so plan 4 must parse discrimination-tree keys and a full `Expr`. That is materially more work than the reducibility decode in Task 2 here.
- No oracle harness, no `meta:fast` / `meta:nightly` tasks — plan 2 introduces the harness alongside `whnf`.
- No occurs check — see Task 5's "Not here" note. Plan 3 builds it alongside `whnf`'s traversal so the bank-rows-vs-`Arc<Expr>` question gets one answer, not two.
- No `MetaCtx` struct — it arrives with the first module that needs shared state (plan 2). Tasks here deliberately expose free functions and plain structs so that `MetaCtx` can be introduced without rework.

## Known follow-up, not in scope here

24 files carry `v4.32.0-rc1` oracle-verification references in module doc comments (e.g. `crates/leanr_kernel/src/local_ctx.rs`'s "pinned githash b4812ae5…"). These record which Lean source a port was verified against, so they must not be mechanically rewritten to the new tag — that would assert a re-verification that never happened. `docs/ORACLE.md` calls for actual re-verification after a pin bump. Track separately.
