# M1b — kernel type checker Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `leanr check` kernel-checks real `.olean` modules and their import closures — the entire pinned toolchain stdlib (~2400 modules) checks with zero errors — via a Rust port of the oracle's C++ kernel (infer/whnf/defeq, inductives, quotients) plus oracle-faithful replay.

**Architecture:** The checker lives in `leanr_kernel` (TCB; still no workspace deps). It mirrors the oracle's C++ kernel function-for-function: a `TypeChecker` with pointer-keyed caches, guarded recursion (`stacker` + depth cap → error, never panic), packed per-node `Expr` metadata behind smart constructors. Admission reconstructs `Declaration`s from decoded `ConstantInfo`s and replays them dependency-first, exactly as the oracle's `Lean/Replay.lean` does. `leanr_olean` gains a search-path loader; `leanr_cli` gains `leanr check`. Spec: `docs/superpowers/specs/2026-07-05-m1b-type-checker-design.md`.

**Tech Stack:** Rust (mise-pinned 1.96.0), num-bigint, stacker (new, TCB), proptest, criterion, cargo-fuzz (local only), the pinned oracle toolchain `leanprover/lean4:v4.32.0-rc1` for fixtures and differential harnesses.

## Global Constraints

- Only these cargo deps may be added: `stacker` (leanr_kernel), `criterion` (leanr_kernel dev-dep), `proptest` (leanr_kernel dev-dep, already used in workspace), `serde_json` (leanr_olean dev-dep, verdict diffing only). Anything else needs a plan change.
- `leanr_kernel` depends on **no workspace crate** (TCB rule, AGENTS.md). External deps after this plan: `num-bigint`, `stacker`. Dependency direction: `leanr_olean → leanr_kernel`, never reverse.
- `.olean` bytes are untrusted: no panic, no unguarded recursion, no unbounded allocation not tied to input length. The **one sanctioned recursion pattern** (this plan amends the crate rule): recursion through `RecGuard::enter`, which combines `stacker::maybe_grow` with a depth counter that returns `KernelError::DeepRecursion` at the cap. Anything else stays loops/explicit stacks.
- Depth-cap rejection is incompleteness, never unsoundness. `MAX_REC_DEPTH = 1_000_000`; the stdlib sweep (Task 16) is the arbiter that the cap is generous enough for real code.
- Every claim about kernel semantics cites oracle source (file:line at githash `b4812ae53eea93439ad5dce5a5c26591c31cb697` = tag `v4.32.0-rc1`) in a comment. C++ kernel paths are relative to `src/kernel/`; Lean paths relative to `src/`.
- The oracle pin (`lean-toolchain` = `leanprover/lean4:v4.32.0-rc1`) does not change in this plan.
- Lint gate before every commit: `mise run lint`. Full gate `mise run ci` where a task says so.
- Conventional-commit prefixes (`feat:`, `test:`, `docs:`, `ci:`, `chore:`).
- Checked arithmetic on anything derived from olean values (M1a rule, unchanged).

## Oracle source access

The C++ kernel is not shipped inside the elan toolchain. Clone it once at the pinned tag before starting (any scratch location; do not commit it):

```bash
git clone --depth 1 --branch v4.32.0-rc1 https://github.com/leanprover/lean4 "$SCRATCH/lean4-src"
cd "$SCRATCH/lean4-src" && git log -1 --format=%H   # must print b4812ae53eea93439ad5dce5a5c26591c31cb697
```

Lean-side sources (`Lean/Replay.lean`, `Lean/Expr.lean`, `Lean/Environment.lean`, `LeanChecker.lean`) are also available inside the toolchain at `~/.elan/toolchains/leanprover--lean4---v4.32.0-rc1/src/lean/`.

## Kernel semantics reference (verified against oracle source at v4.32.0-rc1)

Facts below were read directly from the oracle sources at the pinned tag during planning. Cite these locations in code comments. If an implementation test contradicts one, re-read the cited source — do not guess.

**`type_checker.cpp` map** (the file is 1,160 lines; port order follows Tasks 6–7):

| Oracle function | Lines | Notes |
|---|---|---|
| `infer_fvar / infer_constant / infer_lambda / infer_pi / infer_app / infer_let / infer_proj` | 84–268 | `infer_constant` also rejects unsafe consts referenced from safe decls (92–115) |
| `infer_type_core / infer_type / check / check_ignore_undefined_universes` | 270–316 | two caches: `infer_only` true/false |
| `ensure_sort_core / ensure_pi_core` | 53–82 | whnf-then-retry pattern |
| `is_prop` | 327–331 | |
| `reduce_recursor` | 333–346 | tries `quot_reduce_rec` (quot.h:39–79) then `inductive_reduce_rec` (inductive.cpp, see below) |
| `whnf_fvar / reduce_proj_core / reduce_proj` | 348–388 | `reduce_proj_core` handles string literals (359–365) |
| `whnf_core (cheap_rec, cheap_proj)` | 401–495 | beta, let-zeta, fvar-let-zeta (389–399), proj, iota dispatch |
| `unfold_definition_core / unfold_definition` | 497–535 | delta; hints consulted by caller |
| `is_nat_lit_ext / get_nat_val` | 569–576 | `Nat.zero` counts as a literal |
| `reduce_pow` | 588–607 | guards exponent size before computing |
| `reduce_nat` | 609–639 | binary ops add sub mul pow gcd mod div beq ble land lor xor shiftLeft shiftRight (globals at 28–43); `Nat.succ` folding |
| `whnf` | 641–688 | cache, loop: whnf_core → reduce_nat → reduce_native(skip) → unfold_definition |
| `is_def_eq_binding` | 690–717 | telescopes lambdas/foralls |
| `is_def_eq(level)` / `(levels)` | 719–738 | via `level.cpp` `is_equivalent`:503, `normalize`:439, `operator==`:125, `is_norm_lt`:380, `is_geq`:508–529 |
| `quick_is_def_eq` | 740–765 | ptr eq, defeq-cache (equiv_manager), hash fast-reject, sort/binding/mvar dispatch |
| `is_def_eq_args / try_eta_expansion_core / try_eta_struct_core / is_def_eq_app` | 767–834 | struct eta needs `is_structure_like` (inductive.h) |
| `is_def_eq_proof_irrel` | 836–843 | prop-typed terms equal if types defeq |
| `failed_before / cache_failure` | 845–866 | pointer-pair failure cache |
| `try_unfold_proj_app` | 868–880 | proj-app unfold before lazy delta |
| `is_def_eq_offset` | 961–971 | `Nat.succ`-tower fast path |
| `lazy_delta_reduction(_step) / lazy_delta_proj_reduction` | 882–1026 | hints-ordered unfolding; `cheap_rec/cheap_proj` whnf_core retries |
| `try_string_lit_expansion(_core)` | 1028–1043 | `String.mk` vs string literal |
| `is_def_eq_unit_like` | 1044–1054 | structure-like, one ctor, zero fields |
| `is_def_eq_core / is_def_eq (cached)` | 1056–1139 | the master sequence — port its branch order exactly |
| `eta_expand` | 1140–1160 | used by struct-eta path |

**Admission (`environment.cpp`)**: `check_no_metavar_no_fvar`:87–100, `check_name`:102–109, `check_duplicated_univ_params`:111–125, `check_constant_val`:127–142 (checks name, dup params, no-mvar/fvar in type, then `checker.check(type)` must be a sort), `add_axiom`:152, `add_definition`:160–190 (unsafe defs: header checked, added, then value checked against the *extended* env — meta definitions are recursive), `add_theorem`:192–210 (type must be a Prop), `add_opaque`:211–223, `add_mutual`:224–259 (unsafe/partial only, same-safety, headers then values against extended env), dispatch `environment::add`:261–273. Kernel entry externs: `lean_add_decl`:275, `lean_add_decl_without_checking`:284.

**Inductives (`inductive.cpp`)**: `add_inductive_fn` state:120–210, `check_inductive_types`:211–316 (universe/param telescopes, `to_cnstr_when_K` conditions), `declare_inductive_types`:317–337, `is_valid_ind_app`:338–381, `is_rec_argument`:383–391, `check_positivity`:393–411, `check_constructors`:413–455, `declare_constructors`:456–478, `elim_only_at_universe_zero`:479–537 (large-elim test), `init_elim_level / mk_rec_infos`:538–704 (motives, minors, indices telescopes; K flag), `mk_rec_rules`:705–751, `declare_recursors`:752–779, `operator()`:780–790 (the pipeline order), nested-inductive elimination `elim_nested_inductive_fn`:792–1115 (aux types `_nested.*`, `restore_nested`), `environment::add_inductive`:1116–1129.

**Quotients (`quot.cpp`)**: `check_eq_type`:19–45 (Eq must be an inductive, 1 univ param, 1 ctor `Eq.refl` of the exact expected shape), `add_quot`:47–79 declares `Quot`/`Quot.mk`/`Quot.lift`/`Quot.ind` with hard-coded types built in a local_ctx. Reduction: `quot_reduce_rec` (quot.h:39–79): `Quot.lift f (Quot.mk r a) ↦ f a`, `Quot.ind h (Quot.mk r a) ↦ h a`; arg positions from `quot_val` kind (mk-pos 5, lift arg-pos 3/5, ind arg-pos 3/4).

**Replay (`Lean/Replay.lean`, 189 lines — the normative model for Task 12):**
- Skips **unsafe and partial** constants entirely (lines 176–181): they are neither checked nor added. Consequence: our `Declaration` enum needs no `MutualDefinition` variant and no unsafe-definition admission path; `add_definition`'s unsafe branch (environment.cpp:163–178) is dead code for replay and is NOT ported.
- Dependency-driven: `replayConstant` first replays `ci.getUsedConstantsAsSet` (constants named in type+value), tracked via `remaining`/`pending` sets; a mutual block clears all its members at once.
- Inductives: rebuild `Declaration::Inductive` from the block's `InductiveVal.all` + each ctor's `ConstantInfo` type, with `isUnsafe := false`; constructor deps are replayed too before admission.
- Constructors/recursors are **postponed**: recorded, and after all replays each must be **structurally equal** (`==`, BEq) to the regenerated one in the environment; missing or unequal → error.
- Theorems: a duplicate theorem is tolerated iff name, type, levelParams, and `all` are structurally identical (module-system artifact; Replay.lean:84–97).
- `Quot*` constants: replay `Eq` first, then admit the single `Declaration::Quot` (all four quot infos come from it).
- Errors are wrapped "while replaying declaration '<name>'".

**`Expr.Data` packing (`Lean/Expr.lean`:118–182)** — 64 bits: hash 32 | approxDepth 8 (saturating) | hasFVar 1 | hasExprMVar 1 | hasLevelMVar 1 | hasLevelParam 1 | looseBVarRange 20 (saturating). We mirror this layout exactly so hashes can be cross-checked against the oracle later.

**Substitution (`instantiate.cpp`, `expr.cpp`, `abstract.cpp`)**: `instantiate(e, s, n, subst)`:15–38 (closed-subtree skip via loose-bvar range), `instantiate_rev`:99, `instantiate_lparams`:232–246, `instantiate_type_lparams`:248, `instantiate_value_lparams`:256; `lift_loose_bvars`:expr.cpp:448–466; `abstract` in abstract.cpp (fvar → bvar, same range-skip discipline).

**Local context (`local_ctx.h`)**: `mk_local_decl`:64–66, `mk_pi`/`mk_lambda`:94–99 (abstract fvars back into binders). Kernel fresh fvar ids come from a name generator rooted at `_kernel_fresh` (type_checker.cpp:24).

**Mutation-harness kernel APIs (`Lean/Environment.lean`)**: `Kernel.Environment.addDeclCore` via `@[extern "lean_add_decl"]`:296 (verdict source), `addDeclWithoutChecking` via `@[extern "lean_add_decl_without_checking"]`:307 (kernel bypass for writing rejected constants into an env), `writeModule`:1874 (emit `.olean`). Replay driver reference: `LeanChecker.lean` (toolchain src root).

## File structure

```
crates/leanr_kernel/src/
  lib.rs            (modified: amended recursion rule, new exports)
  error.rs          (new: KernelError — the one error enum for the whole crate)
  guard.rs          (new: RecGuard — the sanctioned guarded-recursion primitive)
  level.rs          (modified: Eq/Hash, normalize, is_equivalent, subst)
  expr.rs           (modified: ExprData + smart constructors + Eq/Hash + accessors)
  subst.rs          (new: instantiate / abstract / lift / instantiate_lparams)
  local_ctx.rs      (new: LocalContext, FVarIdGen)
  tc.rs             (new: TypeChecker — infer/whnf/defeq; the type_checker.cpp port)
  quot_red.rs       (new: quot_reduce_rec — quot.h port)
  decl.rs           (modified: Declaration enum, ConstantInfo PartialEq)
  env.rs            (modified: add_decl admission pipeline)
  inductive.rs      (new: add_inductive_fn port incl. nested elimination)
  quot.rs           (new: add_quot / check_eq_type port)
  replay.rs         (new: Replay.lean port over decoded constant maps)
  used_consts.rs    (new: iterative used-constants fold)
crates/leanr_kernel/benches/check_module.rs   (new: criterion)
crates/leanr_olean/src/loader.rs              (new: SearchPath, load_closure)
crates/leanr_olean/tests/check_fixtures.rs    (new: CI replay of fixtures + mutation verdict diff)
crates/leanr_olean/tests/check_sweep.rs       (new: #[ignored] full-stdlib check)
crates/leanr_olean/fuzz/fuzz_targets/module_data.rs (modified: decode-then-check)
crates/leanr_cli/src/main.rs                  (modified: `leanr check`)
tests/fixtures/mutate.lean                    (new: mutation harness script)
tests/fixtures/Mutations.olean, mutations-verdicts.jsonl (new: committed harness output)
mise.toml                                     (modified: check:stdlib, fixtures:mutations tasks)
ARCHITECTURE.md, AGENTS.md, README.md         (modified: checker documented)
```

Module boundaries inside `leanr_kernel` follow the oracle's file boundaries (tc ↔ type_checker.cpp, inductive ↔ inductive.cpp, …) so audits can proceed file-against-file.

---

### Task 1: Guarded recursion (`RecGuard`) + `KernelError`

**Files:**
- Create: `crates/leanr_kernel/src/guard.rs`, `crates/leanr_kernel/src/error.rs`
- Modify: `crates/leanr_kernel/src/lib.rs`, `crates/leanr_kernel/Cargo.toml`

**Interfaces:**
- Consumes: nothing new.
- Produces: `RecGuard` with `pub fn new() -> RecGuard` and `pub fn enter<R>(&mut self, f: impl FnOnce(&mut RecGuard) -> Result<R, KernelError>) -> Result<R, KernelError>`; `pub const MAX_REC_DEPTH: u32 = 1_000_000`; `KernelError` (all variants below — later tasks add none). Every recursive kernel function in Tasks 2–12 threads `&mut RecGuard` or lives on a struct owning one.

- [ ] **Step 1: Add the dependency**

In `crates/leanr_kernel/Cargo.toml` under `[dependencies]` add `stacker = "0.1"`, then `cargo update -p stacker` and record the locked version in the commit message. Justification (goes in the commit body): TCB dep with rustc pedigree; the alternative — hand-written state machines for whnf/defeq — destroys line-for-line auditability against the oracle, which is the TCB's main defense (spec, "Decisions locked in").

- [ ] **Step 2: Write the failing tests**

`crates/leanr_kernel/src/guard.rs` (tests module at the bottom of the new file):

```rust
#[cfg(test)]
mod tests {
    use super::*;

    /// A recursive function that would blow the OS stack unguarded:
    /// each frame holds a 4 KiB array so 1e5 frames ≈ 400 MiB of stack.
    fn deep(g: &mut RecGuard, n: u64) -> Result<u64, KernelError> {
        let pad = [0u8; 4096];
        std::hint::black_box(&pad);
        if n == 0 {
            return Ok(0);
        }
        g.enter(|g| Ok(deep(g, n - 1)? + 1))
    }

    #[test]
    fn survives_depth_far_beyond_os_stack() {
        let mut g = RecGuard::new();
        assert_eq!(deep(&mut g, 100_000).unwrap(), 100_000);
    }

    #[test]
    fn cap_returns_error_not_panic() {
        let mut g = RecGuard::new();
        fn forever(g: &mut RecGuard) -> Result<(), KernelError> {
            g.enter(forever)
        }
        assert_eq!(forever(&mut g), Err(KernelError::DeepRecursion));
    }

    #[test]
    fn depth_unwinds_after_success() {
        let mut g = RecGuard::new();
        deep(&mut g, 1000).unwrap();
        // Guard is reusable: a second run from depth 0 succeeds.
        assert_eq!(deep(&mut g, 1000).unwrap(), 1000);
    }
}
```

- [ ] **Step 3: Run tests to verify they fail**

Run: `cargo test -p leanr_kernel guard`
Expected: compile error — `RecGuard` not defined.

- [ ] **Step 4: Implement**

`crates/leanr_kernel/src/error.rs`:

```rust
use std::sync::Arc;

use crate::Name;

/// Every failure the kernel can report. Untrusted input maps to `Err`,
/// never a panic (docs/THREAT_MODEL.md). Variants carry the declaration
/// being admitted where known; the CLI adds module context.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KernelError {
    /// Recursion guard cap (guard.rs). Rejection here is incompleteness,
    /// never unsoundness: we refuse, we never accept unchecked.
    DeepRecursion,
    UnknownConstant(Arc<Name>),
    /// oracle: environment.cpp:102 (already_declared_exception)
    AlreadyDeclared(Arc<Name>),
    /// oracle: environment.cpp:111 (duplicate universe level parameter)
    DuplicateUnivParam(Arc<Name>),
    /// oracle: environment.cpp:87 (declaration_has_metavars_exception)
    HasMetavars(Arc<Name>),
    /// oracle: environment.cpp:92 (declaration_has_free_vars_exception)
    HasFVars(Arc<Name>),
    /// oracle: type_checker.cpp:98 (incorrect number of universe levels)
    UnivParamArityMismatch { name: Arc<Name> },
    /// oracle: type_checker.cpp:104-113 (unsafe const in safe decl)
    UnsafeConstInSafeDecl(Arc<Name>),
    /// ensure_sort failed (type_checker.cpp:53) — "type expected"
    TypeExpected,
    /// ensure_pi failed (type_checker.cpp:65) — "function expected"
    FunctionExpected,
    /// oracle: type_checker.cpp:163-197 (app_type_mismatch)
    AppTypeMismatch,
    /// oracle: type_checker.cpp:198-220 (invalid let, type mismatch)
    LetTypeMismatch,
    /// oracle: type_checker.cpp:221-268 (invalid projection)
    InvalidProj,
    /// A loose bound variable escaped (infer_type on BVar is a kernel
    /// invariant violation for *closed* input, but attacker input can
    /// contain loose bvars — reject, don't assert).
    LooseBVar,
    /// Level/expr metavariable reached the checker (spec: the checker
    /// rejects mvars, the decoder does not).
    MetavarEncountered,
    /// oracle: environment.cpp:176/185 (definition_type_mismatch_exception)
    DefTypeMismatch(Arc<Name>),
    /// oracle: environment.cpp:201 (theorem_type_is_not_prop)
    TheoremTypeNotProp(Arc<Name>),
    /// inductive.cpp violations; `what` is a short static reason like
    /// "positivity", "invalid occurrence", "universe too small".
    InvalidInductive { name: Arc<Name>, what: &'static str },
    /// quot.cpp:19-45 — environment lacks the expected `Eq`.
    InvalidQuot { what: &'static str },
    /// Replay: postponed ctor/recursor not structurally equal to the
    /// regenerated one (Replay.lean:149-164).
    ConstructorMismatch(Arc<Name>),
    RecursorMismatch(Arc<Name>),
    /// Replay: name in a ConstantInfo cross-reference missing from the
    /// module set (Replay.lean uses `unreachable!`; untrusted input
    /// makes it a real error for us).
    MissingConstant(Arc<Name>),
}

impl std::fmt::Display for KernelError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            KernelError::DeepRecursion => write!(f, "maximum recursion depth exceeded"),
            KernelError::UnknownConstant(n) => write!(f, "unknown constant '{n}'"),
            KernelError::AlreadyDeclared(n) => write!(f, "'{n}' has already been declared"),
            KernelError::DuplicateUnivParam(n) => write!(f, "duplicate universe parameter '{n}'"),
            KernelError::HasMetavars(n) => write!(f, "declaration '{n}' contains metavariables"),
            KernelError::HasFVars(n) => write!(f, "declaration '{n}' contains free variables"),
            KernelError::UnivParamArityMismatch { name } => {
                write!(f, "incorrect number of universe levels at '{name}'")
            }
            KernelError::UnsafeConstInSafeDecl(n) => {
                write!(f, "invalid declaration, unsafe constant '{n}' used in safe declaration")
            }
            KernelError::TypeExpected => write!(f, "type expected"),
            KernelError::FunctionExpected => write!(f, "function expected"),
            KernelError::AppTypeMismatch => write!(f, "application type mismatch"),
            KernelError::LetTypeMismatch => write!(f, "invalid let declaration, type mismatch"),
            KernelError::InvalidProj => write!(f, "invalid projection"),
            KernelError::LooseBVar => write!(f, "loose bound variable"),
            KernelError::MetavarEncountered => write!(f, "declaration contains metavariables"),
            KernelError::DefTypeMismatch(n) => write!(f, "definition type mismatch at '{n}'"),
            KernelError::TheoremTypeNotProp(n) => write!(f, "theorem type of '{n}' is not a proposition"),
            KernelError::InvalidInductive { name, what } => {
                write!(f, "invalid inductive '{name}': {what}")
            }
            KernelError::InvalidQuot { what } => write!(f, "invalid quotient init: {what}"),
            KernelError::ConstructorMismatch(n) => write!(f, "invalid constructor '{n}'"),
            KernelError::RecursorMismatch(n) => write!(f, "invalid recursor '{n}'"),
            KernelError::MissingConstant(n) => write!(f, "constant '{n}' missing from module set"),
        }
    }
}

impl std::error::Error for KernelError {}
```

`crates/leanr_kernel/src/guard.rs`:

```rust
use crate::KernelError;

/// Depth cap for guarded recursion. Far above anything real code
/// produces (the Task 16 stdlib sweep is the arbiter); low enough that
/// adversarial inputs terminate promptly. Hitting it rejects the input
/// — incompleteness, never unsoundness.
pub const MAX_REC_DEPTH: u32 = 1_000_000;

/// Keep at least this much stack headroom; grow in these increments.
/// Values follow rustc's own use of stacker (compiler/rustc_data_structures).
const RED_ZONE: usize = 128 * 1024;
const STACK_CHUNK: usize = 4 * 1024 * 1024;

/// The one sanctioned recursion pattern in this crate (see lib.rs):
/// every recursive kernel function enters frames through `enter`, which
/// (a) counts depth and errors out at `MAX_REC_DEPTH`, and (b) grows
/// the stack segment via `stacker` so the OS stack can never overflow
/// beneath the cap.
#[derive(Debug, Default)]
pub struct RecGuard {
    depth: u32,
}

impl RecGuard {
    pub fn new() -> RecGuard {
        RecGuard { depth: 0 }
    }

    pub fn enter<R>(
        &mut self,
        f: impl FnOnce(&mut RecGuard) -> Result<R, KernelError>,
    ) -> Result<R, KernelError> {
        if self.depth >= MAX_REC_DEPTH {
            return Err(KernelError::DeepRecursion);
        }
        self.depth += 1;
        let r = stacker::maybe_grow(RED_ZONE, STACK_CHUNK, || f(self));
        self.depth -= 1;
        r
    }
}
```

In `crates/leanr_kernel/src/lib.rs`: add `mod error; mod guard;`, re-export `pub use error::KernelError; pub use guard::{RecGuard, MAX_REC_DEPTH};`, and replace the crate-doc recursion sentence with:

```rust
//! Values of these types are built from UNTRUSTED `.olean` bytes by
//! `leanr_olean`, so they can be adversarially shaped (e.g. 100k-deep
//! `Name` parent chains). Nothing here may recurse proportionally to
//! value depth EXCEPT through `RecGuard::enter` (guard.rs), which
//! bounds depth (error at the cap, never a panic) and grows the stack
//! via `stacker` beneath it. Everything else stays loops or explicit
//! stacks, and the `Arc` tree types implement iterative `Drop`.
```

- [ ] **Step 5: Run tests to verify they pass**

Run: `cargo test -p leanr_kernel`
Expected: all PASS, including the pre-existing M1a suite.

- [ ] **Step 6: Lint and commit**

```bash
mise run lint
git add -A crates/leanr_kernel
git commit -m "feat: RecGuard guarded recursion + KernelError (M1b Task 1)"
```

---

### Task 2: `Level` operations — equality, hashing, `normalize`, `is_equivalent`

**Files:**
- Modify: `crates/leanr_kernel/src/level.rs`, `crates/leanr_kernel/src/lib.rs`

**Interfaces:**
- Consumes: `RecGuard`, `KernelError` (Task 1); existing `Level`, `Name`, `Nat`.
- Produces (all on `impl Level`, all taking `&mut RecGuard` where recursive):
  - `pub fn structural_eq(a: &Arc<Level>, b: &Arc<Level>, g: &mut RecGuard) -> Result<bool, KernelError>` — oracle `operator==` level.cpp:125 with Arc-ptr fast path.
  - `pub fn hash_val(l: &Arc<Level>, g: &mut RecGuard) -> Result<u64, KernelError>`
  - `pub fn normalize(l: &Arc<Level>, g: &mut RecGuard) -> Result<Arc<Level>, KernelError>` — level.cpp:439.
  - `pub fn is_equivalent(a: &Arc<Level>, b: &Arc<Level>, g: &mut RecGuard) -> Result<bool, KernelError>` — level.cpp:503 (`a == b || normalize(a) == normalize(b)`).
  - `pub fn instantiate_params(l: &Arc<Level>, params: &[Arc<Name>], args: &[Arc<Level>], g: &mut RecGuard) -> Result<Arc<Level>, KernelError>`
  - `pub fn is_zero(&self) -> bool`, `pub fn is_never_zero(l: &Arc<Level>, g: &mut RecGuard) -> Result<bool, KernelError>` (level.cpp `is_not_zero`), `pub fn mk_succ(l: Arc<Level>) -> Arc<Level>`, `pub fn mk_max_pair / mk_imax_pair` (the normalizing constructors `mk_max`/`mk_imax`, level.cpp), `pub fn has_mvar(l: &Arc<Level>, g: &mut RecGuard) -> Result<bool, KernelError>`, `pub fn has_param(...) -> Result<bool, KernelError>`.
  - Helper `pub fn to_offset(l: &Arc<Level>) -> (&Arc<Level>, u64)` — peel `Succ` iteratively (loop, no guard needed).

**Port notes (verified):** `normalize` (level.cpp:439–501) works on `to_offset`, collects `max` arguments, sorts by `is_norm_lt` (level.cpp:380: Zero < Param < MVar < Max < IMax ordering with lexicographic recursion into children), dedups args that are prefixes of one another (`is_explicit`/offset logic), rebuilds right-associated `max`. `imax` normalizes via: `imax u 0 = 0`? No — oracle: `imax u v` with `v` known-never-zero → `max u v`; `imax u zero = zero`... read level.cpp:439–501 for the exact `imax` cases while porting; the test table below encodes the observable contract and is the arbiter here.

- [ ] **Step 1: Write the failing tests**

Append to `level.rs` tests (representative — port the full table):

```rust
#[cfg(test)]
mod m1b_tests {
    use super::*;
    use crate::{KernelError, RecGuard};
    use std::sync::Arc;

    fn p(s: &str) -> Arc<Level> {
        Arc::new(Level::Param(Name::from_str(s)))
    }
    fn z() -> Arc<Level> {
        Arc::new(Level::Zero)
    }
    fn s(l: Arc<Level>) -> Arc<Level> {
        Level::mk_succ(l)
    }
    fn max(a: Arc<Level>, b: Arc<Level>) -> Arc<Level> {
        Arc::new(Level::Max(a, b))
    }
    fn imax(a: Arc<Level>, b: Arc<Level>) -> Arc<Level> {
        Arc::new(Level::IMax(a, b))
    }
    fn equiv(a: &Arc<Level>, b: &Arc<Level>) -> bool {
        Level::is_equivalent(a, b, &mut RecGuard::new()).unwrap()
    }

    #[test]
    fn equivalence_table() {
        // max is commutative/idempotent up to normalization
        assert!(equiv(&max(p("u"), p("v")), &max(p("v"), p("u"))));
        assert!(equiv(&max(p("u"), p("u")), &p("u")));
        // succ distributes over max under normalization
        assert!(equiv(&s(max(p("u"), p("v"))), &max(s(p("u")), s(p("v")))));
        // imax with succ rhs is max (rhs never zero)
        assert!(equiv(&imax(p("u"), s(p("v"))), &max(p("u"), s(p("v")))));
        // imax u 0 = 0
        assert!(equiv(&imax(p("u"), z()), &z()));
        // imax 0 u = u
        assert!(equiv(&imax(z(), p("u")), &p("u")));
        // distinct params are NOT equivalent
        assert!(!equiv(&p("u"), &p("v")));
        assert!(!equiv(&s(p("u")), &p("u")));
    }

    #[test]
    fn structural_eq_and_hash_agree() {
        let mut g = RecGuard::new();
        let a = max(s(p("u")), imax(p("v"), z()));
        let b = max(s(p("u")), imax(p("v"), z()));
        assert!(Level::structural_eq(&a, &b, &mut g).unwrap());
        assert_eq!(
            Level::hash_val(&a, &mut g).unwrap(),
            Level::hash_val(&b, &mut g).unwrap()
        );
    }

    #[test]
    fn instantiate_params_substitutes() {
        let mut g = RecGuard::new();
        let u = Name::from_str("u");
        let l = max(Arc::new(Level::Param(Arc::clone(&u))), z());
        let r = Level::instantiate_params(&l, &[u], &[s(z())], &mut g).unwrap();
        assert!(equiv(&r, &s(z())));
    }

    #[test]
    fn adversarial_depth_errors_not_crashes() {
        let mut l = z();
        for _ in 0..2_000_000 {
            l = s(l);
        }
        // to_offset peels iteratively — must not be affected by depth
        assert_eq!(Level::to_offset(&l).1, 2_000_000);
        // a 2M-deep *alternating* tree exceeds the guard in normalize
        let mut t = z();
        for i in 0..2_000_000u64 {
            t = if i % 2 == 0 { s(t) } else { max(t, z()) };
        }
        assert_eq!(
            Level::normalize(&t, &mut RecGuard::new()).unwrap_err(),
            KernelError::DeepRecursion
        );
    }
}
```

(`Name::from_str` exists from M1a — check its exact name in `name.rs` before writing; if it is `Name::str(parent, part)`-style, build `Arc<Name>` accordingly and adjust the helpers.)

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p leanr_kernel m1b_tests`
Expected: compile errors (missing functions).

- [ ] **Step 3: Implement**

Port from level.cpp in this order, each function commented with its oracle lines: `mk_succ` (trivial), `mk_max_pair`/`mk_imax_pair` (the smart constructors at level.cpp:56–104: `mk_imax` returns rhs-normalizing cases — `imax(l, zero) = zero`, `imax(zero, l) = l`, `imax(l, l) = l`, rhs `is_not_zero` → `mk_max`), `to_offset` (iterative loop), `structural_eq` (ptr fast path, then guarded match), `hash_val` (guarded; combine children hashes with the same mixer used for Name in name.rs — reuse that helper), `has_mvar`/`has_param` (guarded walks), `instantiate_params` (guarded rebuild; return the same Arc when nothing changed — preserve sharing), `is_norm_lt` (level.cpp:380), `normalize` (level.cpp:439), `is_equivalent` (level.cpp:503: structural_eq OR normalize-compare).

Sharing discipline: every rebuild function returns the input `Arc` unchanged when no child changed (compare with `Arc::ptr_eq`) — this keeps decoder sharing intact so the Task 6 pointer caches stay effective.

- [ ] **Step 4: Run tests to verify they pass**

Run: `cargo test -p leanr_kernel`
Expected: all PASS.

- [ ] **Step 5: Lint and commit**

```bash
mise run lint
git add -A crates/leanr_kernel
git commit -m "feat: Level normalize/is_equivalent/eq/hash (M1b Task 2)"
```

---

### Task 3: `Expr` metadata (`ExprData`) + smart constructors + equality

The representation change of the milestone: `Expr` becomes a struct wrapping the existing enum (renamed `ExprNode`) plus a packed `u64` computed at construction. Everything downstream (decoder, tests, fuzz target) migrates to smart constructors in this task so later tasks never see raw construction.

**Files:**
- Modify: `crates/leanr_kernel/src/expr.rs`, `crates/leanr_kernel/src/lib.rs`
- Modify: `crates/leanr_olean/src/interp.rs` (construction sites), `crates/leanr_cli/src/main.rs` (if it pattern-matches `Expr` — check), `crates/leanr_olean/fuzz/fuzz_targets/module_data.rs` (only if it constructs `Expr`)

**Interfaces:**
- Consumes: `Level::hash_val`/`has_mvar`/`has_param` (Task 2), `RecGuard`.
- Produces:

```rust
pub struct Expr { data: ExprData, node: ExprNode }
pub enum ExprNode { /* exactly the M1a Expr variants, unchanged fields */ }

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ExprData(u64);   // oracle: Lean/Expr.lean:118-127 layout
impl ExprData {
    pub fn hash(self) -> u32;
    pub fn approx_depth(self) -> u8;          // saturating at 255
    pub fn loose_bvar_range(self) -> u32;     // saturating at 2^20 - 1
    pub fn has_fvar(self) -> bool;
    pub fn has_expr_mvar(self) -> bool;
    pub fn has_level_mvar(self) -> bool;
    pub fn has_level_param(self) -> bool;
}

impl Expr {
    // Smart constructors — the ONLY way to build Expr from here on.
    // Each computes ExprData from children in O(1).
    pub fn bvar(idx: Nat) -> Arc<Expr>;
    pub fn fvar(id: Arc<Name>) -> Arc<Expr>;
    pub fn mvar(id: Arc<Name>) -> Arc<Expr>;
    pub fn sort(level: Arc<Level>, g: &mut RecGuard) -> Result<Arc<Expr>, KernelError>;
    pub fn const_(name: Arc<Name>, levels: Vec<Arc<Level>>, g: &mut RecGuard) -> Result<Arc<Expr>, KernelError>;
    pub fn app(f: Arc<Expr>, arg: Arc<Expr>) -> Arc<Expr>;
    pub fn lam(binder_name: Arc<Name>, binder_type: Arc<Expr>, body: Arc<Expr>, binder_info: BinderInfo) -> Arc<Expr>;
    pub fn forall_e(binder_name: Arc<Name>, binder_type: Arc<Expr>, body: Arc<Expr>, binder_info: BinderInfo) -> Arc<Expr>;
    pub fn let_e(decl_name: Arc<Name>, ty: Arc<Expr>, value: Arc<Expr>, body: Arc<Expr>, non_dep: bool) -> Arc<Expr>;
    pub fn lit(l: Literal) -> Arc<Expr>;
    pub fn mdata(data: KVMap, expr: Arc<Expr>) -> Arc<Expr>;
    pub fn proj(type_name: Arc<Name>, idx: Nat, structure: Arc<Expr>) -> Arc<Expr>;

    pub fn node(&self) -> &ExprNode;
    pub fn data(&self) -> ExprData;
    pub fn structural_eq(a: &Arc<Expr>, b: &Arc<Expr>, g: &mut RecGuard) -> Result<bool, KernelError>;

    // App spine helpers (iterative), used constantly in Tasks 6-11:
    pub fn get_app_fn(e: &Arc<Expr>) -> &Arc<Expr>;
    pub fn get_app_args(e: &Arc<Expr>) -> Vec<Arc<Expr>>;
    pub fn get_app_num_args(e: &Arc<Expr>) -> usize;
    pub fn mk_app_spine(f: Arc<Expr>, args: &[Arc<Expr>]) -> Arc<Expr>;
    pub fn is_bvar(&self) -> bool; // + is_app/is_lambda/is_forall/is_sort/is_const/is_fvar/is_let/is_proj/is_lit/is_mdata
    pub fn const_name(&self) -> Option<&Arc<Name>>; // Some iff Const
}
```

- Sort and Const constructors are fallible only because level hashing walks attacker-depth levels; all other constructors are O(1) over already-computed child data and infallible.

**Data computation rules (oracle: Lean/Expr.lean `mkData` uses and the per-ctor `mkExpr*` functions at Expr.lean:600-780; C++ mirror lean_expr_mk_* in expr.cpp):**
- `bvar(idx)`: hash = mix(3, hash(idx as u64 lossy)); looseBVarRange = idx+1 (saturating at 0xFFFFF — beyond-saturation semantics: any range ≥ 2^20-1 means "treat as open, skip no optimizations"); depth 1.
- `fvar`: hasFVar = true. `mvar`: hasExprMVar = true.
- `sort(l)`: hasLevelMVar = l.has_mvar, hasLevelParam = l.has_param, hash from `Level::hash_val`.
- `const_(n, ls)`: level flags OR-folded over `ls`; hash mixes name hash and level hashes.
- Binary/ternary nodes (`app/lam/forall_e/let_e/mdata/proj`): flags = OR of children; approxDepth = 1 + max(children) saturating; looseBVarRange: `app` max(f, arg); `lam/forall` max(type, body−1); `let` max(ty, value, body−1); `mdata/proj` = child's; each `−1` floors at 0 (a binder closes one bvar level). Beyond-saturation ranges never subtract (once saturated, stay saturated).
- hash: same mixer as Name/Level (u64 mix), truncated to 32 bits into the packed word. We do NOT promise oracle-identical hash *values* (the oracle's mixer constants live in Expr.lean `mkData` — matching them is optional; what tests require is: structural_eq ⇒ equal hashes).

- [ ] **Step 1: Write the failing tests**

In `expr.rs` tests:

```rust
#[cfg(test)]
mod m1b_tests {
    use super::*;
    use crate::{Level, Name, Nat, RecGuard};
    use std::sync::Arc;

    fn nm(s: &str) -> Arc<Name> {
        Name::from_str(s) // adjust to the real M1a constructor
    }

    #[test]
    fn loose_bvar_range_tracks_binders() {
        let b0 = Expr::bvar(Nat::from(0u64));
        let b3 = Expr::bvar(Nat::from(3u64));
        assert_eq!(b0.data().loose_bvar_range(), 1);
        assert_eq!(b3.data().loose_bvar_range(), 4);
        let lam = Expr::lam(nm("x"), Expr::bvar(Nat::from(0u64)), Arc::clone(&b0), BinderInfo::Default);
        // λ x, #0 is closed
        assert_eq!(lam.data().loose_bvar_range(), 0);
        let lam_open = Expr::lam(nm("x"), Arc::clone(&b0), Arc::clone(&b3), BinderInfo::Default);
        // body #3 under one binder → range 3; binder type #0 → range 1
        assert_eq!(lam_open.data().loose_bvar_range(), 3);
        let app = Expr::app(b0, b3);
        assert_eq!(app.data().loose_bvar_range(), 4);
    }

    #[test]
    fn flags_propagate() {
        let mut g = RecGuard::new();
        let fv = Expr::fvar(nm("h"));
        let mv = Expr::mvar(nm("m"));
        let app = Expr::app(fv, mv);
        assert!(app.data().has_fvar());
        assert!(app.data().has_expr_mvar());
        let sp = Expr::sort(Arc::new(Level::Param(nm("u"))), &mut g).unwrap();
        assert!(sp.data().has_level_param());
        assert!(!sp.data().has_fvar());
    }

    #[test]
    fn structural_eq_implies_hash_eq_and_ptr_neq_ok() {
        let mut g = RecGuard::new();
        let mk = |g: &mut RecGuard| {
            let n = Expr::const_(nm("Nat"), vec![], g).unwrap();
            Expr::forall_e(nm("x"), Arc::clone(&n), Expr::bvar(Nat::from(0u64)), BinderInfo::Default)
        };
        let a = mk(&mut g);
        let b = mk(&mut g);
        assert!(!Arc::ptr_eq(&a, &b));
        assert!(Expr::structural_eq(&a, &b, &mut g).unwrap());
        assert_eq!(a.data().hash(), b.data().hash());
    }

    #[test]
    fn hash_reject_makes_deep_unequal_cheap() {
        // Two 100k-deep spines differing at the leaf: hash differs, so
        // structural_eq must return false without deep traversal.
        // (Correctness assertion only; the perf claim is the design.)
        let mut g = RecGuard::new();
        let mut a = Expr::bvar(Nat::from(0u64));
        let mut b = Expr::bvar(Nat::from(1u64));
        for _ in 0..100_000 {
            a = Expr::app(a, Expr::lit(Literal::StrVal("x".into())));
            b = Expr::app(b, Expr::lit(Literal::StrVal("x".into())));
        }
        assert!(!Expr::structural_eq(&a, &b, &mut g).unwrap());
    }

    #[test]
    fn app_spine_helpers() {
        let mut g = RecGuard::new();
        let f = Expr::const_(nm("f"), vec![], &mut g).unwrap();
        let x = Expr::lit(Literal::NatVal(Nat::from(1u64)));
        let y = Expr::lit(Literal::NatVal(Nat::from(2u64)));
        let e = Expr::mk_app_spine(Arc::clone(&f), &[x, y]);
        assert!(Arc::ptr_eq(Expr::get_app_fn(&e), &f));
        assert_eq!(Expr::get_app_num_args(&e), 2);
        assert_eq!(Expr::get_app_args(&e).len(), 2);
    }
}
```

- [ ] **Step 2: Run tests to verify they fail**

Run: `cargo test -p leanr_kernel expr::m1b`
Expected: compile errors.

- [ ] **Step 3: Implement the representation change**

1. Rename the current `pub enum Expr` to `pub enum ExprNode` (fields unchanged), keep its iterative `Debug` and move the iterative `Drop`/`take_expr_children` machinery to operate on `ExprNode` (children are now `Arc<Expr>`; the drop-stack type becomes `Vec<Arc<Expr>>` and `take_expr_children(&mut ExprNode, ...)` reaches through `node`).
2. Add `pub struct Expr { data: ExprData, node: ExprNode }` with `Debug` delegating to the node impl plus the packed word, and the accessor/constructor surface from the Interfaces block. `ExprData` packing (bit layout exactly Lean/Expr.lean:118-127):

```rust
// bits 0..32 hash | 32..40 approxDepth | 40 hasFVar | 41 hasExprMVar
// | 42 hasLevelMVar | 43 hasLevelParam | 44..64 looseBVarRange
const LOOSE_BVAR_SAT: u32 = (1 << 20) - 1;
const DEPTH_SAT: u8 = u8::MAX;
```

3. Implement smart constructors per the data-computation rules above. `structural_eq`: ptr fast path → `data` word compare (covers hash+flags fast-reject) → guarded structural descent via `RecGuard::enter` per node pair. Compare `Name`s with the existing `Name` `PartialEq`, levels with `Level::structural_eq`, `Literal`/`BinderInfo` with derived eq. `MData` nodes compare structurally including their `KVMap` entry lists (the oracle's `expr_eq_fn` does not skip mdata); `DataValue::OfSyntax` compares by `Arc::ptr_eq` only, with a comment: kernel checking never needs syntax equality, and decoder sharing makes ptr-eq exact for terms from the same file.
4. Migrate `leanr_olean/src/interp.rs`: every `Arc::new(Expr::Xyz {...})` becomes the smart constructor; the decoder's memoization is unchanged (it memoizes on offset and now stores `Arc<Expr>` of the new type). Adjust any direct field pattern-matches in leanr_olean/cli/tests to go through `.node()`.
5. `cargo build --workspace` until clean.

- [ ] **Step 4: Run the full suite (kernel + olean golden fixtures)**

Run: `cargo test --workspace`
Expected: all PASS — the golden decls fixtures prove the decoder migration changed nothing observable.

- [ ] **Step 5: Lint and commit**

```bash
mise run lint
git add -A
git commit -m "feat: packed ExprData metadata behind Expr smart constructors (M1b Task 3)"
```

---

### Task 4: Substitution — `instantiate`, `abstract`, `lift`, level instantiation

**Files:**
- Create: `crates/leanr_kernel/src/subst.rs`
- Modify: `crates/leanr_kernel/src/lib.rs`

**Interfaces:**
- Consumes: `Expr` smart constructors + `ExprData` (Task 3), `Level::instantiate_params` (Task 2), `RecGuard`.
- Produces (free functions in `subst`, re-exported from lib):

```rust
/// oracle: instantiate.cpp:15-38. Replace loose bvars #s..#(s+subst.len)
/// with subst (subst[0] replaces the OUTERMOST, i.e. #(s+n-1) — match
/// the oracle's convention exactly; the tests below pin it).
pub fn instantiate_core(e: &Arc<Expr>, s: u32, subst: &[Arc<Expr>], g: &mut RecGuard) -> Result<Arc<Expr>, KernelError>;
/// oracle: instantiate.cpp:42 — the common single-substitution form.
pub fn instantiate(e: &Arc<Expr>, sub: &Arc<Expr>, g: &mut RecGuard) -> Result<Arc<Expr>, KernelError>;
/// oracle: instantiate.cpp:99 (subst given innermost-first).
pub fn instantiate_rev(e: &Arc<Expr>, subst: &[Arc<Expr>], g: &mut RecGuard) -> Result<Arc<Expr>, KernelError>;
/// oracle: expr.cpp:448-466.
pub fn lift_loose_bvars(e: &Arc<Expr>, s: u32, d: u32, g: &mut RecGuard) -> Result<Arc<Expr>, KernelError>;
/// oracle: abstract.cpp — fvars (by id) become loose bvars, innermost = last.
pub fn abstract_fvars(e: &Arc<Expr>, fvars: &[Arc<Expr>], g: &mut RecGuard) -> Result<Arc<Expr>, KernelError>;
/// oracle: instantiate.cpp:232-246.
pub fn instantiate_level_params(e: &Arc<Expr>, params: &[Arc<Name>], args: &[Arc<Level>], g: &mut RecGuard) -> Result<Arc<Expr>, KernelError>;
```

**The load-bearing optimization (spec):** every function returns the input `Arc` unchanged (clone of the ref) when the packed data proves no work is possible — `instantiate*`/`lift` when `loose_bvar_range() <= s` (closed enough), `abstract_fvars` when `!has_fvar()`, `instantiate_level_params` when `!has_level_param()`. On rebuilds, if all children come back `Arc::ptr_eq`-identical, return the original node (sharing preservation, same discipline as Task 2). Bvar indices beyond `u32` (possible: `Nat` is bignum) can never be *hit* by a substitution — a term with a loose bvar that large is only reachable if range saturated; handle by comparing the actual `Nat` when the packed range is saturated, and translating an out-of-substitution-window bvar by exact bignum arithmetic (checked; `KernelError::LooseBVar` on impossible states rather than panic).

- [ ] **Step 1: Write the failing tests**

`subst.rs` tests (the convention-pinning cases matter most):

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BinderInfo, Expr, ExprNode, Literal, Name, Nat, RecGuard};
    use std::sync::Arc;

    fn nm(s: &str) -> Arc<Name> { Name::from_str(s) }
    fn bv(i: u64) -> Arc<Expr> { Expr::bvar(Nat::from(i)) }
    fn lit(i: u64) -> Arc<Expr> { Expr::lit(Literal::NatVal(Nat::from(i))) }

    #[test]
    fn instantiate_hits_only_index_zero_at_top() {
        let mut g = RecGuard::new();
        // (#0 #1)[x] = (x #0)  — #1 shifts down to #0
        let e = Expr::app(bv(0), bv(1));
        let r = instantiate(&e, &lit(7), &mut g).unwrap();
        let ExprNode::App { f, arg } = r.node() else { panic!() };
        assert!(Expr::structural_eq(f, &lit(7), &mut g).unwrap());
        assert!(Expr::structural_eq(arg, &bv(0), &mut g).unwrap());
    }

    #[test]
    fn instantiate_shifts_under_binders() {
        let mut g = RecGuard::new();
        // (λ x, #1)[y] = λ x, y   (the #1 refers past the λ to the substituted slot)
        let e = Expr::lam(nm("x"), lit(0), bv(1), BinderInfo::Default);
        let r = instantiate(&e, &lit(7), &mut g).unwrap();
        let ExprNode::Lam { body, .. } = r.node() else { panic!() };
        assert!(Expr::structural_eq(body, &lit(7), &mut g).unwrap());
        // and the substituted term's own loose bvars are lifted:
        // (λ x, #1)[#0] = λ x, #1
        let r2 = instantiate(&e, &bv(0), &mut g).unwrap();
        let ExprNode::Lam { body, .. } = r2.node() else { panic!() };
        assert!(Expr::structural_eq(body, &bv(1), &mut g).unwrap());
    }

    #[test]
    fn closed_subtrees_are_shared_not_copied() {
        let mut g = RecGuard::new();
        let closed = Expr::app(lit(1), lit(2));
        let e = Expr::app(Arc::clone(&closed), bv(0));
        let r = instantiate(&e, &lit(9), &mut g).unwrap();
        let ExprNode::App { f, .. } = r.node() else { panic!() };
        assert!(Arc::ptr_eq(f, &closed)); // the whole point of looseBVarRange
    }

    #[test]
    fn abstract_then_instantiate_roundtrips() {
        let mut g = RecGuard::new();
        let fv = Expr::fvar(nm("h"));
        let e = Expr::app(Arc::clone(&fv), lit(3));
        let abs = abstract_fvars(&e, &[Arc::clone(&fv)], &mut g).unwrap();
        assert_eq!(abs.data().loose_bvar_range(), 1);
        assert!(!abs.data().has_fvar());
        let back = instantiate(&abs, &fv, &mut g).unwrap();
        assert!(Expr::structural_eq(&back, &e, &mut g).unwrap());
    }

    #[test]
    fn instantiate_rev_order_matches_oracle() {
        let mut g = RecGuard::new();
        // instantiate_rev: subst[len-1] replaces #0 (innermost-last).
        let e = Expr::app(bv(0), bv(1));
        let r = instantiate_rev(&e, &[lit(10), lit(20)], &mut g).unwrap();
        let ExprNode::App { f, arg } = r.node() else { panic!() };
        assert!(Expr::structural_eq(f, &lit(20), &mut g).unwrap());
        assert!(Expr::structural_eq(arg, &lit(10), &mut g).unwrap());
    }

    #[test]
    fn level_params_substitute_in_const_and_sort() {
        let mut g = RecGuard::new();
        let u = nm("u");
        let c = Expr::const_(nm("f"), vec![Arc::new(crate::Level::Param(Arc::clone(&u)))], &mut g).unwrap();
        let r = instantiate_level_params(&c, &[u], &[Arc::new(crate::Level::Zero)], &mut g).unwrap();
        let ExprNode::Const { levels, .. } = r.node() else { panic!() };
        assert!(levels[0].is_zero());
        assert!(!r.data().has_level_param());
    }
}
```

- [ ] **Step 2: Run tests to verify they fail** — `cargo test -p leanr_kernel subst` → compile errors.

- [ ] **Step 3: Implement**

Port instantiate.cpp:15–38 faithfully: guarded recursion; at each node, if `loose_bvar_range() as u64 <= s as u64` return unchanged; on `BVar(idx)`: if `idx < s` unchanged; if `idx < s + n` return `lift_loose_bvars(subst[idx - s], 0, s)` — note the oracle indexes `subst[idx - s]` where subst is outermost-first for `instantiate(e, n, subst)` and applies `lift_loose_bvars(subst[i], s)`; `instantiate_rev(e, n, subst)` maps `subst[n - 1 - (idx - s)]` (instantiate.cpp:99–104). If `idx >= s + n`, rebuild `bvar(idx - n)`. Under binders `s + 1`. `abstract_fvars`: guarded descent tracking binder offset; an `FVar` whose id matches `fvars[i]` (compare `Name` eq) becomes `bvar(offset + (len - 1 - i))` (abstract.cpp convention — innermost is the *last* fvar; the round-trip and Task 5 mk_pi tests arbitrate). `instantiate_level_params`: rebuild `Sort`/`Const` levels via `Level::instantiate_params`, skip subtrees with `!has_level_param()`.

- [ ] **Step 4: Run tests** — `cargo test -p leanr_kernel` → all PASS.

- [ ] **Step 5: Lint and commit**

```bash
mise run lint
git add -A crates/leanr_kernel
git commit -m "feat: instantiate/abstract/lift with looseBVarRange skips (M1b Task 4)"
```

---

### Task 5: `LocalContext` and fresh free variables

**Files:**
- Create: `crates/leanr_kernel/src/local_ctx.rs`
- Modify: `crates/leanr_kernel/src/lib.rs`

**Interfaces:**
- Consumes: `Expr`, `subst::abstract_fvars`, `subst::instantiate` (Task 4).
- Produces:

```rust
/// oracle: local_ctx.h:20-47. Kernel-internal; no user names needed.
pub struct LocalDecl {
    pub id: Arc<Name>,           // fresh, from FVarIdGen
    pub binder_name: Arc<Name>,
    pub ty: Arc<Expr>,
    pub binder_info: BinderInfo,
    pub value: Option<Arc<Expr>>, // Some for let-decls (whnf_fvar zeta)
}

/// oracle: local_ctx.h:49+; insertion-ordered map.
#[derive(Default)]
pub struct LocalContext { /* Vec<LocalDecl> + HashMap<Arc<Name>, usize> */ }
impl LocalContext {
    pub fn mk_local_decl(&mut self, gen: &mut FVarIdGen, binder_name: &Arc<Name>, ty: Arc<Expr>, bi: BinderInfo) -> Arc<Expr>; // returns the FVar expr
    pub fn mk_let_decl(&mut self, gen: &mut FVarIdGen, binder_name: &Arc<Name>, ty: Arc<Expr>, value: Arc<Expr>) -> Arc<Expr>;
    pub fn get(&self, fvar_id: &Arc<Name>) -> Option<&LocalDecl>;
    /// oracle: local_ctx.h:94-99 — rebuild Π/λ over the given fvars.
    pub fn mk_pi(&self, fvars: &[Arc<Expr>], e: &Arc<Expr>, g: &mut RecGuard) -> Result<Arc<Expr>, KernelError>;
    pub fn mk_lambda(&self, fvars: &[Arc<Expr>], e: &Arc<Expr>, g: &mut RecGuard) -> Result<Arc<Expr>, KernelError>;
}

/// Fresh ids `_kernel_fresh.<n>` (oracle: type_checker.cpp:24 g_kernel_fresh).
#[derive(Default)]
pub struct FVarIdGen { next: u64 }
```

`mk_pi`/`mk_lambda` abstract the fvars (last = innermost, matching Task 4) and wrap binders using each fvar's stored `binder_name`/`ty`/`binder_info`; a let-decl fvar wraps as `LetE`. The fvar *types* themselves may mention earlier fvars — abstract them progressively exactly as local_ctx.cpp does (per-binder: abstract the accumulated body, then the binder type against the *earlier* fvars).

- [ ] **Step 1: Write the failing tests**

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BinderInfo, Expr, ExprNode, Literal, Name, Nat, RecGuard};
    use std::sync::Arc;

    fn nm(s: &str) -> Arc<Name> { Name::from_str(s) }

    #[test]
    fn mk_pi_roundtrips_a_telescope() {
        let mut g = RecGuard::new();
        let mut lctx = LocalContext::default();
        let mut gen = FVarIdGen::default();
        let nat = Expr::const_(nm("Nat"), vec![], &mut g).unwrap();
        // x : Nat, y : (x = x)-shaped dependent type stand-in: Vec x
        let x = lctx.mk_local_decl(&mut gen, &nm("x"), Arc::clone(&nat), BinderInfo::Default);
        let vec_x = Expr::app(Expr::const_(nm("Vec"), vec![], &mut g).unwrap(), Arc::clone(&x));
        let y = lctx.mk_local_decl(&mut gen, &nm("y"), Arc::clone(&vec_x), BinderInfo::Implicit);
        let body = Expr::app(Arc::clone(&y), Arc::clone(&x));
        let pi = lctx.mk_pi(&[Arc::clone(&x), Arc::clone(&y)], &body, &mut g).unwrap();
        // Result must be closed and shaped Π (x : Nat), Π {y : Vec #0}, #0 #1
        assert_eq!(pi.data().loose_bvar_range(), 0);
        assert!(!pi.data().has_fvar());
        let ExprNode::ForallE { binder_type, body, .. } = pi.node() else { panic!() };
        assert!(Expr::structural_eq(binder_type, &nat, &mut g).unwrap());
        let ExprNode::ForallE { binder_info, binder_type: bt2, body: b2, .. } = body.node() else { panic!() };
        assert_eq!(*binder_info, BinderInfo::Implicit);
        assert_eq!(bt2.data().loose_bvar_range(), 1); // Vec #0
        assert_eq!(b2.data().loose_bvar_range(), 2);  // #0 #1
    }

    #[test]
    fn fresh_ids_never_collide() {
        let mut gen = FVarIdGen::default();
        let mut lctx = LocalContext::default();
        let mut g = RecGuard::new();
        let t = Expr::lit(Literal::NatVal(Nat::from(0u64)));
        let a = lctx.mk_local_decl(&mut gen, &nm("x"), Arc::clone(&t), BinderInfo::Default);
        let b = lctx.mk_local_decl(&mut gen, &nm("x"), t, BinderInfo::Default);
        let (ExprNode::FVar { id: ia }, ExprNode::FVar { id: ib }) = (a.node(), b.node()) else { panic!() };
        assert_ne!(ia, ib);
        assert!(lctx.get(ia).is_some() && lctx.get(ib).is_some());
    }
}
```

- [ ] **Step 2: Run to verify failure** — `cargo test -p leanr_kernel local_ctx` → compile errors.
- [ ] **Step 3: Implement** per the interface block (mk_pi/mk_lambda: fold fvars right-to-left; at each step `abstract_fvars(acc, &[fvar])` then wrap the binder with the decl's stored fields, also abstracting later fvars out of each binder type as the fold proceeds — port local_ctx.cpp `mk_binding` shape).
- [ ] **Step 4: Run tests** — all PASS.
- [ ] **Step 5: Lint and commit** — `git commit -m "feat: LocalContext + fresh fvars (M1b Task 5)"`

---

### Task 6: `TypeChecker` — infer, whnf (beta/zeta/delta/proj), defeq core

The heart of the port. This task lands the whole `TypeChecker` skeleton with every branch present; the branches belonging to Task 7 (iota, quot, nat/string literals, eta/struct-eta/unit-like/offset) are stubbed as `Ok(None)` / `Lbool::Undef` **with their final signatures**, so Task 7 only fills bodies. Port order and structure follow the type_checker.cpp map in the semantics reference; every function carries its oracle line comment.

**Files:**
- Create: `crates/leanr_kernel/src/tc.rs`
- Modify: `crates/leanr_kernel/src/lib.rs`, `crates/leanr_kernel/src/env.rs` (lookup helpers only)

**Interfaces:**
- Consumes: Tasks 1–5 surfaces.
- Produces:

```rust
/// Three-valued result, oracle `lbool` (type_checker.cpp passim).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Lbool { False, True, Undef }

/// Pointer-identity cache key holding its Arc (sound: unshared
/// duplicates miss; decoder sharing makes hits common — spec).
pub(crate) struct ExprPtr(pub Arc<Expr>);  // Hash/Eq via Arc::as_ptr

pub struct TypeChecker<'e> {
    env: &'e Environment,
    safety: DefinitionSafety,        // safe unless admitting unsafe (never, per Replay) — kept for oracle parity
    lparams: Vec<Arc<Name>>,         // set by check(); infer_constant validates against it
    lctx: LocalContext,
    fvar_gen: FVarIdGen,
    guard: RecGuard,
    infer_cache: [HashMap<ExprPtr, Arc<Expr>>; 2],  // [infer_only=false, true] (t_c.cpp:270-303)
    whnf_cache: HashMap<ExprPtr, Arc<Expr>>,        // whnf (641)
    whnf_core_cache: HashMap<ExprPtr, Arc<Expr>>,   // whnf_core cheap=false (401)
    eqv_cache: UnionFind<ExprPtr>,                  // oracle equiv_manager (quick_is_def_eq:745)
    failure_cache: HashSet<(ExprPtr, ExprPtr)>,     // failed_before (845-866)
}

impl<'e> TypeChecker<'e> {
    pub fn new(env: &'e Environment) -> TypeChecker<'e>;
    /// oracle: type_checker.cpp:308-312 — THE public checking entry.
    pub fn check(&mut self, e: &Arc<Expr>, lparams: &[Arc<Name>]) -> Result<Arc<Expr>, KernelError>;
    pub fn infer_type(&mut self, e: &Arc<Expr>) -> Result<Arc<Expr>, KernelError>;   // 304
    pub fn whnf(&mut self, e: &Arc<Expr>) -> Result<Arc<Expr>, KernelError>;         // 641
    pub fn is_def_eq(&mut self, t: &Arc<Expr>, s: &Arc<Expr>) -> Result<bool, KernelError>; // 1133
    pub fn is_prop(&mut self, e: &Arc<Expr>) -> Result<bool, KernelError>;           // 327
    pub fn ensure_sort(&mut self, e: &Arc<Expr>) -> Result<Arc<Expr>, KernelError>;  // 53: returns whnf'd Sort or TypeExpected
    pub fn ensure_pi(&mut self, e: &Arc<Expr>) -> Result<Arc<Expr>, KernelError>;    // 65
}
```

`Environment` gains `pub fn get_with(&self, name: &Arc<Name>) -> Result<&ConstantInfo, KernelError>` (UnknownConstant on miss) plus `pub(crate) fn add_core(&mut self, info: ConstantInfo)` (unchecked insert, oracle environment.cpp:144 — used by admission in Tasks 8–11; not exported).

**Private method skeleton (all present this task; ⋆ = stub until Task 7):**

```text
infer_type_core(e, infer_only)                 // 270: dispatch + per-flag cache; BVar → LooseBVar, MVar → MetavarEncountered
infer_fvar / infer_constant / infer_lambda / infer_pi / infer_app / infer_let / infer_proj / infer_lit(94-268; Lit: Nat/String types via g_nat/g_string names)
check_level(l)                                 // params ⊆ self.lparams, no level mvars (t_c.cpp uses check_ignore_undefined? no: 92-101)
whnf_core(e, cheap_rec, cheap_proj)            // 401
  reduce_proj(e, ...) / reduce_proj_core       // 359-388  (incl. the string-literal case at 359-365 — small, land it in this task)
  whnf_fvar                                    // 348 (let-decl zeta via lctx)
  ⋆ reduce_recursor                            // 333 (iota + quot: Task 7)
whnf(e)                                        // 641: loop { whnf_core; ⋆reduce_nat; unfold_definition } with cache
unfold_definition(_core)                       // 497-535: Const/app-of-Const → instantiate_value_lparams; respects hints? no — height used by defeq only
is_def_eq(t, s) → cached is_def_eq_core        // 1056-1139 exact branch order:
  quick_is_def_eq                              // 740: ptr eq → eqv_cache → node-pair dispatch (Sort/Lambda/ForallE). Do NOT add a hash fast-reject here — the oracle has none at this point, and defeq-unequal hashes prove nothing (defeq ≠ structural).
  whnf_core both (cheap_rec=true, cheap_proj=true), then:
  is_def_eq_proof_irrel                        // 836 (needs infer_type; NOT a stub — proofs are everywhere)
  failure cache check                          // 845
  lazy_delta_reduction loop                    // 973 (+ try_unfold_proj_app 868, ⋆is_def_eq_offset 961, ⋆nat lit cases)
  Const/FVar/Proj head cases, is_def_eq_app    // 815, is_def_eq_binding 690, Sort levels, mdata-skip
  ⋆ try_eta_expansion / ⋆ try_eta_struct       // 778/793
  ⋆ try_string_lit_expansion                   // 1030
  ⋆ is_def_eq_unit_like                        // 1044
  on false: cache_failure
```

Two structural port rules: (1) every mutually-recursive entry (`infer_type_core`, `whnf_core`, `whnf`, `is_def_eq_core`, `lazy_delta_reduction`) enters frames through the guard. Because the guard lives on `self` and the recursive calls also need `&mut self`, `TypeChecker` gets its own `fn guarded<R>(&mut self, f: impl FnOnce(&mut Self) -> Result<R, KernelError>) -> Result<R, KernelError>` that checks/increments a `guard_depth: u32` field against `MAX_REC_DEPTH` and calls `stacker::maybe_grow` directly (same constants as `RecGuard`; no raw pointers, no borrow gymnastics). `RecGuard` itself stays the primitive for the free functions of Tasks 2–5. (2) `mdata` is transparent in whnf/infer (oracle strips it, t_c.cpp:279/427) — strip via `e.node()` match at dispatch heads.

`UnionFind<ExprPtr>`: 40-line path-compressing union-find (port of equiv_manager.cpp's role in quick_is_def_eq: hit → True; merge on successful is_def_eq at 1133–1139).

- [ ] **Step 1: Write the failing tests**

Tests build a small environment BY HAND with `Environment::from_modules` on hand-rolled `ConstantInfo`s (no olean involved — that arrives in Task 12's fixtures). Helper module `tc::tests::mini` provides: `Sort 0`/`Sort u` sorts, `axiom A : Prop`, `axiom a : A`, `def id₁ : Π (α : Sort u), α → α := λ α x, x`, `opaque w : A`, plus a `Nat`-free `Bool`-like inductive faked as axioms (`axiom B : Type`, `axiom bt : B`, `axiom bf : B`) — inductive-free on purpose; recursor behavior is Task 7/9 territory.

```rust
#[test] fn infer_sort_of_sort() {            // infer(Sort u) = Sort (u+1)
#[test] fn infer_lambda_gives_pi() {         // infer(λ (x : A), x) ≡ A → A
#[test] fn check_rejects_loose_bvar() {      // infer(#0) = Err(LooseBVar)
#[test] fn check_rejects_mvar() {            // infer(?m) = Err(MetavarEncountered)
#[test] fn check_rejects_univ_arity() {      // Const id₁ [] where decl has 1 param → UnivParamArityMismatch
#[test] fn app_type_mismatch_rejected() {    // id₁ A a is fine; id₁ a a → AppTypeMismatch (first arg must be a Sort-typed term)
#[test] fn beta_whnf() {                     // whnf((λ x, x) a) = a  (ptr-preserved!)
#[test] fn zeta_whnf() {                     // whnf(let x := a in x) = a
#[test] fn delta_whnf() {                    // whnf(id₁ A a) = a via unfold+beta chain
#[test] fn defeq_alpha_binding() {           // λ x, x ≡ λ y, y (binder names ignored via is_def_eq_binding)
#[test] fn defeq_proof_irrelevance() {       // a ≡ w  (both : A : Prop)
#[test] fn defeq_pi_congruence() {           // Π(x:A),A ≡ Π(y:A),A ; and NOT ≡ Π(x:A),Prop
#[test] fn whnf_cache_and_sharing() {        // whnf twice: second call returns Arc::ptr_eq result
#[test] fn check_sets_lparams() {            // check(λ (α : Sort u) ..., [u]) passes; with [] → UnivParamArityMismatch? no: undefined param → check_level error
```

Write each as real code against the `mini` env; expected values built with smart constructors and compared via `is_def_eq` (for the positive cases) or `structural_eq` (for exact-result cases like beta ptr-preservation, where assert `Arc::ptr_eq`).

- [ ] **Step 2: Run to verify failure** — `cargo test -p leanr_kernel tc` → compile errors.

- [ ] **Step 3: Implement the skeleton + infer**

`infer_type_core` (270–303): cache per `infer_only`; dispatch on node. `infer_constant` (92–115): look up; `levels.len()` must equal decl's `level_params.len()` else `UnivParamArityMismatch`; when `!infer_only` each level is checked (`check_level`: every `Param` must be in `self.lparams`, `MVar` → `MetavarEncountered`); if `self.safety == Safe` and the referenced constant is unsafe → `UnsafeConstInSafeDecl` (104–113: partial is allowed only when... port the exact condition at 104–113). Result: `instantiate_type_lparams(info, levels)`. `infer_lambda` (116–133): loop binders, `mk_local_decl`, infer body with fvars, `mk_pi` back; when `!infer_only`, `ensure_sort(infer(binder_type))` each binder. `infer_pi` (134–158): collect fvar telescope, `ensure_sort` each domain, result `Sort(imax-fold)` via `Level::mk_imax_pair` right-fold. `infer_app` (163–197): spine walk; `ensure_pi` the (whnf'd) fn type; when `!infer_only` check each arg type defeq to domain (`AppTypeMismatch`), instantiate. `infer_let` (198–220): `!infer_only` → check type is sort, check value's type defeq (`LetTypeMismatch`); then infer the body — port the oracle's exact mechanism at 198–220 (it walks nested lets accumulating value-carrying fvars via `mk_let_decl`, infers the body in that context, and instantiates the fvars back out of the result). `infer_proj` (221–268): whnf the structure type, must be app of a `Const` naming a structure-like inductive (one ctor, no indices), walk ctor type params/fields instantiating, return the idx-th field type (`InvalidProj` on every malformed shape). `infer_lit`: `Nat`/`String` const types (the two names are `Name` constants built once).

`whnf_core` (401–495): match on node after mdata-strip; `App` → spine, whnf_core the head cheaply, beta-collapse lambda spines (`instantiate_rev` over as many args as lambdas), retry; `LetE` → zeta (instantiate body with value), retry; `Proj` → `reduce_proj` then retry; `FVar` → let-value zeta (348–358); `Sort` → normalize level? (401 area: sorts pass through); iota/quot dispatch → `reduce_recursor` (stub `Ok(None)` now). `cheap_rec/cheap_proj` plumb through untouched. `unfold_definition(_core)` (497–535): head `Const` (or app-of) whose info is a `Defn` with value; safety gate (unsafe defs unfold only in unsafe mode); build `instantiate_value_lparams`; app case re-applies args. `whnf` (641–688): cache; loop `{ t = whnf_core(t); (⋆reduce_nat/native stubs); match unfold_definition(t) { Some(next) => continue, None => break } }`.

- [ ] **Step 4: Implement defeq core**

`is_def_eq_core` (1056–1131) in the oracle's exact sequence, with Task-7 branches stubbed to `Undef`/`false` **at the same sequence positions** (leave `// M1b Task 7:` markers). `is_def_eq_binding` telescopes with fvars (690–717); `is_def_eq_app` (815): fn defeq + args pairwise; `quick_is_def_eq` (740–765): `Arc::ptr_eq` → `eqv_cache.same` → node-pair dispatch for Sort (level `is_equivalent` under guard), Lambda/ForallE (binding); proof irrelevance (836–843): `infer_type(t)`, `is_prop` on it, `infer_type(s)`, types defeq → equal. `lazy_delta_reduction` (973–1006): loop comparing `ReducibilityHints` — unfold the *greater-height* side first (`Regular(h)` compare; `Abbrev` always unfolds; `Opaque` never here), `whnf_core(cheap_rec=true, cheap_proj=true)` after each unfold, `quick_is_def_eq` re-probe each round. On overall success at `is_def_eq` (1133): `eqv_cache.merge(t, s)`; on `false` from the structural fallthrough: `failure_cache.insert`.

- [ ] **Step 5: Run tests** — `cargo test -p leanr_kernel` → all PASS.

- [ ] **Step 6: Lint and commit**

```bash
mise run lint
git add -A crates/leanr_kernel
git commit -m "feat: TypeChecker core - infer/whnf/defeq skeleton (M1b Task 6)"
```

---

### Task 7: Special reductions — iota, quotients, Nat/String literals, eta family

Fill every Task-6 stub. After this task the `TypeChecker` is semantically complete for safe declarations.

**Files:**
- Create: `crates/leanr_kernel/src/quot_red.rs`
- Modify: `crates/leanr_kernel/src/tc.rs`, `crates/leanr_kernel/src/num.rs` (Nat ops)

**Interfaces:**
- Consumes: Task 6 skeleton; `RecursorVal`/`QuotVal` from decl.rs (M1a).
- Produces: no new public API — the Task 6 stubs become real. `Nat` gains kernel arithmetic (all checked/total): `add sub(truncated) mul pow gcd mod(x%0=x) div(x/0=0) beq ble land lor lxor shiftl shiftr` as `impl Nat` methods over `BigUint`.

**Port checklist (each with oracle ref, each with its own test):**

1. **Iota — `inductive_reduce_rec`** (inductive.cpp bottom region; dispatched from type_checker.cpp:333–346). Head must be `Const(rec_name)` applied to ≥ `num_params+num_motives+num_minors+num_indices+1` args; whnf the major premise (position = all-but-last of that count); K-recursors (`k == true`) may synthesize the unique ctor app when the major's *type* has the right shape (port `to_cnstr_when_K`, inductive.cpp — uses infer+whnf+defeq on the major's type); Nat literal majors convert to `Nat.zero`/`Nat.succ` form (`nat_lit_to_cnstr`), String literals to `String.mk` char list form; major must whnf to a ctor app of a ctor in `rules`; the rule's `rhs` is a closed lambda telescope — apply it (beta) to, in order: the recursor app's params+motives+minors, then the LAST `rule.nfields` args of the ctor app (the fields; the ctor's own params are dropped). Port the exact argument assembly from `inductive_reduce_rec`. Result reapplies any surplus recursor-app args beyond the major position.
2. **Quot reduction** — `quot_red.rs`, port quot.h:39–79 verbatim: for `Const(Quot.lift|Quot.ind)` heads with enough args, whnf the `Quot.mk`-position arg (lift: arg 5 of 6; ind: arg 4 of 5 — 0-based positions from the header comment at quot.h:44–60); if it is `Quot.mk r a` applied fully, reduce to `f a` (arg 3) applied to the remaining spine tail.
3. **Nat literals** — `reduce_nat` (609–639): binary op with BOTH args whnf-literal (`is_nat_lit_ext`: literal or `Nat.zero` const, 569) folds via `Nat` methods; `Nat.succ lit` → lit+1. `reduce_pow` (588–607) refuses huge exponents — port its exact guard constant. beq/ble produce `Bool.true`/`Bool.false` consts. Wire into the `whnf` loop position (t_c.cpp:659–668) and the defeq `lazy_delta` interleave (the oracle checks nat-lit cases inside `lazy_delta_reduction_step`, 882–960 — port placement exactly).
4. **String literals** — `reduce_proj_core` string case (359–365: proj of a string literal = char list access shape) and `try_string_lit_expansion` (1028–1043: `String.mk cs ≟ strLit` → expand the literal to `String.mk` of a char-list literal; needs a `str_lit_to_ctor` helper building `List.cons (Char.ofNat n) ...`).
5. **Offset defeq** — `is_def_eq_offset` (961–971): peel `Nat.succ` towers/literals from both sides, compare stems.
6. **Eta** — `try_eta_expansion(_core)` (778–792): `t` lambda, `s` non-lambda whose type is a Pi → compare `t` with `λ x, s x`. **Structure eta** — `try_eta_struct(_core)` (793–814): `s` a ctor app of a structure-like inductive, `t` anything of that type → compare fieldwise via `Proj` on `t` (needs `Environment::is_structure_like(name)`: inductive, one ctor, no indices — add as a query on `Environment`).
7. **Unit-like** — `is_def_eq_unit_like` (1044–1054): both types whnf to the same structure-like zero-field inductive app → equal.
8. **Proj-app unfold** — `try_unfold_proj_app` (868–880) in the lazy-delta loop.

- [ ] **Step 1: Write the failing tests**

The mini env grows real inductives, still hand-rolled as `ConstantInfo`s (this is deliberate: it also pre-tests Task 9's expectations about the shapes): `Nat` (`zero`/`succ` + `Nat.rec` with its two rules written out by hand — transcribe the types from `#print Nat.rec` under the oracle toolchain and build them with smart constructors in a test helper), `Unit` (structure-like, zero fields), `Prod` (structure-like, two fields), and the four `Quot` constants as `QuotVal`s. Tests (each a real function, expected terms hand-built):

```text
iota_reduces_nat_rec_on_succ      whnf(Nat.rec C z s (Nat.succ n)) steps to s n (Nat.rec C z s n)
iota_on_literal_major             whnf(Nat.rec C z s (lit 2)) reduces (literal → succ form)
k_like_rec_on_eq                  Eq.rec with k=true reduces on rfl-typed major (add Eq to mini env)
quot_lift_beta                    whnf(Quot.lift f h (Quot.mk r a)) = f a
quot_ind_beta                     whnf-style for Quot.ind
nat_add_folds                     whnf(Nat.add 2 3) = lit 5 ; same for sub(2-5=0), div by 0, mod by 0, pow guard returns None un-reduced for huge exponent
nat_beq_folds_to_bool             whnf(Nat.beq 2 2) = Bool.true
succ_folds                        whnf(Nat.succ (lit 4)) = lit 5
offset_defeq                      is_def_eq(Nat.succ (Nat.succ n), n+2 as lit-offset shape)
eta_lambda                        is_def_eq(f, λ x, f x)
eta_struct                        is_def_eq(p, Prod.mk p.1 p.2)
unit_like_defeq                   any two Unit-typed terms defeq
string_lit_expansion              is_def_eq("ab" strLit, String.mk (…char list…))
```

- [ ] **Step 2: Run to verify failure** — new tests fail (stubs return Undef/None).
- [ ] **Step 3: Implement** in checklist order; after each item its tests pass. Keep every stub-site marker comment replaced by the oracle line ref.
- [ ] **Step 4: Full suite** — `cargo test -p leanr_kernel` all PASS.
- [ ] **Step 5: Lint and commit**

```bash
mise run lint
git add -A crates/leanr_kernel
git commit -m "feat: iota/quot/literal/eta reductions - TypeChecker complete (M1b Task 7)"
```

---

### Task 8: `Declaration` and the admission pipeline (axiom/def/thm/opaque)

**Files:**
- Modify: `crates/leanr_kernel/src/decl.rs` (add `Declaration`), `crates/leanr_kernel/src/env.rs` (admission), `crates/leanr_kernel/src/lib.rs`

**Interfaces:**
- Consumes: `TypeChecker` (Tasks 6–7).
- Produces:

```rust
/// Kernel admission INPUT (oracle declaration.h:201; Lean Declaration).
/// No MutualDefinition variant: replay skips unsafe/partial constants
/// (Replay.lean:176-181), which are the only legal mutual defs
/// (environment.cpp:224-232), so the variant is unreachable for us.
#[derive(Debug, Clone)]
pub enum Declaration {
    Axiom(AxiomVal),
    Defn(DefinitionVal),
    Thm(TheoremVal),
    Opaque(OpaqueVal),
    Quot,
    /// oracle: inductive_decl (declaration.h:266+): the mutual block's
    /// level params, num params, and per-type name/type/ctors.
    Inductive {
        lparams: Vec<Arc<Name>>,
        nparams: Nat,
        types: Vec<InductiveType>,
        is_unsafe: bool, // always false from replay
    },
}

#[derive(Debug, Clone)]
pub struct InductiveType {
    pub name: Arc<Name>,
    pub ty: Arc<Expr>,
    pub ctors: Vec<(Arc<Name>, Arc<Expr>)>, // (ctor name, ctor type)
}

impl Environment {
    /// oracle: environment::add (environment.cpp:261-273) — check then
    /// extend. Inductive → Task 9; Quot → Task 11 (stubs error until then:
    /// KernelError::InvalidInductive{what:"not implemented"} placeholder
    /// replaced by those tasks).
    pub fn add_decl(&mut self, d: Declaration) -> Result<(), KernelError>;
}
```

**Admission semantics (port exactly):** `check_constant_val` (environment.cpp:127–133) = `check_name` (AlreadyDeclared) + `check_duplicated_univ_params` + `check_no_metavar_no_fvar(type)` (flags make this O(1): `has_expr_mvar/has_level_mvar` → HasMetavars, `has_fvar` → HasFVars) + `checker.check(type, lparams)` must `ensure_sort`. Then: **Axiom** (152): that's all. **Defn** (160, safe branch only — 179–189): additionally value has no mvar/fvar, `check(value, lparams)` defeq to declared type else `DefTypeMismatch`. A `Defn` with `safety != Safe` returns `DefTypeMismatch`? No — it is a caller error; `add_decl` asserts-by-error: `debug_assert!` plus `Err(InvalidInductive{what:"unsafe declaration reached add_decl"})`? Keep it simple and total: `add_decl` on an unsafe/partial `Defn` returns `KernelError::UnsafeConstInSafeDecl(name)` (documented: replay never sends one). **Thm** (192–210): type must be `is_prop` (`TheoremTypeNotProp`), then value check as Defn. **Opaque** (211–223): like Defn without the safety wrinkle. On success `self.add_core(info)` where `info` is the corresponding `ConstantInfo` built from the val (this is what `constant_info(d)` does in the oracle).

- [ ] **Step 1: Write the failing tests** — the rejection corpus, part 1. In `env.rs` tests, against the Task-7 mini env packaged as a reusable `testenv` helper (promote it from `tc.rs` tests to `crates/leanr_kernel/src/testenv.rs` behind `#[cfg(test)]`):

```text
admits_wellformed_axiom_def_thm_opaque   (happy path for each kind)
rejects_duplicate_name                   AlreadyDeclared
rejects_duplicate_univ_param             DuplicateUnivParam
rejects_mvar_in_type / value             HasMetavars
rejects_fvar_in_type / value             HasFVars
rejects_type_that_is_not_a_sort          TypeExpected  (e.g. type := Nat.zero)
rejects_ill_typed_value                  DefTypeMismatch (def x : Nat := Bool-ish term)
rejects_theorem_not_prop                 TheoremTypeNotProp (thm with type Nat)
rejects_unknown_constant_in_value        UnknownConstant
rejects_unsafe_defn_at_add_decl          UnsafeConstInSafeDecl
env_unchanged_after_rejection            failed add_decl leaves get()/len() identical
```

- [ ] **Step 2: Run to verify failure** — compile errors (`Declaration` missing).
- [ ] **Step 3: Implement** per the semantics block. `add_decl` takes `&mut self`; construct the `TypeChecker` against `&*self` scoped so the borrow ends before `add_core` (check-then-extend; for Defn the oracle checks value against the PRE-extension env in the safe branch — same scoping works).
- [ ] **Step 4: Run tests** — all PASS.
- [ ] **Step 5: Lint and commit** — `git commit -m "feat: Declaration admission for axiom/def/thm/opaque + rejection corpus (M1b Task 8)"`

---

### Task 9: Inductive machinery — mutual, non-nested

The largest single port (inductive.cpp:120–790). One Rust struct `AddInductiveFn` mirroring `add_inductive_fn` state and its pipeline `operator()` (780–790): `check_inductive_types → declare_inductive_types → check_constructors → declare_constructors → mk_rec_infos → declare_recursors`. Nested inductives (`num_nested > 0`) return `InvalidInductive{what:"nested inductive"}` until Task 10.

**Files:**
- Create: `crates/leanr_kernel/src/inductive.rs`
- Modify: `crates/leanr_kernel/src/env.rs` (route `Declaration::Inductive`), `crates/leanr_kernel/src/lib.rs`

**Interfaces:**
- Consumes: everything through Task 8.
- Produces: `pub(crate) fn add_inductive(env: &mut Environment, lparams: Vec<Arc<Name>>, nparams: Nat, types: Vec<InductiveType>, is_unsafe: bool, nnested: Nat) -> Result<(), KernelError>` — `nnested` is threaded from Task 10's elimination (0 in this task); on success the env contains the `InductiveVal`s, `ConstructorVal`s, and `RecursorVal`s **with every metadata field** (`num_params/num_indices/all/ctors/num_nested/is_rec/is_reflexive/k/num_motives/num_minors/rules`) computed exactly as the oracle computes them — Task 12's structural comparison against decoded oleans is the acceptance test for every one of these fields.

**Port map (function-for-function, keep oracle names snake_cased):**

| Rust fn | oracle | what to preserve exactly |
|---|---|---|
| `check_inductive_types` | 211–316 | same lparams across block; each type's type is a telescope of ≥ nparams binders ending in `Sort`; all result levels equal; params of every type defeq-identical to the first's; records `m_lvls/m_result_level/m_params/m_indices`; `m_is_not_zero` via `Level::is_never_zero` |
| `declare_inductive_types` | 317–337 | `add_core` an `InductiveVal` per type — `is_rec`/`is_reflexive` computed in `check_constructors` region (they are settable after; mirror the oracle's ordering: it computes them during ctor checks, then declares — read 317–337 + 413–455 and match the exact sequencing the oracle uses; the golden arbiter is Task 12) |
| `is_valid_ind_app` | 338–381 | app of the d_idx-th type const with THE SAME param prefix (ptr-fast structural compare) and correct arg count |
| `is_rec_argument` | 383–391 | whnf, peel Pi telescope, then is_valid_ind_app |
| `check_positivity` | 393–411 | domain: if the inductive occurs (`has_ind_occ`, a name-occurrence walk) it must be a valid ind app or nested-in-Pi-codomain; else InvalidInductive{"positivity"} |
| `check_constructors` | 413–455 | ctor names fresh, same lparams; telescope: first nparams binders defeq the params; each field type is a sort ≤ result level (unless prop); positivity per field; codomain `is_valid_ind_app` of its own type |
| `declare_constructors` | 456–478 | ConstructorVal{cidx, num_params, num_fields} |
| `elim_only_at_universe_zero` | 479–537 | large-elim decision: false if not prop-sized... port the three conditions (more than one ctor; non-prop field not appearing in codomain indices; etc.) |
| `mk_rec_infos` + `init_elim_level` | 538–704 | elim level `u` fresh name when large-elim; motives (dep elim), minor premises per ctor (recursive fields get induction hypotheses; reflexive types via `is_rec_argument` under binders), indices+major telescope; the `K` flag — the oracle sets it in this region for prop-sized types with exactly one ctor all of whose arguments are the block's params (read the exact `m_K_target` condition at its use site while porting) |
| `mk_rec_rules` | 705–751 | per ctor: rhs = λ params motives minors fields ihs, minor applied to fields+ihs; `nfields` recorded |
| `declare_recursors` | 752–779 | RecursorVal with `num_motives = #types (+aux)`, `num_minors = Σ ctors`, `all` = rec names block, level params = [u?] ++ lparams |

All telescope walks use the Task 5 `LocalContext` + fvars and a fresh `TypeChecker` against the env-so-far (the oracle constructs `type_checker(m_env, ...)` after `declare_inductive_types` so ctor checks can reference the type consts — preserve that phasing).

- [ ] **Step 1: Write the failing tests** — build `Declaration::Inductive` values by hand and admit them; then compare the RESULTING `ConstantInfo`s structurally against hand-transcribed oracle output (`#print Nat.rec`, `#print Prod.rec` etc. under the pinned toolchain — transcribe into test helpers; keep each transcript in a comment above its helper):

```text
admits_nat_and_regenerates_m1a_shapes    Nat: InductiveVal{is_rec:true, ...}, Nat.rec{k:false, 2 rules, num_minors:2, num_motives:1}
admits_prod_structure_like               Prod: 1 ctor, num_indices 0; Prod.rec num_minors 1
admits_eq_with_k                         Eq: Eq.rec has k:true
admits_mutual_pair                       two-type mutual block: `all` lists both, recs reference both motives
prop_only_elim_small                     an inductive that must NOT large-eliminate: rec's elim level is 0 (transcribe `Or` or `Exists`? use `Or`)
large_elim_singleton                     `Eq`-style singleton DOES large-eliminate
rejects_positivity_violation             ctor field (T → T) → T   ⇒ InvalidInductive{"positivity"}
rejects_wrong_codomain                   ctor returning a different type ⇒ InvalidInductive
rejects_universe_too_small               type in Sort 0 with a ctor packing a Type ⇒ InvalidInductive (unless prop rules allow)
rejects_param_mismatch_across_block      mutual block with unequal param telescopes
iota_now_reduces_declared_recursor       whnf(Nat.rec ... (Nat.succ n)) using the REGENERATED recursor (ties Task 7's iota to real generated rules)
```

- [ ] **Step 2: Run to verify failure.**
- [ ] **Step 3: Implement** in port-map order; keep each fn under ~80 lines mirroring its oracle counterpart; every deviation forced by Rust (no exceptions, no mutable global env) documented in a comment.
- [ ] **Step 4: Run tests** — all PASS, including the whole earlier suite.
- [ ] **Step 5: Lint and commit** — `git commit -m "feat: inductive admission with recursor generation, non-nested (M1b Task 9)"`

---

### Task 10: Nested inductives

**Files:**
- Modify: `crates/leanr_kernel/src/inductive.rs`, `crates/leanr_kernel/src/env.rs`

**Interfaces:** none new — `add_inductive` loses its `nested → error` guard. Internally: `ElimNestedInductive` struct porting `elim_nested_inductive_fn` (inductive.cpp:792–1115).

**Semantics (from 792–1115):** when a ctor field mentions *other* inductives applied to the block's types (e.g. `Array Expr` inside `Expr`), the oracle (1) lifts each such application to a fresh auxiliary type in the mutual block (aux names under a reserved `_nested` prefix, 792–809), rewriting occurrences; (2) runs the ordinary Task-9 machinery on the enlarged block in a **scratch environment**; (3) `restore_nested` (828+) maps aux constants back to the real nested applications and copies the resulting decls into the real env under their real names, recording `num_nested`. The recursors gain motives for the aux types (`num_motives` counts them; `num_nested` on the InductiveVal counts aux types).

- [ ] **Step 1: Write the failing tests**

```text
admits_nested_via_list                   `inductive Tree | node : List Tree → Tree` — hand-build with List in env; assert num_nested = 1, Tree.rec has 2 motives, and the `below`-free shapes match `#print Tree.rec` transcription
nested_iota_reduces                      whnf of Tree.rec applied to a node ctor app reduces
rejects_nested_positivity_violation      nested occurrence in a negative position still rejected
stdlib_shape_smoke                       admit the hand-transcribed `Lean.Syntax`-shaped nested inductive (uses Array) — the heaviest nested consumer in the stdlib
```

- [ ] **Step 2–5:** fail → implement → tests pass → `mise run lint` → `git commit -m "feat: nested inductive admission (M1b Task 10)"`. Environment handling during elimination: the aux `_nested.*` declarations must NOT appear in the final environment — only the restored real-named decls land (the aux block lives in a working env used while running the Task-9 machinery; `restore_nested` rewrites results out of it). Port the exact env dataflow from `environment::add_inductive` (inductive.cpp:1116–1129) and the `elim_nested_inductive_fn` result plumbing at 1076–1115.

---

### Task 11: Quotient admission + `ConstantInfo` structural equality

**Files:**
- Create: `crates/leanr_kernel/src/quot.rs`
- Modify: `crates/leanr_kernel/src/decl.rs` (PartialEq), `crates/leanr_kernel/src/env.rs` (route `Declaration::Quot`)

**Interfaces:**
- Produces: `pub(crate) fn add_quot(env: &mut Environment) -> Result<(), KernelError>` (quot.cpp:47–79): requires `Eq` in env shaped exactly as check_eq_type demands (19–45); declares the four `QuotVal` constants with the hard-coded types (transcribe the four types from quot.cpp:59–78 comments — they are written out there as Lean signatures); marks quot initialized (`Environment` gains a `quot_initialized: bool` — iota's quot dispatch (Task 7) must consult it, as the oracle does via `env.is_quot_initialized()`, add the check there now).
- Produces: `impl PartialEq for ConstantInfo` (and the *Val structs + `RecursorRule`): structural, using `Expr::structural_eq`-with-fresh-guard... `PartialEq` can't thread a guard or return `Err`. Resolution: implement `pub fn constant_info_eq(a: &ConstantInfo, b: &ConstantInfo, g: &mut RecGuard) -> Result<bool, KernelError>` in decl.rs instead of the trait (the trait would hide a panic path). Replay (Task 12) and tests use it. Compares every field the oracle's BEq compares — which is ALL fields (derived BEq in Lean).

- [ ] **Step 1: Failing tests**

```text
add_quot_after_eq_succeeds        mini env with hand-built Eq → add_quot → four constants present with expected types (structural compare against transcriptions)
add_quot_without_eq_fails         InvalidQuot{"Eq"}
add_quot_wrong_eq_shape_fails     Eq with 2 ctors → InvalidQuot
quot_iota_gated_on_initialized    before add_quot, Quot.lift application does NOT reduce; after, it does
constant_info_eq_discriminates    equal ↔ structurally equal on each kind; differing hints/safety/rules detected
```

- [ ] **Step 2–5:** fail → implement → pass → `mise run lint` → `git commit -m "feat: quotient admission + ConstantInfo structural equality (M1b Task 11)"`.

---

### Task 12: Replay — oracle-faithful admission of decoded modules

**Files:**
- Create: `crates/leanr_kernel/src/replay.rs`, `crates/leanr_kernel/src/used_consts.rs`
- Modify: `crates/leanr_kernel/src/lib.rs`
- Test: `crates/leanr_olean/tests/check_fixtures.rs` (new — integration: decode fixture oleans and replay them)

**Interfaces:**
- Consumes: everything above; `ModuleData` (from leanr_olean, in the *test* only — replay itself sees plain maps, keeping the kernel workspace-dep-free).
- Produces:

```rust
/// Port of Lean/Replay.lean (see semantics reference). `constants` is
/// the union of the modules-to-check's ConstantInfos (decode order
/// irrelevant); `env` starts as the already-trusted base (empty for
/// fresh checking). Returns the number of declarations sent to the
/// kernel (checked), for CLI reporting.
pub fn replay(env: &mut Environment, constants: HashMap<Arc<Name>, ConstantInfo>) -> Result<ReplayStats, ReplayError>;

pub struct ReplayStats { pub checked: usize, pub skipped_unsafe: usize }

/// KernelError + the offending declaration, mirroring Replay.lean's
/// "while replaying declaration '<name>'" wrapping.
#[derive(Debug, PartialEq, Eq)]
pub struct ReplayError { pub decl: Arc<Name>, pub error: KernelError }
```

`used_consts.rs`: `pub fn used_constants(info: &ConstantInfo) -> Vec<Arc<Name>>` — iterative (explicit stack — NOT guarded recursion; this is a plain walk, keep the crate rule's default) fold over type+value+rec rules collecting `Const` names, deduped.

**Algorithm (Replay.lean:33–189, port faithfully):** worklist of `remaining` (all safe non-partial names); `replay_constant(name)`: if still remaining → pending; recurse into `used_constants`; then per kind: Defn/Axiom/Opaque → `Declaration::*` → `add_decl`; Thm → duplicate-tolerance check (structurally identical name/type/lparams/all against an existing thm → skip) else `add_decl`; Induct → gather the block via `all`, drop all members from remaining/pending, gather ctor infos (recursing into ctor used-constants first), build `Declaration::Inductive{is_unsafe: false}`, `add_decl`; Ctor/Rec → push to postponed sets; Quot → `replay_constant(Eq)` then `add_decl(Declaration::Quot)` once (subsequent quot infos see quot_initialized and skip). Finish: `check_postponed_constructors`/`recursors` — each postponed name must exist in env with `constant_info_eq` true vs the decoded one (else `ConstructorMismatch`/`RecursorMismatch`); recursion in `replay_constant` goes through a `RecGuard` (dependency chains are value-depth-ish: attacker-controlled). Unsafe/partial: counted, never checked, never added (Replay.lean:176–181; document that dependents in safe code cannot exist by construction — the oracle guarantee).

- [ ] **Step 1: Write the failing tests**

Unit (in `replay.rs`, mini-env-based): `replays_out_of_order_deps` (constants map given in reverse dependency order still checks), `postponed_ctor_mismatch_detected` (tamper a decoded-style ConstructorVal's num_fields → ConstructorMismatch), `postponed_rec_mismatch_detected` (tamper a RecursorRule rhs), `skips_unsafe_and_partial` (stats), `thm_duplicate_tolerated`, `missing_dep_is_error` (MissingConstant, not panic).

Integration (`crates/leanr_olean/tests/check_fixtures.rs`):

```rust
/// Hermetic (runs in CI): the new import-free fixture replays from an
/// empty environment. `Prelude0.lean` is a `prelude`-mode file added to
/// `fixtures:regen` in this task: it declares a tiny world (an
/// inductive with a recursive ctor, a def using its recursor, a
/// theorem) and imports nothing.
#[test]
fn prelude0_replays_from_empty_env() {
    let bytes = std::fs::read(fixture_path("Prelude0.olean")).unwrap();
    let m = leanr_olean::ModuleData::parse(&bytes).unwrap();
    let constants: std::collections::HashMap<_, _> = m
        .constants
        .into_iter()
        .map(|c| (std::sync::Arc::clone(c.name()), c))
        .collect();
    let mut env = leanr_kernel::Environment::default();
    let stats = leanr_kernel::replay(&mut env, constants).unwrap();
    assert!(stats.checked >= 3);
}

/// Toolchain-dependent (local, like the M1a sweep): the M1a fixtures
/// import Init, so their closure comes from LEANR_SWEEP_DIR. Manual
/// transitive walk here (read imports, recurse over files); Task 13's
/// loader replaces it. Skipped when LEANR_SWEEP_DIR is unset.
#[test]
#[ignore = "needs the pinned toolchain: LEANR_SWEEP_DIR (mise run check:stdlib covers it)"]
fn fixture_modules_replay_clean_with_closure() {
    for fx in ["Sample.olean", "SampleRich.olean"] {
        let constants = decode_with_import_closure(fixture_path(fx)); // helper in this file
        let mut env = leanr_kernel::Environment::default();
        let stats = leanr_kernel::replay(&mut env, constants).unwrap();
        assert!(stats.checked > 0);
    }
}
```

Add `tests/fixtures/Prelude0.lean` (`prelude`-mode: defines a tiny world — `Nat`-like inductive, a def, a theorem — with zero imports) to `fixtures:regen` in mise.toml, regenerate, commit the olean. CI replays it from the empty environment; the toolchain-closure variants are `#[ignore]`d like the M1a sweep.

- [ ] **Step 2: Run to verify failure.**
- [ ] **Step 3: Implement** replay.rs + used_consts.rs per the algorithm block.
- [ ] **Step 4: Run** `cargo test --workspace` (fixtures replay clean) and `mise run sweep:stdlib` still green (decoder untouched but Task 3 changed Expr — this is the checkpoint that nothing drifted).
- [ ] **Step 5: Lint and commit** — `git commit -m "feat: oracle-faithful replay of decoded modules (M1b Task 12)"`

---

### Task 13: Import-closure loader (`leanr_olean::loader`)

**Files:**
- Create: `crates/leanr_olean/src/loader.rs`
- Modify: `crates/leanr_olean/src/lib.rs`

**Interfaces:**
- Consumes: `ModuleData::parse`, `Import` (M1a).
- Produces:

```rust
pub struct SearchPath { pub roots: Vec<PathBuf> }
impl SearchPath {
    /// Priority: explicit paths, then LEAN_PATH entries, then
    /// `lean --print-libdir` fallback is the CLI's job (Task 14) —
    /// the library takes roots verbatim (no env reads in lib code).
    pub fn new(roots: Vec<PathBuf>) -> SearchPath;
    /// `Init.Data.Nat` → first root containing `Init/Data/Nat.olean`.
    pub fn find(&self, module: &Name) -> Option<PathBuf>;
}

#[derive(Debug, thiserror::Error)]
pub enum LoadError {
    #[error("module '{0}' not found in search path")] ModuleNotFound(String),
    #[error("import cycle through '{0}'")] ImportCycle(String),
    #[error("{path}: {source}")] Io { path: PathBuf, #[source] source: std::io::Error },
    #[error("{path}: {source}")] Decode { path: PathBuf, #[source] source: OleanError },
}

/// Load `targets` and their transitive imports, topologically sorted
/// (dependencies first). Iterative DFS with an explicit stack and an
/// on-stack set for cycle detection (import depth is attacker-ish).
pub fn load_closure(sp: &SearchPath, targets: &[Arc<Name>]) -> Result<Vec<(Arc<Name>, ModuleData)>, LoadError>;
```

Module-name → path mapping: each `Name::Str` component becomes a path segment (reject `Name::Num` components and components containing `/`, `\\`, `..`, or NUL with `ModuleNotFound` — path-traversal hardening for untrusted import tables; module names come from olean bytes).

- [ ] **Step 1: Failing tests** (`loader.rs` unit tests use a tempdir tree of copied fixtures; plus `#[ignore]`d toolchain test):

```text
finds_module_in_second_root         first root missing, second hits
name_to_path_mapping                Init.Data.Nat → Init/Data/Nat.olean
rejects_traversal_components        import named `..` or `a/b` → ModuleNotFound (never touches fs outside roots)
loads_closure_topo_sorted           A imports B imports C: order [C,B,A], each exactly once
detects_cycle                       hand-crafted two-file cycle (write two tiny oleans? cycles can't be produced by lean — craft by copying a fixture and patching its import name bytes is brittle; instead: unit-test the DFS on an injected `fn imports_of` seam — make load_closure generic over a ModuleSource trait, prod impl reads files, test impl serves an in-memory cyclic graph)
diamond_imports_loaded_once         A→{B,C}, B→D, C→D: D appears once
```

- [ ] **Step 2–5:** fail → implement (`ModuleSource` seam: `trait ModuleSource { fn load(&self, m:&Name) -> Result<ModuleData…> }`) → pass → lint → `git commit -m "feat: olean import-closure loader with search paths (M1b Task 13)"`.

---

### Task 14: `leanr check` CLI + mise tasks

**Files:**
- Modify: `crates/leanr_cli/src/main.rs`, `mise.toml`
- Test: `crates/leanr_olean/tests/check_sweep.rs` (the `#[ignore]`d full check). No CLI test harness dep is added: the CLI stays a thin frontend tested by running it (Step 4), with all logic covered at the library level (M1a precedent).

**Interfaces:**
- Produces CLI:

```text
leanr check <module>...  [--path <dir>]...   # roots := --path* ++ LEAN_PATH(split ':') ++ [lean --print-libdir if resolvable]
leanr check --all        [--path <dir>]...   # every *.olean under the roots
```

Behavior: load closure of targets (or enumerate all), `Environment::default()`, one `replay` over the union of all loaded modules' constants (LeanChecker's `--fresh` semantics — everything checked from an empty env, exactly the acceptance bar), per-module progress line `checking <mod> (<i>/<n>)` to stderr, summary `checked N modules, M declarations (skipped U unsafe/partial)` to stdout; on error `error: <module>: while replaying '<decl>': <kernel error>` and exit 1.

mise tasks:

```toml
[tasks."check:stdlib"]
description = "Kernel-check every .olean shipped with the pinned toolchain (local; CI has no Lean)"
depends = ["elan:bootstrap"]
run = "sh -c 'cargo run --release -p leanr_cli -- check --all --path \"$(lean --print-libdir)\"'"
```

and `check_sweep.rs` mirrors it as an `#[ignore]`d test on `LEANR_SWEEP_DIR` (same env-var convention as the M1a sweep) so the sweep is runnable under `cargo test` tooling too.

- [ ] **Step 1: Failing test** — extend `check_fixtures.rs` with a test invoking the same library path the CLI uses (`load_closure` + `replay` over `Prelude0.olean` from an explicit root = the fixtures dir), asserting stats; CLI arg-parsing is exercised by `cargo run -p leanr_cli -- check --help` in Step 4.
- [ ] **Step 2: Verify failure** (new subcommand absent).
- [ ] **Step 3: Implement** subcommand + tasks.
- [ ] **Step 4: Demo the deliverable**

```bash
cargo run --release -p leanr_cli -- check Init.Data.Nat --path "$(mise exec -- lean --print-libdir)"
```

Expected: progress lines for the closure (~200 modules), summary, exit 0.

- [ ] **Step 5: Lint and commit** — `git commit -m "feat: leanr check subcommand + check:stdlib task (M1b Task 14)"`

---

### Task 15: Mutation-differential harness vs the oracle kernel

**Files:**
- Create: `tests/fixtures/mutate.lean`, `tests/fixtures/Mutations.olean` (generated+committed), `tests/fixtures/mutations-verdicts.jsonl` (generated+committed)
- Modify: `mise.toml` (`fixtures:mutations` task), `crates/leanr_olean/tests/check_fixtures.rs` (diff test), `crates/leanr_olean/Cargo.toml` (`serde_json` dev-dep)

**Design (spec §Testing 3, APIs pinned in the semantics reference):** `mutate.lean` runs under the pinned toolchain (`lean --run`):

1. Loads a target module env (default `Init.Core`) via `importModules`.
2. Selects the first `K = 40` safe theorems/defs (deterministic order = the module's constants array; NO randomness — seeded mutation means "seed = constant index", keeping regeneration byte-stable).
3. For each, applies one structural mutation chosen by `index % 5`: (a) swap the last two args of the outermost app in the value; (b) replace the value with the value of the *previous* mutated constant (type/body crossover); (c) bump one `Sort u` in the type to `Sort (u+1)`; (d) replace a `Const` in the value by `id`-wrapped self (changes term but preserves type — an ACCEPT-expected mutant); (e) drop the last lambda binder's use (replace body's `#0` with a fresh constant of the binder type if one exists, else skip).
4. Verdict: `(Lean.Kernel.Environment.addDeclCore kenv 0 decl none)` accept/reject (Environment.lean:296 extern) against the kernel env of the module's imports.
5. Writes each mutated ConstantInfo into an env via `addDeclWithoutChecking` (Environment.lean:307) on top of the import env, then `writeModule env "tests/fixtures/Mutations.olean"` (Environment.lean:1874) — one module containing ALL mutants (renamed `mutant_<i>_<origName>` to avoid clashes; record the rename in the verdict record).
6. Emits `mutations-verdicts.jsonl`: `{"name":"mutant_3_Nat.le_trans","verdict":"reject"}` per line (plus a header line with module + githash).

mise task:

```toml
[tasks."fixtures:mutations"]
description = "Regenerate the mutation-differential fixtures (requires the pinned toolchain)"
depends = ["elan:bootstrap"]
run = "sh -c 'lean --run tests/fixtures/mutate.lean > tests/fixtures/mutations-verdicts.jsonl'"
```

Rust side (`check_fixtures.rs::mutation_verdicts_match`): decode `Mutations.olean`; for each verdict line, replay JUST that constant (plus the real import closure — `#[ignore]`d toolchain-dependent variant; the CI variant targets a `Prelude0`-based mutation set `Mutations0.olean` generated the same way from the import-free fixture, fully hermetic): leanr accept ⇔ oracle accept, per name. Any disagreement prints the constant and both verdicts.

**Scope note:** mutations target `Declaration`-level admission (defs/thms). Inductive-shape mutations are covered by Task 9/10's rejection corpus instead — `addDeclWithoutChecking` can't smuggle an ill-formed inductive's *recursor* consistently into an olean (the oracle regenerates recursors itself), so differential inductive mutation adds machinery without adding acceptance-boundary signal. Verdict granularity is accept/reject only (spec).

- [ ] **Step 1: Write `mutate.lean` + failing Rust test** (test first reads the not-yet-existing fixtures → fails with a clear "run `mise run fixtures:mutations`" message via `expect`).
- [ ] **Step 2: Generate fixtures** — `mise run fixtures:mutations`; sanity-check the jsonl has both accepts and rejects (≥ 5 each; tune the mutation mix if not — mutation (d) supplies accepts).
- [ ] **Step 3: Implement the diff test; run it** — disagreements at this point are REAL FINDINGS: debug the kernel port (systematic-debugging skill), do not adjust verdicts. Expected end state: zero disagreements.
- [ ] **Step 4: Commit fixtures + test** — `git commit -m "test: mutation-differential harness vs oracle kernel verdicts (M1b Task 15)"`

---

### Task 16: Hardening and acceptance — proptest, fuzz, bench, stdlib sweep, docs

**Files:**
- Create: `crates/leanr_kernel/benches/check_module.rs`
- Modify: `crates/leanr_kernel/Cargo.toml` (criterion+proptest dev-deps, `[[bench]]`), `crates/leanr_kernel/src/tc.rs` (proptest module), `crates/leanr_olean/fuzz/fuzz_targets/module_data.rs`, `mise.toml` (bench task), `ARCHITECTURE.md`, `AGENTS.md`, `README.md`, `docs/THREAT_MODEL.md`

- [ ] **Step 1: Proptest invariants** (in `tc.rs`, strategy generating small WELL-TYPED terms by construction over the mini env — a recursive strategy that picks from: literals, consts, well-typed apps of known functions, lambdas over generated bodies):

```text
prop_infer_succeeds_on_generated       infer_type(t) is Ok
prop_whnf_preserves_defeq              is_def_eq(t, whnf(t))
prop_defeq_reflexive_symmetric         is_def_eq(t,t); is_def_eq(t,s) == is_def_eq(s,t)
prop_instantiate_abstract_roundtrip    over generated terms + fresh fvars
```

- [ ] **Step 2: Fuzz target grows check mode** — `module_data.rs`: after a successful decode, run `replay` into a fresh env with a small iteration budget... replay has no budget knob; DoS-by-CPU is out of scope (matches oracle; THREAT_MODEL documents it) — the fuzz goal stays *no panic/UB*: call `replay` and ignore the `Result`. libfuzzer's timeout flag (default in `mise run fuzz`: add `-timeout=120`) bounds pathological runtimes. Run locally ≥ 10 min: `mise run fuzz`.
- [ ] **Step 3: Criterion bench** — `check_module.rs`: decode+replay `SampleRich.olean` (hermetic); report ns/decl. Add `[tasks.bench] run = "cargo bench -p leanr_kernel"`.
- [ ] **Step 4: THE ACCEPTANCE BAR** — run `mise run check:stdlib`. Expected: `checked ~2400 modules, ~<total> declarations` exit 0, zero errors, wall-clock recorded in the commit message. Every failure here is a finding: fix via systematic-debugging; re-run until clean. This step is not done until the full sweep exits 0.
- [ ] **Step 5: Docs** — ARCHITECTURE.md: checker + replay dataflow, guarded-recursion rule, cache design; AGENTS.md: TCB section updated (checker exists; `stacker` is the one sanctioned TCB dep; the RecGuard pattern is the one sanctioned recursion); THREAT_MODEL.md: CPU-DoS acceptance note (mirrors oracle), depth-cap incompleteness note; README quickstart gains `leanr check`.
- [ ] **Step 6: Full gate + commit**

```bash
mise run ci
git add -A
git commit -m "test: proptest/fuzz/bench hardening + stdlib acceptance sweep (M1b Task 16)"
```

---

## Plan self-review (performed at write time)

1. **Spec coverage:** checker w/ all 8 kinds (T6–T11), whnf/defeq fidelity list incl. Nat/String literals + structure eta (T7), Expr metadata + smart constructors (T3), guarded recursion + rule amendment (T1), pointer caches (T6), Declaration + eager rejections (T8), inductive machinery incl. recursor regeneration + match check (T9/T10/T12), quot (T11), replay per Replay.lean incl. structural ctor/rec comparison — resolves the spec's pinned-open comparison question as **structural** (T12), loader (T13), CLI + check:stdlib (T14), rejection corpus (T8/T9/T11) + mutation-differential harness (T15), proptest/fuzz/bench + acceptance sweep + docs (T16). Stable error codes: explicitly deferred by spec. ✓
2. **Known intentional deviations from the spec text** (all narrowing, none loosening): (a) replay *skips* unsafe/partial rather than "type-checks the type" — this is what the oracle's replay actually does (Replay.lean:176–181); the spec's "means what the oracle's acceptance means" clause is satisfied by construction. (b) No `MutualDefinition` declaration variant — unreachable under (a). (c) Loader default root comes from `lean --print-libdir` (the M1a sweep's discovery), not elan directory layout.
3. **Type consistency:** `RecGuard`/`KernelError` (T1) are used by every later signature; `ExprNode`/`Expr::node()` (T3) used in T4–T12 test code; `constant_info_eq` defined T11, consumed T12; `ReplayStats`/`ReplayError` defined T12, consumed T14 CLI. ✓
4. **Placeholders:** Task 6/7/9/10 bodies are long C++ ports; where the plan does not transcribe full Rust bodies it pins (function → oracle file:line → what to preserve) and the arbiter test. Per repo oracle discipline (M1a precedent), the cited C++ **is** the normative how; transcription happens at implementation time against the pinned clone. No TBDs remain.




