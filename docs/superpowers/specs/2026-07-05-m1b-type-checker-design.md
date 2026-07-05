# M1b — kernel type checker

**Date:** 2026-07-05
**Status:** Approved design, pre-implementation
**Parent:** `2026-07-04-leanr-architecture-design.md` (M1, second slice)
**Predecessor:** `2026-07-04-m1a-olean-decoder-design.md`

## Scope

M1 ("`leanr check` re-checks all of Mathlib from `.olean`s") continues.
M1a shipped the decoder and the kernel data model; this slice ships the
checker — everything M1a deferred to M1b, in one pass:

- the type checker in `leanr_kernel`: type inference, reduction (whnf),
  definitional equality, and the declaration-admission pipeline
  (`Environment::add_decl`) covering all eight constant kinds,
  including the full inductive machinery (positivity, universe checks,
  recursor generation) and quotient validation;
- cached per-node `Expr` metadata (hash, loose-bvar range, flags) that
  the checker's fast paths need;
- import-closure resolution in `leanr_olean` (search paths, recursive
  load, cycle detection);
- a `leanr check <module>` CLI command as the demo deliverable.

**Acceptance bar:** the entire pinned toolchain stdlib
(`v4.32.0-rc1`: Init, Std, Lean, and the rest of the ~2400 toolchain
modules) checks with zero errors, sequentially.

The follow-up slice (M1-final) parallelizes checking and takes on
Mathlib scale.

## Decisions locked in

| Decision | Choice |
|---|---|
| Semantic reference | The pinned oracle's C++ kernel (`src/kernel/type_checker.cpp`, `inductive.cpp`, `quot.cpp`), mirrored file-for-file; lean4lean consulted as tiebreak where the C++ is opaque |
| Recursion strategy | Guarded recursion: `stacker::maybe_grow` (segmented stack growth) plus an explicit depth counter returning a `DeepRecursion` error at a generous cap. The `leanr_kernel` crate rule ("no recursion proportional to value depth") is amended to permit exactly this pattern |
| New TCB dependency | `stacker` (with its `psm` backend) — rustc-pedigree, justified as the price of keeping the checker's code shaped like the oracle's |
| Checker location | `leanr_kernel` (per the architecture spec: the kernel owns defeq, reduction, inductives). File IO never enters the kernel crate |
| Cache keying | Per-run memo caches keyed by `Arc` pointer identity — sound because unshared duplicates only miss the cache (cost time, never correctness); effective because the M1a decoder maximally shares subterms |
| Replay strategy | lean4checker's: reconstruct kernel `Declaration`s from decoded `ConstantInfo`s and re-run admission; regenerated constructors/recursors must match the decoded ones |
| Rejection coverage | Hand-written rejection corpus + proptest + a mutation-differential harness that diffs accept/reject verdicts against the oracle kernel |
| Diagnostics | Descriptive `KernelError` variants carrying declaration context; stable `E`-codes and `leanr explain` deferred to the user-facing diagnostics story (M2+) |

**Why hitting the depth cap is safe:** the cap rejects; it can produce
false *rejection* of pathologically deep real code (incompleteness),
never false acceptance (unsoundness). The stdlib sweep is the evidence
that the cap is generous enough for real code.

## Crate changes

### `leanr_kernel` (extended — stays dependency-clean plus `stacker`)

**`TypeChecker`.** Owns a reference to the `Environment`, a
`LocalContext` (free variables created when descending under binders,
as the C++ kernel does), and per-run memo caches for `infer_type`,
`whnf`, and `is_def_eq`, keyed by `Arc` pointer identity. Public
surface: `Environment::add_decl(decl) -> Result<(), KernelError>` as
the admission pipeline, plus `infer_type` / `whnf` / `is_def_eq` for
tests and the differential harness. Everything else is private.

**whnf/defeq fidelity list** — each item traces to its C++ counterpart;
the implementation plan pins line references the way the M1a plan did:

- delta unfolding respecting `ReducibilityHints`, with definitional
  height guiding lazy unfolding order in defeq exactly as the oracle;
- beta, zeta, iota (recursor rules), quotient reduction
  (`Quot.lift` / `Quot.ind`);
- Nat literal acceleration: folding `Nat.add sub mul div mod gcd beq
  ble land lor lxor shiftLeft shiftRight pow` and `Nat.succ` on literal
  arguments via bignum — stdlib proofs rely on kernel-level literal
  arithmetic, so this is in scope, not an optimization;
- String literal handling;
- proof irrelevance, lambda eta, structure eta.

**Level defeq** via the oracle's normalize-and-compare (`is_equiv`
style) with the `imax`/`param` case analysis.

**`Expr` metadata.** Each node carries a packed `u64` (hash,
saturating loose-bvar range, hasFVar / hasExprMVar / hasLevelMVar /
hasLevelParam flags) computed O(1) from children at construction. All
`Expr` construction moves behind smart constructors (`Expr::app(..)`,
…); the M1a decoder and tests migrate to them. `instantiate` /
`abstract` use the loose-bvar range to skip closed subtrees — the
single biggest kernel performance lever.

**`Declaration`.** A new enum — `Axiom`, `Definition`, `Theorem`,
`Opaque`, `Quot`, `Inductive` — the kernel's admission input, distinct
from `ConstantInfo` (the admission *output* stored in oleans). The
inductive form carries the mutual block's types and constructors only,
rebuilt from `InductiveVal.all` and the constructor lists.

**Eager rejections:** metavariables anywhere in an admitted
declaration (M1a decodes them faithfully; the checker rejects them),
free variables escaping the local context, duplicate names,
universe-parameter arity mismatches.

**Admission pipeline per kind:**

- *Axiom / Definition / Theorem / Opaque*: check the type is a sort,
  check the value's inferred type is defeq to the declared type.
  `unsafe`/`partial` definitions (per `DefinitionSafety`) are admitted
  the way the oracle admits them — type checked, value unchecked — so
  the sweep's "zero errors" means what the oracle's acceptance means.
- *Inductive*: mirror `inductive.cpp` — universe and parameter checks,
  positivity, constructor validity, then recursor generation (motives,
  minor premises, iota rules). The regenerated constructor and
  recursor `ConstantInfo`s must match the decoded ones (the exact
  comparison — structural vs defeq — is pinned in the implementation
  plan against lean4checker's behavior); mismatch is a check failure.
  Recursors are derived, never trusted from the file.
- *Quot*: validate `Quot` / `Quot.mk` / `Quot.lift` / `Quot.ind`
  against their expected types exactly as `quot.cpp` does (requires
  `Eq` admitted first, matching the oracle).

**Replay ordering** is dependency-driven, as in lean4checker:
replaying a constant first recursively replays anything its type or
value references that isn't admitted yet. This is robust to
constant-array ordering in the file and handles cross-module
references once the import closure is loaded.

**Errors.** One `KernelError` enum (type mismatch, universe error,
unknown constant, recursor mismatch, deep recursion, metavariable
encountered, …), each variant carrying the offending declaration's
name. No input, however adversarial, panics: the depth cap and checked
arithmetic turn pathological inputs into `Err`.

### `leanr_olean` (extended)

A `loader` module: `SearchPath` (ordered root directories) maps module
names to files (`Init.Nat` → `Init/Nat.olean`);
`load_closure(names) -> Result<Vec<(Name, ModuleData)>, LoadError>`
recursively loads imports, detects cycles, and returns modules
topologically sorted. Search roots, in priority order: explicit
`--path` flags, `LEAN_PATH`, then the pinned toolchain's `lib/lean` directory
discovered via elan (the same discovery the existing sweep task uses).

### `leanr_cli` (extended)

`leanr check <module>...` — resolve the closure, decode, replay every
declaration, print a per-module progress line and a final
`checked N modules, M declarations` summary; non-zero exit on any
failure, with module + declaration context on each error.

### Tasks (mise)

- `check:stdlib` — sweep the whole toolchain (local, non-CI, like
  `olean:sweep`).
- CI runs `leanr check` over the committed fixture modules
  hermetically, and the committed mutation fixtures (below).

## Testing

Four layers, cheapest first:

1. **Unit tests per feature** against the C++ reference behavior:
   whnf on each reduction class, defeq fast/slow paths, level
   equivalence, instantiate/abstract with bvar-range skips, metadata
   correctness (hash/flags recomputed naively in tests and compared
   against the packed values).
2. **Rejection corpus**: hand-written bad declarations — ill-typed
   values, universe violations, positivity violations, forged
   recursors (wrong rule count, wrong minor premises), metavariable
   smuggling, unknown constants, wrong quot signatures — each
   asserting its specific `KernelError` variant.
3. **Mutation-differential harness vs the oracle.** A Lean script
   under the pinned toolchain loads a module, applies seeded
   structural mutations to declarations (argument swaps, constant
   substitutions, universe tweaks, body/type crossovers), obtains the
   oracle's verdict via `Lean.Kernel.Environment.addDeclCore`,
   force-writes the mutated constants into an environment via the
   kernel-bypass `Environment.add`, and emits `mutated.olean` +
   `verdicts.jsonl`. The Rust side loads the mutated olean, replays,
   and diffs **accept/reject verdicts** (not error text) one-to-one.
   A committed fixture set runs in CI; a larger seeded sweep runs
   locally alongside `check:stdlib`.
4. **Acceptance sweep, proptest, fuzz.** The full-stdlib check (the
   acceptance bar); proptest invariants (generated well-typed terms:
   `infer_type` succeeds, whnf preserves defeq, defeq is reflexive and
   symmetric); the existing fuzz target grows a decode-then-check mode
   that must never panic.

A criterion benchmark checks a fixed rich module, giving M1-final's
parallelization a baseline.

## Demo deliverable

`leanr check Init.Nat` (or any toolchain module) resolves the import
closure and kernel-checks every declaration in it; `mise run
check:stdlib` checks all ~2400 toolchain modules with zero errors.

## Deferred (and where it lands)

- Parallel checking + Mathlib-scale sweep — M1-final.
- Stable error codes and `leanr explain` — M2+ diagnostics story.
- Env-extension interpretation — M4 (elaborator).
- JIT/zero-copy/performance work beyond the metadata caches — only if
  profiling demands it.
