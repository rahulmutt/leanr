# M1a — olean decoder + kernel data model

**Date:** 2026-07-04
**Status:** Approved design, pre-implementation
**Parent:** `2026-07-04-leanr-architecture-design.md` (M1, first slice)

## Scope

M1 ("`leanr check` re-checks all of Mathlib from `.olean`s") is sliced.
This slice ships the foundation the checker stands on:

- `leanr_kernel` crate with the kernel **data model** (no checker yet),
- full `.olean` object-graph decoding in `leanr_olean`,
- `Environment` construction from decoded modules,
- a `leanr olean decls <file>` CLI command as the demo deliverable.

The follow-up slice (M1b) adds the type checker (defeq, reduction,
inductives) and import-closure resolution; a later slice parallelizes
over Mathlib.

## Decisions locked in

| Decision | Choice |
|---|---|
| Parse model | Deserialize to **owned** kernel types in one validating pass; no mmap, no zero-copy views |
| Sharing | Memoize on object offset; DAG sharing in the file is preserved via `Arc` in memory |
| Thread-safety | `Arc` (not `Rc`) so the M1 checker can share environments across threads |
| Env extensions | `ModuleData.entries` decoded structurally but kept opaque — kernel checking never reads them (elaborator territory, M4) |
| Import resolution | Deferred to M1b; this slice operates on explicit file sets |
| Bignums | `num-bigint` in `leanr_kernel` — Lean `Nat` literals are arbitrary-precision by semantics |
| Volume validation | Local (non-CI) sweep over every `.olean` shipped with the pinned toolchain; CI stays hermetic on committed fixtures |

**Why owned deserialization** (performance included): the M1 checker
must visit every expression anyway, so conversion cost is amortized and
the walk is memory-bandwidth bound (a few seconds for Mathlib-scale
bytes, parallelizable per module); the kernel wants its own `Expr`
representation for fast defeq regardless, so zero-copy views would just
smear the same conversion across the checker's hot path; and one bounded
validating pass is a far smaller panic-free/fuzz surface than lazy
validation on every accessor. The loader sits behind
`parse(&[u8]) -> Result<ModuleData, OleanError>`, so a
validate-once-then-zero-copy loader can replace it later without moving
any other code.

## Crate changes

### `leanr_kernel` (new)

The trusted-computing-base crate arrives now, data-only. Per the TCB
rule it depends on **no workspace crate** (external deps: `num-bigint`
only). Contents:

- `Name` — anonymous | str | num; parent-linked, `Arc`-shared.
- `Level` — zero | succ | max | imax | param | mvar. Decoded faithfully;
  the checker (M1b) rejects metavariables, not the parser.
- `Expr` — bvar, fvar, mvar, sort, const, app, lam, forallE, letE,
  lit, mdata, proj. `Arc`-shared. Cached per-node metadata (hash,
  has-fvar flags) is an M1b concern; the representation must not
  preclude it.
- `Literal` — natVal (`num_bigint::BigUint`) | strVal.
- `ConstantInfo` — all eight kinds: axiom, def, theorem, opaque, quot,
  inductive, constructor, recursor; shared `ConstantVal` (name, level
  params, type) plus kind-specific payload (value, hints, inductive
  metadata, …) mirroring the oracle's structures.
- `Environment` — name → `ConstantInfo` map plus
  `Environment::from_modules(...)`, which merges decoded modules and
  errors on duplicate names.

### `leanr_olean` (extended)

Gains the object-graph decoder and a dependency on `leanr_kernel`
(dependency direction is olean → kernel, never the reverse).

The compacted region after the 64-byte header is a memory dump of Lean
runtime objects: real `lean_object` layouts, pointers rebased against
`base_addr`, scalars as tagged (odd) values. The decoder is one
schema-directed walk from the root `ModuleData` object (imports,
constant names, constants, extension entries), recursively decoding
fields as their types dictate: constructor objects, arrays, strings,
boxed scalars, bignums. All layout constants are verified against the
oracle source at the pinned tag and cited by file/line in comments,
extending the discipline the header parser established.

Decoding is **memoized on object offset**: shared subobjects decode
once and reuse the same `Arc`. This is load-bearing — expressions in
real `.olean`s are DAGs with massive sharing, and naive tree copying
explodes memory exponentially. Output size stays proportional to region
size.

Validation is total, because the bytes are untrusted
(`docs/THREAT_MODEL.md`):

- every pointer bounds-checked and alignment-checked before dereference;
- every object tag matched against the constructor set its schema
  position allows;
- cycles detected via the memo table (legitimate `.olean`s are acyclic;
  a crafted cyclic file must produce an error, not a hang);
- no code path panics on arbitrary bytes.

### `leanr_cli` (extended)

`leanr olean decls <path>` — decodes the module and lists declaration
names and kinds. Errors reuse the `olean info` rendering path. Still no
logic in the CLI beyond argument handling and printing.

## Error handling

`OleanError` grows structured variants for the decoder — at minimum
`BadPointer { offset }`, `BadTag`, `Cycle`, plus truncation/UTF-8
cases as implementation finds them. Human-readable messages, tested, no
panics.

## Testing

Four layers, extending M0's harness:

1. **Golden vs oracle.** `fixtures:regen` gains an oracle-side Lean
   script that dumps a module's constants (names + kinds) to a text
   fixture; `leanr olean decls` output must match it exactly. A second,
   meatier fixture module (inductives, structures, theorems) exercises
   all constant kinds.
2. **Property + fuzz.** The proptest "arbitrary bytes never panic"
   guarantee extends over the whole decoder in CI. A `cargo-fuzz`
   target on module parsing arrives for deeper local runs — fuzzing was
   deferred from M0 to exactly this parser.
3. **Stdlib sweep (local, non-CI).** `mise run sweep:stdlib` decodes
   every `.olean` shipped with the pinned toolchain (~2,500 modules,
   all of Lean core) and requires zero errors. CI cannot run it (no
   Lean toolchain in CI, by design); it is the contributor-side gate
   for decoder completeness.
4. **Sharing test.** Decoding a term with repeated subterms yields
   pointer-equal `Arc`s, guarding the memoization against silent
   regression.

## Demo deliverable

`leanr olean decls` on a real toolchain module (e.g. `Init.Nat`) lists
hundreds of declarations, matching the oracle's account of the module
exactly.

## Deferred (and where it lands)

- Type checker: defeq, whnf, inductive checking — M1b.
- Import-closure resolution and search paths — M1b.
- Parallel checking over Mathlib + Mathlib-scale sweep — M1 final slice.
- Env-extension interpretation — M4 (elaborator).
- Expr metadata caches (hash, flags) for defeq speed — M1b.
- Zero-copy loading — only if profiling ever shows load time matters.
