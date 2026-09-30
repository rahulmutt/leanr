# M4b-4b — the anonymous constructor `⟨⟩` — design spec

## Where this sits

M4b-4 was split into independent specs
(`2026-09-29-m4b4-dot-notation-design.md`, § Where this sits). M4b-4a
(dot notation, LVals, term-level postponement) shipped as #49–#52. This
spec covers **M4b-4b**, the anonymous constructor. M4b-4c (`elabAsElim`)
still needs its own spec.

On `main` @ `6dcee4e`, `Lean.Parser.Term.anonymousCtor` is parsed
(`leanr_syntax` `builtin/term.rs`) but deliberately unrouted.
`seam_audit.rs`'s `unregistered_kinds_are_named_by_kind` pins that.

Pinned oracle: `leanprover/lean4:v4.33.0-rc1`. The oracle is
`elabAnonymousCtor`,
`src/lean/Lean/Elab/BuiltinNotation.lean:43-102`, opened while writing
this spec. The pin is not bumped.

## Evidence

These results were run, not read. Each term was checked with `#check`
under `pp.all` using the pinned `lean`, in a scratch `prelude` file
that imports `tests/fixtures/elab/Elab0.olean` and declares any missing
types locally.

| Term | Oracle |
|---|---|
| `(⟨Nat.zero, Nat.zero⟩ : Prod Nat Nat)` | `@Prod.mk.{0,0} Nat Nat Nat.zero Nat.zero` |
| `(⟨z, z, z⟩ : Prod Nat (Prod Nat Nat))` | `@Prod.mk … Nat.zero (@Prod.mk … Nat.zero Nat.zero)` (flattened) |
| `(⟨z, z, z, z⟩ : Prod Nat (Prod Nat (Prod Nat Nat)))` | flattened twice |
| `(⟨z, ⟨z, z⟩⟩ : Prod Nat (Prod Nat Nat))` | same term as the single flatten |
| `(⟨Nat.zero⟩ : ImpI)`, `ImpI.mk {n : Nat} (x : Nat)` | `@ImpI.mk ?m Nat.zero` (implicit field not counted) |
| `(⟨z, Eq.refl z⟩ : Exists (fun n : Nat => Eq n z))` | `@Exists.intro.{1} Nat (fun n => …) Nat.zero (@Eq.refl.{1} Nat Nat.zero)` |
| `(⟨True.intro, True.intro⟩ : And True True)` | `@And.intro True True True.intro True.intro` |
| `(⟨⟩ : PUnit)` | `PUnit.unit.{u_1}` |
| `(⟨⟩ : Unit)` (`abbrev Unit := PUnit`) | `PUnit.unit.{1}`: `whnf` unfolds the alias before the inductive check |
| `(⟨z, z, z⟩ : S3Alias)` (`S3 extends S2`) | app type mismatch: `S3.mk`'s explicit fields are `toS2` and `c` (k = 2), so the first `z` is checked against `S2`. Parent fields are not flattened. |
| `sameAs ⟨z, z⟩ (Prod.mk z z)` | succeeds: top-level postpone, resumed after `?α := Prod Nat Nat` |
| `sameAs (⟨z, z, z⟩ : Prod Nat _) (Prod.mk z (Prod.mk z z))` | succeeds: the flatten **tail** postpones on `?β` and resumes |
| `Prod.fst ⟨z, z⟩` | `@Prod.fst … (@Prod.mk … Nat.zero Nat.zero)` |
| `⟨z, z⟩` (no expected type) | "The expected type of this term could not be determined" |
| `(⟨z, z, z⟩ : Prod Nat _)` | the same error, reported at the **outer** `⟨` column: the tail's ref is the outer node |
| `(⟨z⟩ : Nat → Nat)` | "The expected type `Nat → Nat` is not an inductive type" |
| `(⟨⟩ : Empty)` | "… has no constructors" |
| `(⟨⟩ : Bool)` | "… has more than one constructor" |
| `(⟨z⟩ : Prod Nat Nat)` | "Insufficient number of fields … `Prod.mk` has 2 explicit field, but only 1 was provided" |
| `(⟨z, z, z⟩ : Prod Nat T3)`, `T3` with 3 fields | the same error from the **nested** tail: "`T3.mk` has 3 explicit field, but only 2 were provided" |
| `(⟨z, z⟩ : Prod Nat (Prod Nat (Prod Nat Nat)))` | n = k: an application type mismatch from the app elaborator, no flattening |
| `(⟨z⟩ : True)` | "Constructor `True.intro` does not have explicit fields, but 1 was provided" |
| `(⟨⟩ : Eq Nat.zero Nat.zero)` | **Type mismatch** `@Eq.refl ?α : ∀ (a : ?α), Eq a a`. Elab0's `Eq` index is promoted to a parameter, so `numParams = 2` and k = 0. It is not `InsufficientFields`. |
| `(⟨z⟩ : PrivMk)`, private `mk`, same module | succeeds (`_private.Anon.0.PrivMk.mk`), because the constructor is accessible there |
| `match p with \| ⟨a, b⟩ => a` | pattern position: belongs to the matcher, not this elaborator |

leanr today: every row raises `UnsupportedSyntax("Lean.Parser.Term.anonymousCtor")`.

## Scope

In scope:
- The term-position `anonymousCtor` elaborator, ported step by step.
- The flatten "tail" syntax form, and carrying it through `Arg` and
  term-level postponement.
- A typed error family for the notation's own errors.
- Fixture declarations, corpus records, smoke tests, audit updates.

Out of scope:
- `⟨⟩` in patterns (`fun ⟨a, b⟩ =>`, `match`), which belongs to the
  match slice in later M4. Its current seam stays and is pinned.
- A general synthesized-syntax representation, which belongs to the
  macro-expansion slice (`binop%` et al.). See § The tail form for why
  this slice does not pre-build it.
- Private-name accessibility, which stays under the existing
  crate-wide seam.

## Architecture

Only `leanr_elab` changes. `leanr_meta`, `leanr_syntax` and
`leanr_olean` are untouched. `whnf`, `forall_telescope_reducing` and
the inductive/constructor `ConstantInfo` data are already exposed.

### `builtin/anon_ctor.rs` — the elaborator

This file adds
`elab_anon_ctor(elab, node: &SyntaxNode, from: usize, kinds, expected)`.
The dispatch arm for `Lean.Parser.Term.anonymousCtor` calls it with
`from = 0`. The args are the node's `non_trivia_children` inner list
with the `,` separators dropped, and the function uses `args[from..]`.
Let n = `|args[from..]|`.

Control flow, with oracle lines from `BuiltinNotation.lean`:

1. `:46`: `try_postpone_if_none_or_mvar(expected)`. If postponement is
   not allowed this falls through, and `expected = None` raises
   `ExpectedTypeUnknown` (`:101`).
2. `:53-54`: `whnf` at default transparency. If the app head is still
   an mvar, raise `ExpectedTypeUnknown`. This is a hard error, not a
   second postponement.
3. `:55-57`: the head must be `Const` naming an inductive, otherwise
   `NotInductive { ty }`. Structures, classes and non-structure
   inductives (`Exists`) all pass.
4. `:59`, `:98-99`: zero constructors raises `NoCtors { ty }`. More than
   one raises `MultipleCtors { ty }`.
5. `:61-62`: a constructor name starting with `_private.` raises
   `UnsupportedSyntax`, naming the private-names slice. This is the
   same seam as `app/lval.rs` (`App.lean:1860`) and `app/dot_ident.rs`
   (`App.lean:2024`). **Narrowing:** the oracle accepts a private
   constructor from its own module (see § Evidence).
6. `:64-69`: k = the number of `BinderInfo::Default` binders at
   positions `numParams..` of `forall_telescope_reducing(ctor.type)`.
7. Branch in the oracle's order:
   - n < k: `InsufficientFields { ctor, explicit: k, provided: n }`
     (`:71-85`). **Narrowing:** under `errToSorry` the oracle logs this
     and pads with labeled `sorry`s. leanr has no `errToSorry` and
     throws, following the same precedent as `app/args.rs`'s
     `ensureArgType` note. The dumper drops logged-error queries, so no
     corpus record can see the difference.
   - n = k: every arg is `Arg::Stx`.
   - k = 0 (with n > 0): `NoExplicitFields { ctor, provided: n }`
     (`:88-91`).
   - otherwise: `args[from .. from+k-1]` become `Arg::Stx`, and the
     last arg is `Arg::AnonCtorTail { node, from: from + k - 1 }`
     (`:93-96`). The tail always has at least 2 args.
8. `:97`: `app::elab_app_args(mk_const(ctor, &[]), AppCall { named_args:
   [], args, expected, explicit: false, ellipsis: false, stx: node })`.

   Calling `mk_const` directly is faithful to `mkCIdentFrom stx ctor
   (canonical := true)` (`Init/Meta/Defs.lean:736-739`). That ident
   carries a reserved macro scope and `[.decl ctor []]`, so
   `resolveName`'s `resolveLocalName` (`TermElabM.lean:2180`) can never
   capture it, and the preresolved decl becomes `mkConst` with fresh
   level mvars. leanr models no section-variable capture (`:2187`).

   `withMacroExpansion` has no counterpart, because leanr has no macro
   stack.

### The tail form

The oracle recurses through synthesized syntax `⟨$[$extra],*⟩`. leanr
elaborates rowan `SynElem`s, and no real node covers "args i..n of this
`⟨⟩`". The tail is represented as **the outer node plus a start index**.
Every nesting level shares the same outer node and only moves `from`
forward.

A crate-private type in `elab.rs`:

```rust
enum TermTarget {
    Stx(SynElem),
    AnonCtorTail { node: SyntaxNode, from: usize },
}
```

- `ref_elem()` returns the outer node for the tail. This is what the
  oracle sees too: the synthesized node has kind `anonymousCtor` and
  `SourceInfo.fromRef` the outer node, which § Evidence confirms (the
  error column). So `use_implicit_lambda`/`block_implicit_lambda`, the
  postponement ref, `ensure_has_type`'s ref and `report.rs`'s range
  ordering all receive the outer node.
- `elab_term_core`, `elab_using_elab_fns`, `elab_implicit_lambda` and
  `postpone_elab_term` take a `TermTarget`. The public `elab_term*`
  signatures keep `&SynElem` and wrap it in `TermTarget::Stx`.
  Dispatching `AnonCtorTail` goes straight to `elab_anon_ctor(node,
  from)`.
- `Arg::AnonCtorTail { node, from }` (`app/expand.rs`). Its match
  sites:
  - `should_propagate_expected_type_for`: true (the kind is not
    `hole`/`syntheticHole`/`byTactic`).
  - `next_arg_hole`: `None`.
  - `elab_and_add_new_arg`: elaborates the tail target, with `node` as
    the `ensure_has_type` ref.
- `SyntheticMVarKind::Postponed { ctx, tail_from: Option<usize> }`.
  `postpone_elab_term` sets `tail_from` from the target, and
  `resume_postponed` rebuilds `TermTarget` from
  `(decl.stx, tail_from)`. A tail postponed on `?β` therefore resumes
  as the tail, not as the whole `⟨⟩`. `report.rs`'s `Postponed` arm
  ignores the new field.

This is deliberately narrow. The macro-expansion slice will need a
general synthesized-syntax type, and at that point `TermTarget` is the
place to grow it. Pre-building it here would widen every `elab_term`
signature for a single producer. A detached rowan green node was
rejected because its text ranges restart at 0: that is a silent
position divergence rather than a named one.

## Errors

`ElabError::InvalidAnonymousCtor(AnonCtorError)`, with:

| Variant | Oracle |
|---|---|
| `ExpectedTypeUnknown` | `:47-48`, raised at `:54` and `:101` |
| `NotInductive { ty }` | `:56-57` |
| `NoCtors { ty }` | `:98` |
| `MultipleCtors { ty }` | `:99-100` |
| `InsufficientFields { ctor, explicit, provided }` | `:77-82` |
| `NoExplicitFields { ctor, provided }` | `:89-91` |

All six are `is_oracle_error` (they are `throwError`s), so a resumed
postponement under `postponeOnError` catches them. The prose is not
ported. The oracle's inverted pluralization ("has 2 explicit field")
is a prose bug and does not matter here.

## Fixture

These are added to `tests/fixtures/elab/Elab0.lean` (prelude-safe):
- `structure And (a b : Prop) : Prop` (`intro ::`, on its own line)
- `inductive Exists {α : Sort u} (p : α → Prop) : Prop`
- `inductive True : Prop`
- `inductive Empty : Type`
- `inductive ImpI | mk {n : Nat} (x : Nat)`
- `structure T3` with three `Nat` fields
- `structure PrivMk` with `private mk ::`
- `def sameAs {α : Type} (a b : α) : α := b`

The fixtures are regenerated with `mise run fixtures:regen`. Each new
name is first checked against existing Elab0 names and
`seam_audit`'s undecoded-attribute gate.

## Testing

**Corpus** (`elab-queries.jsonl`, success paths only):
`anon/prod`, `anon/flat1`, `anon/flat2`, `anon/nestedExplicit`,
`anon/implicitField`, `anon/exists`, `anon/and`, `anon/punit`, `anon/unitAlias`,
`anon/postponed`, `anon/tailPostponed`, `anon/arg`, with the sources
in § Evidence. `anon/tailPostponed` is the only record that exercises
the `tail_from` resume.

**Smoke** (`tests/anon_ctor_smoke.rs`): one test per `AnonCtorError`
variant, with the § Evidence term and the oracle's message quoted in a
comment:
- `ExpectedTypeUnknown`, both bare and from the unresolved tail
- `NotInductive`, `NoCtors`, `MultipleCtors`
- `InsufficientFields`, both top-level and nested (`T3`)
- `NoExplicitFields`
- `(⟨⟩ : Eq Nat.zero Nat.zero)` giving `TypeMismatch` and **not**
  `InsufficientFields`
- `PrivMk` giving the private-names seam

**`seam_audit`:**
- Drop `anonymousCtor` from `unregistered_kinds_are_named_by_kind`.
- Pin that pattern-position `⟨⟩` (`fun ⟨a, b⟩ => a`) still raises its
  named seam.
- Add an `M4b-4b` needle to `no_seam_message_names_a_completed_slice`,
  measured non-vacuous.

**Mutations.** Each of these must turn at least one test red, run
before the final check rather than trusted from the plan:

| Mutation | Killed by |
|---|---|
| `from + k - 1` → `from + k` | `anon/flat1` |
| resume ignores `tail_from` (resumes the whole node) | `anon/tailPostponed` |
| skip `whnf` | `anon/unitAlias` (`Unit` is a def, not an inductive) |
| count every binder, not just explicit ones | `anon/implicitField` |
| count from 0 instead of `numParams` | the `Eq` smoke test |
| check `k = 0` before `n < k` | the `True` / `Prod` smoke tests |
| recurse with `from` unchanged | `anon/flat2` |

**Gates:** `mise run ci` (fmt, clippy, tests, deps) green before merge.

## Delivery

One plan, one PR. Tasks, in order:
1. Fixture and corpus.
2. `TermTarget` threading, with no behaviour change.
3. The elaborator and dispatch arm.
4. Errors and smoke tests.
5. The audit and the mutation sweep.
