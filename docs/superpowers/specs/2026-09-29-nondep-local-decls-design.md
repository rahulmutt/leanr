# `nondep` and `LocalDeclKind` on local declarations — design spec

## Where this sits

M4b-3 is complete and its close-out shipped (#45). The close-out's
§ Amendment 1 pinned a `let`-bound local instance leaking an
unabstracted `fvar` and blamed `mk_let_expr` skipping `elim_mvar_deps`,
which needs a `nondep` bit leanr's local declarations do not carry.

That diagnosis was wrong, and § Amendment 2 of
`2026-09-11-m4b3-closeout-design.md` records the correction: the
instance is solved eagerly and was simply never substituted into the
body. A one-line `instantiate_mvars` closed it (#46 @ `1ca8fd1`).

Scoping that fix found the divergence the amendment's *cause* paragraph
actually described, previously unobserved: a metavariable still
UNASSIGNED when a `let`/`have` closes. That one does need `nondep`, and
it is this slice. Along the way the same missing bit turned out to be
read by seven other sites, each of which is a live or latent divergence.

This slice ships no user-visible functionality. It removes one
wrong-term divergence, one accepts-what-Lean-rejects gap, and five
latent ones, and it stores the `LocalDeclKind` that M4b-4's match slice
needs.

## Evidence

Every row below was run, not read. leanr through
`elab_term_and_synthesize` on `main` @ `1ca8fd1`; the oracle through
`tests/fixtures/elab/dump_elab.lean` with its query list swapped, under
`LEAN_PATH=tests/fixtures/elab` against the committed `Elab0.olean`,
on the pinned `leanprover/lean4:v4.33.0-rc1`.

| Term | Oracle | leanr today |
|---|---|---|
| `let n : Nat := Nat.zero; pairW n Nat.zero` | `pairW Nat (Wrapper.mk Nat (bvar 0)) Nat.zero` | **`fvar`** in place of `bvar 0` |
| `have n : Nat := Nat.zero; pairW n Nat.zero` | same, `nd: true` | **`fvar`** |
| `fun (n : Nat) => pairW n Nat.zero` | `bvar 0` | `bvar 0` (correct) |
| `let n : Nat := Nat.zero; (rfl : Eq n Nat.zero)` | accepted, `@rfl Nat (bvar 0)` | accepted |
| `have n : Nat := Nat.zero; (rfl : Eq n Nat.zero)` | **rejected**, "Type mismatch" | to be measured; expected accepted (see § Risk) |

The first two are the slice's reason for existing: a `.coe`
metavariable postponed inside the body is unassigned when the `let`
closes, so instantiating cannot help and `mk_let_expr`'s bare
`abstract_fvars` leaks the let-bound `fvar`. The `fun` twin is correct
only because `mk_binding` runs `elim_mvar_deps`.

The last row is the `whnf` divergence: the oracle never zeta-delta
expands a `have`, so `n` is opaque and `rfl` does not typecheck. leanr
follows the value of every let-bound fvar.

**Citations are by symbol where a line could not be opened.** The C++
kernel sources do not ship with the toolchain, so the existing
`expr.cpp:448-460` style citation on `lift_loose_bvars` cannot be
verified locally; this spec cites `lower_loose_bvars` by name only.

## Scope

**In.** The storage, its producers, the eight consumers, two missing
expression primitives — one of which is a flagged, additive
`leanr_kernel` addition (§ Design 4) — and the `LocalDeclKind` storage
M4b-4 needs.

**Out.** M4b-4 constructs and the `withLocalInstances` port that will
read the stored kind; `mk_binding`'s existing "let-decl fvar in a cdecl
telescope" refusal (no measured producer — it stays until something
reaches it); `revert` / `preserveOrder` / `mvarIdsToAbstract` (no
producer in leanr); `numScopeArgs`; a kernel `LocalDecl` field (§ Design
1, rejected alternatives); `lean-toolchain` bump.

## Design

### 1. Storage: one attribute row per declaration

`MetaCtx::local_names` — already exactly one entry per
`push_local_decl`/`push_let_decl` call and asserted in lockstep with
`lctx.decls` at every push, checkpoint, restore and install — becomes a
vector of a named struct in its own module beside `local_instance.rs`:

```rust
pub(crate) struct LocalEntry {
    pub fvar: ExprId,          // unchanged
    pub name: Option<NameId>,  // unchanged
    pub id: NameId,            // NEW — the declaration's fvar id
    pub nondep: bool,          // NEW — false for every cdecl
    pub kind: LocalDeclKind,   // NEW — today a throwaway parameter
}
```

`id` is new so lookups compare by `NameId`, the basis
`LocalCtxSnapshot::reduced` already argues for over `ExprId`, without a
`Store` decode per read. It is decoded once at push via the existing
`MetaCtx::fvar_id_of`.

The same rows travel inside `LocalCtxSnapshot`, which is what a
metavariable stores as its own context. Every place that maintains the
lockstep — the `debug_assert` in `LocalCtxSnapshot::new`, the truncation
in `lctx_restore`, the swap in `install_lctx`, and `reduced`'s
filter-and-renumber — operates on the row vector wholesale, so widening
the row changes those signatures, not their logic. Rows stay
positional, so `local_instances`' `at_depth`-indexes-its-own-declaration
assertion is unaffected.

**Lookups.** Two accessors, each a reverse scan, the idiom
`lctx_lookup_by_name` already uses: `MetaCtx::local_entry(NameId)` for
the ambient context (`whnf`, `assign`), and
`LocalCtxSnapshot::entry(NameId)` for a metavariable's own context
(`mk_aux_mvar_type`, `mk_mvar_app`). Contexts are binder-depth-sized.
No hash index: it would be a second structure to hold in lockstep, for
a scan that is already the crate's idiom.

**Measured churn.** Outside `metactx.rs` and `local_snapshot.rs` there
is exactly ONE real reader of the rows — `instances.rs:1539`, a test
destructuring `(_, f)`. Every other mention of `local_names` in the
workspace is prose.

**Rejected alternatives.**

- *A second sparse side table keyed by fvar id, in the style of
  `local_instances`.* Least churn to existing readers, but these bits
  are not sparse — every declaration has a kind and every ldecl has a
  `nondep` — and it would invent a second depth-based truncation rule.
  `local_instance.rs`'s own module doc is the evidence for how subtle
  that rule is (truncate by recorded depth, renumber on reduce).
- *Fields on `leanr_kernel`'s `LocalDecl`.* O(1) through the existing
  `get`, no parallel structure. Rejected: that type ports the C++
  kernel's `local_ctx.h`, which has neither bit — they are
  `Lean.LocalDecl` (elaborator) concepts. The kernel does read let
  values during whnf (`is_let_fvar`, `tc.rs:1385`; `tc.rs:1544`), so
  the fields would sit there inert, which is what the real kernel does
  — but inert TCB fields invite a future kernel reader, and AGENTS.md
  keeps the kernel minimal.

### 2. Producers

`push_let_decl` / `push_let_decl_with_kind` gain a `non_dep`
parameter; `push_local_decl_inner` writes `nondep: false` and the
caller's kind. Every producer already has the bit:

| Producer | Source of `non_dep` |
|---|---|
| `leanr_elab`'s `push_user_let_decl` | `elab_let_like`'s own `non_dep` (`let` false, `have` true) |
| `infer.rs`'s let telescope | the `LetE` node's `non_dep` |
| `transform.rs`'s `transform_let` | the `LetE` node's (already collected into its `lets` vector) |
| `whnf.rs`'s `sunfold_go_let` | its own `non_dep` PARAMETER, which it currently drops |

`install_local_instance_for_last_pushed` stops taking `kind` and reads
the stored one. Its current doc says the caller "must pass it again
here because it is not stored"; that wart goes away. One caller, in
`leanr_elab`.

### 3. Consumers

Eight sites read a let-declaration today. Each gains the oracle's
`nondep` semantics.

| # | leanr site | Today | Oracle | Change |
|---|---|---|---|---|
| 1 | `MetaCtx::mk_let_expr` | bare `abstract_fvars` | `mkLetFVars` → `mkBinding` → `abstractRange`, i.e. elim-then-abstract | run `elim_mvar_deps(&[fvar], body)` first |
| 2 | `mk_aux_mvar_type` | refuses an ldecl in `to_revert` | the two ldecl arms, `MetavarContext.lean:1133-1156` | port both; take `kind` and `used_let_only` |
| 3 | `mk_mvar_app` | applies every fvar | `isLet` unless the kind is `syntheticOpaque` (`:1090-1097`) | a genuine `let` is NOT applied; a `have` is |
| 4 | `whnf_easy_cases`' fvar arm | follows every let value under `zeta_delta` | matches only `.ldecl (nondep := false)` | add the `nondep` test |
| 5 | `assign.rs`'s `simp_assignment_arg_aux` | expands any let value | `FVarId.getValue?`, `allowNondep := false` (`Meta/Basic.lean:1044`) | same |
| 6 | `assign.rs`'s `check_assignment_scope_body` | any valued decl is "a let" | `checkFVar` matches `.ldecl (nondep := false)`; a `have` is "locally a cdecl" (`ExprDefEq.lean:851-877`) | a `have` falls through to the in-scope test |
| 7 | `assign.rs`'s `mk_lambda_fvars_with_let_deps` | seams on any ldecl among `xs` | `hasLetDeclsInBetween` uses `isLet`, which excludes nondep (`ExprDefEq.lean:559-573`) | narrow the seam to genuine lets |
| 8 | `local_decl_depends_on` | always counts the value | `findLocalDeclDependsOn`: `generalizeNondepLet && nondep` → type only (`MetavarContext.lean:744-753`) | add the flag; leanr's only caller, `collect_forward_deps`, passes `true` — the oracle's own default at `:1037` |

Sites 2 and 3 need `kind` and `used_let_only` from `elim_mvar`. leanr
reaches them only through `elim_app`'s unassigned arm, where the oracle
passes `usedLetOnly := true` (`:1219-1221`), so that is a constant, not
a parameter chain. `revert`, the oracle's `usedLetOnly := false`
caller, has no leanr producer.

### 4. Two missing expression primitives

The ldecl arms need `hasLooseBVar e 0` (`Lean/Expr.lean:1330`) and
`lowerLooseBVars e 1 1` (`:1357`). leanr has neither; the
`syntheticOpaque` arm's `liftLooseBVars 0 1` already exists as the
exported `lift_loose_bvars`.

- **`has_loose_bvar(e, 0)`** — `leanr_meta`. `ExprData::loose_bvar_range`
  is `1 + max loose index` (saturating at `LOOSE_BVAR_SAT`), so
  `range > 0` means "some loose bvar", NOT "bvar 0 is loose". The exact
  test is a walk, with `range == 0` as a sound fast path. No kernel
  involvement: `loose_bvar_range_exact` is `pub(crate)` to the kernel,
  so the walk uses the public saturating accessor only.
- **`lower_loose_bvars(e, s, d)`** — `leanr_kernel`'s `subst.rs`, beside
  its existing twin `lift_loose_bvars`. Unlike `nondep`, this IS a
  kernel expression primitive in the C++ kernel, so the port stays
  faithful by having it there. Additive, with no caller inside the type
  checker, on the precedent of `LocalContext::erase` (added for
  `reduceLocalContext` on the same argument). **Flagged as a TCB edit**
  per AGENTS.md; user-approved 2026-09-29.

**A claimed approximation in `whnf`, WITHDRAWN before implementation.**
An earlier draft of this spec claimed `whnf`'s `zeta_unused` branch
used `loose_bvar_range() == 0` where the oracle used the singular
`!body.hasLooseBVar 0`, and the project owner approved fixing it here.
That claim was wrong, and the fix is withdrawn. The oracle's `whnfCore`
reads `cfg.zetaUnused && !b.hasLooseBVars` (`WHNF.lean:661`) — the
PLURAL predicate, `looseBVarRange > 0` (`Lean/Expr.lean:1312-1313`) —
and `consumeUnusedLet` (`:639-642`) tests the same plural predicate and
performs no lowering, which is sound precisely because the body is
closed. leanr's `whnf.rs:343` is `loose_bvar_range() == 0` and its
`consume_unused_let` does not lower: both are already exact.

The lesson is the standing one (`leanr-oracle-citations-unverified`): the
singular/plural distinction was inferred from the helper's name and not
read. The exact `has_loose_bvar` helper below is still required — the
oracle's `mkAuxMVarType` ldecl arm really does use the SINGULAR
`e.hasLooseBVar 0` (`MetavarContext.lean:1138`), which leanr cannot
express today.

### 5. The gap-2 fix itself

With storage and primitives in place:

- `mk_let_expr` runs `elim_mvar_deps` over the body before abstracting,
  matching `mkBinding`'s `abstractRange`. It keeps its `non_dep`
  parameter and its `usedLetOnly := false` / `generalizeNondepLet :=
  false` semantics — `elabLetDeclAux` passes exactly those
  (`Elab/Binders.lean:832`), which is why a `have` stays a `letE` with
  `nd: true` rather than becoming a lambda.
- `mk_aux_mvar_type`'s refusal is replaced by the oracle's arms, so the
  postponed coercion's auxiliary metavariable is typed correctly
  instead of erroring.
- `mk_mvar_app` consults `isLet`.

## Crate-boundary ledger

`leanr_meta`:

| Change | Shape |
|---|---|
| `LocalEntry` rows replace the `local_names` tuples | internal; one test call site outside the two owning files |
| `local_entry` / `entry` accessors on `MetaCtx` and `LocalCtxSnapshot` | additive |
| `push_let_decl*` gains `non_dep` | signature change, four producers |
| `install_local_instance_for_last_pushed` drops `kind` | signature change, one caller (`leanr_elab`) |
| `has_loose_bvar` | additive |
| Consumers 1-8 | **behaviour change**, each toward the oracle |

`leanr_kernel`: `lower_loose_bvars` only — additive, no caller inside
the checker, TCB-neutral, flagged above.

## Error handling

No new `MetaError` or `ElabError` variants. One error is RETIRED:
`mk_aux_mvar_type`'s "let-decl fvar in to_revert" refusal, replaced by
the ported arms. `mk_binding`'s separate "let-decl fvar in a cdecl
telescope" refusal stays (§ Scope).

## Verification

### Oracle records (`dump_elab.lean`)

A new `nondepQueries` group, appended so the corpus diff stays additions
only:

- `nondep/let-coe`, `nondep/have-coe` — `let`/`have n : Nat := Nat.zero;
  pairW n Nat.zero`. The gap-2 gate: both must emit
  `Wrapper.mk Nat (bvar 0)`. Neither can be committed before the fix —
  `oracle_elab`'s leaked-fvar assertion rejects them.
- `nondep/let-rfl` — `let n : Nat := Nat.zero; (rfl : Eq n Nat.zero)`,
  which pins that a genuine `let` stays TRANSPARENT after consumer 4,
  guarding against over-correcting into "no let value is ever followed".

### Unit tests

Rejections cannot be corpus records (the dumper emits nothing for a
failed elaboration), and the meta-tier corpus is Expr-level with no
local-context field, so these carry the rest:

- `leanr_elab`: `have n : Nat := Nat.zero; (rfl : Eq n Nat.zero)` is
  REJECTED (the variant is pinned after running it); the `let` twin
  still elaborates.
- `leanr_meta`, one per ldecl arm: nondep → `forall` with
  `BinderInfo::Default`; used genuine let → `letE`; unused genuine let →
  lowered by one; `syntheticOpaque` → lifted, then `forall`.
- `leanr_meta`: `mk_mvar_app` applies a `have` and skips a `let`.
- `leanr_meta`: `local_decl_depends_on` ignores a nondep decl's value
  under the flag and counts it without.
- `leanr_meta`: consumers 5, 6 and 7, each with a `have` and a `let`.
- `leanr_meta`: `has_loose_bvar` against hand-built terms, including the
  case that motivates it — a term whose packed range is nonzero while
  bvar 0 is NOT loose. (There is no `zeta_unused` test: that fix was
  withdrawn, § Design 4.)
- `leanr_meta`: rows survive `lctx_restore`, `install_lctx` and
  `reduced`; a `__`-named binder's stored kind still suppresses the
  local-instance install (the close-out's behaviour, now read from
  storage rather than a parameter).
- `seam_audit.rs`: `a_coercion_postponed_under_a_let_leaks_an_fvar` is
  FLIPPED to the oracle's `bvar 0` and renamed.

### Mutations (each run, each recorded in its task report)

| Mutation | Must fail |
|---|---|
| Drop `elim_mvar_deps` from `mk_let_expr` | the two `nondep/*-coe` records |
| Invert the `nondep` test in `whnf` | the `have … rfl` rejection test |
| Invert it in consumers 5, 6, 7 | that consumer's own test |
| Drop `isLet` from `mk_mvar_app` | the apply/skip test |
| Drop `generalizeNondepLet` | the depends-on test |
| Use `lift` where the arm wants `lower` | the unused-let arm test |
| Use `range > 0` for `has_loose_bvar` | the exact-test case and the `zeta_unused` test |
| Store `Default` for every kind | the `__`-binder install test and the `closeout/impl-detail-*` records |

### Branch gate

- Elaboration corpus: 162 → 165, additions only.
- Synthesis corpus (32) and meta corpus: byte-identical.
- `leanr_kernel` diff: `lower_loose_bvars` and its tests, nothing else.
- `lean-toolchain` unbumped; `Elab0.lean` unchanged unless a record
  needs a constant it lacks, which would land in its own fixture-only
  commit re-checking every existing record (the P5 Task 0 precedent).
- `mise run ci` before every push.

## Risk

**The behaviour changes are broad.** Consumers 4-8 touch reduction and
unification for every let-bound variable, not only the terms in
§ Evidence. The corpora are the gate: apart from the three new records
they must not move. If any committed record changes, that is a finding
to bring back to the project owner, not something to absorb into this
slice.

**One row of § Evidence is unmeasured on leanr**: that leanr today
ACCEPTS `have n : Nat := Nat.zero; (rfl : Eq n Nat.zero)`. It follows
from `whnf` following every let value, but it was not run. The
implementation's first task measures it; if leanr already rejects it,
consumer 4's discriminator is wrong and the test must be redesigned
before the fix lands.

## Seams and deferrals

| Seam | Owner |
|---|---|
| `withLocalInstances` reading the stored kind (`Match.lean:826`) | M4b-4's match slice |
| `mk_binding`'s cdecl-telescope ldecl refusal | the slice that measures a producer |
| `revert` / `preserveOrder` / `mvarIdsToAbstract` / `numScopeArgs` | no producer in leanr |
| `zetaDeltaSet` / `trackZetaDelta` / `isImplementationDetail` channels in `whnf` | the slice that gives `leanr_meta` elaborator context |
| `get_instances` re-entrancy (latent) | first environment carrying matchers |

## Next step

Implementation plan via the writing-plans skill, then M4b-4.
