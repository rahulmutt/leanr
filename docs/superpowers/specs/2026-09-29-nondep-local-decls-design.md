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

## Landed

Measured against `main` (merge-base `08e90ac` after the rebase onto the
deps fix, ruling R10), branch `nondep-local-decls`, commits
`1d44aa2..HEAD`:

- Elaboration corpus 162 → 165, additions only (`git diff --numstat`:
  `3 0` on `elab-queries.jsonl`; `dump_elab.lean` `20 1` is the query
  list). Synthesis corpus and `tests/fixtures/meta`: byte-identical.
  `lean-toolchain` unbumped.
- `leanr_kernel`: `subst.rs | 240 +` and `lib.rs | 2 +-` only
  (`lower_loose_bvars`, its arms and tests, and the export).
- `leanr_meta`/`leanr_elab`: the `LocalEntry` rows, the eight consumers,
  and `has_loose_bvar`, as in § Design.
- Gate: per task, `mise run lint && mise run test && mise run
  scan:secrets` and `mise run meta:fast` (ruling R7). After the rebase
  onto the deps fix (R10), the full `mise run ci`, `lint:deps` included,
  passes.

### Mutations (each applied, run, watched go red, reverted)

| Mutation | Result | Killed by |
|---|---|---|
| `lower_go`'s `>=` to `>` (Task 1) | red | both `lower_loose_bvars` tests |
| Store `nondep: false` in `push_let_decl_with_kind` | red | both `local_entries_*` tests |
| Store `Default` for every kind (push path) | red | the stored-kind and `__`-binder install tests, and `oracle_elab_gate` |
| Same, in `install_local_instance_for_last_pushed` | red | the same two tests; `closeout/impl-detail-fun` and `-fun-inst` |
| Invert the `nondep` test in `whnf`'s fvar arm | red | `binder_smoke`'s `have … rfl` rejection test |
| Invert it in `simp_assignment_arg_aux` | red | its own test only |
| Invert it in `check_assignment_scope_body` | red | its own test only |
| Invert it in `mk_lambda_fvars_with_let_deps` | red | its own test only |
| Drop `isLet` from `mk_mvar_app` (and: treat a `have` as a `let`) | red | `mk_mvar_app_skips_a_let_but_applies_a_have` |
| Drop `generalizeNondepLet` | red | the depends-on test and `collect_forward_deps_honours_the_rows_nondep` |
| `collect_forward_deps` always passes `nondep = false` (added, ruling R4) | red | `collect_forward_deps_honours_the_rows_nondep` |
| `lift` where the drop arm wants `lower` | red | `drops_an_unused_let_and_lowers` (after ruling R5) |
| `has_loose_bvar` as `range > 0` | red | Task 2's index-one and `has_loose_bvar_shifts_under_a_binder` tests; Task 8's drop and opaque-unused tests |
| `has_loose_bvar` prunes on `range <= idx` without the saturation guard (final fix) | red | `has_loose_bvar_never_prunes_on_a_saturated_range` |
| Invert the `nondep` test at any one of the three `assign.rs` sites (final fix) | red | `a_have_is_a_pattern_argument_and_a_let_is_not` (each site) |
| Invert the `nondep` test in `whnf`'s fvar arm (final fix) | red | `zeta_delta_follows_a_let_but_not_a_have` |
| Report a refused `have` in `mk_binding` under the let message (final fix) | red | `mk_binding_names_a_refused_have_as_the_seam` |
| Drop the `has_loose_bvar` condition in the let arm | red | the same two Task 8 tests |
| nondep treated as false in the have arm | red | `turns_a_have_into_a_forall` |
| Lift only the body, not the whole `letE` | red | `lifts_a_used_let_under_a_forall_when_opaque` |
| syntheticOpaque treated as non-opaque; opaque-unused arm skipped; no lift in the opaque-used arm | red | the two opaque tests |
| Drop `elim_mvar_deps` from `mk_let_expr` | red | `nondep/let-coe` and `nondep/have-coe`; `a_coercion_postponed_under_a_let_abstracts_to_bvar_0` |

The spec's `zeta_unused` row is **withdrawn**: § Design 4's premise was
false (`consume_unused_let` performs no lowering; its branch requires a
closed body), so Task 5 was never dispatched and no test names it.

### Rulings made during execution

- **R1**: Task 2's test cites `mkAuxMVarType`'s unused-let arm
  (`MetavarContext.lean:1138`), not the withdrawn whnf claim.
- **R2**: `push_local_decl_without_instance` gained a `kind` parameter
  instead of a `_with_kind` twin.
- **R3**: the "store `Default`" mutation was also run on the deferred
  (`elab_fun`) path; it died, so no extra test was needed.
- **R4**: `local_decl_depends_on(ty, value, nondep, pf,
  generalize_nondep_let)` takes the oracle's shape; the caller passes
  the row's `nondep` and the literal `true` (oracle default, `:1037`).
- **R5**: Task 8's drop-unused-let test was strengthened (context
  `[c, l := Sort 0]`, `?m : c`, exact result `∀ c, #0`); the plan's
  closed-type test could not tell `lift` from `lower`.
- **R6**: push, PR and merge happen after the final whole-branch review.
- **R7**: the per-task gate excludes `lint:deps`, because `cargo deny`
  fails on the base commit with two unrelated advisories: RUSTSEC-2026-0285
  (rustls 0.23.41) and RUSTSEC-2026-0308 (salsa 0.23.0, via
  `leanr_query`). They block GitHub CI regardless of this slice and are
  handled in a separate commit/PR.
- **R8**: `have n := Nat.zero; (rfl : Eq n Nat.zero)` is pinned as
  `ElabError::StuckCoercion`, where the oracle throws "Type mismatch"
  eagerly. leanr postpones a coercion when the got-type has mvars; that
  divergence is pre-existing and out of scope. A future
  coercion-postponement fix flips the test's `matches!`.
- **R9**: `elim_mvar` passes `decl.kind`; the oracle passes
  `newMVarKind` (`syntheticOpaque` when `!isAssignable`, `:1195`). The
  two agree only because leanr has no mctx depth, so every mvar is
  assignable.
- **R10**: the R7 advisories were fixed on a separate branch off `main`
  (`cargo update -p rustls`; salsa 0.23 → 0.28.5 in `leanr_query`),
  merged first as PR #47 (`08e90ac`), and this branch was rebased onto
  it. A `deny.toml` ignore would have silenced a security advisory.
- **R11**: the final fix wave covers the review's Important 1 and 2 and
  minors 4-6. Minor 3 is parked (see the seams table): changing it
  risks moving corpora for no observable gain.

### Measurement finding (Task 4)

The plan's Step 1 probe (`support::elab_result`) was non-discriminating:
`elab_result` never synthesizes, so a postponed coercion is accepted
before AND after the `whnf` fix. Defeq did fail correctly. The real
evidence is the stashed-fix RED under `elab_and_synthesize` (term
accepted), GREEN with the fix.

### Other variants that differed from the plan

- Task 8 abstracts the type per arm as the oracle does (not eagerly up
  front): `abstract_range_aux` can mint mvars, so the drop arm, which
  abstracts nothing, must not. The oracle's elimApp caller is at
  `:1245-1246`, not `:1219-1221`.
- Task 9's seam test was renamed to
  `a_coercion_postponed_under_a_let_abstracts_to_bvar_0`; the leak pin
  is gone.

### Seams discovered or still open

| Seam | Owner |
|---|---|
| R8: eager oracle "Type mismatch" vs leanr's `StuckCoercion` | a coercion-postponement slice |
| R9: `elim_mvar` must compute `newMVarKind` once leanr gains mctx depth (`withNewMCtxDepth`), or the ldecl arms take the non-opaque branch for a non-assignable mvar | the slice adding mctx depth |
| `mk_aux_mvar_type`'s mvar arm does not mint a fresh binder name for an anonymous mvar user name (oracle `:1162`); pre-existing | first anonymous-mvar producer |
| "Genuine let" predicate repeated in `assign.rs`, `whnf.rs`, `mk_binding.rs`, with an inconsistent missing-row fallback (`mk_binding.rs` treats it as a let, the others do not); an `is_genuine_let` helper would unify | cleanup |
| `check_assignment`'s genuine-let branch returns false where the oracle's `checkFVar` recurses into the value (`ExprDefEq.lean:873`). Reachable: `?m =?= l`, `l` a genuine `let l := Nat.zero` outside `?m`'s context, is `true` (`?m := Nat.zero`) on the oracle with `zetaDelta` on or off; leanr reaches the same answer only with `zeta_delta` on (a later unfold of `l`) and answers `false` with it off. Pinned by `check_fvar_seam_shows_only_with_zeta_delta_off` | pre-existing; the slice porting `checkAssignmentAux` |
| `mk_binding` (`metactx.rs`) refuses a `have` in a cdecl telescope, where the oracle's `mkBinding` (`generalizeNondepLet := true`, `MetavarContext.lean:1330-1332`) builds a `.default` binder. Behaviour unchanged; the refusal now names a `have` separately so one reaching it is recognisable | the slice that needs ldecl telescopes in `mk_binding` |
| Minor 3, parked (R11): `transform_let` runs `elim_mvar_deps` once per let (via `mk_let_expr`); the oracle runs it once over all the fvars. Same instantiated terms, different aux-mvar count and ids | a later cleanup, if an aux-mvar id ever becomes observable |
| Deferred minors: `lower_go`'s silent saturation when `s < d`; untested bignum/`LetE`/`MData`/`Proj` arms of `lower_go` and `has_loose_bvar`; no ldecl-arm test with a beta-redex type; no `mk_let_expr` unit test for an unassigned mvar; push paths not transactional if `fvar_id_of` fails | cleanup |

Still open as § Seams and deferrals above: `withLocalInstances` reading
the stored kind, the `mk_binding` cdecl-telescope ldecl refusal (its
`have` case is in the table above), and the remaining oracle channels.
