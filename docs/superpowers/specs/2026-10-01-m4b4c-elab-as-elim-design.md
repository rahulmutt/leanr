# M4b-4c — eliminator elaboration (`elabAsElim`) — design spec

## Where this sits

M4b-4 was split into independent specs
(`2026-09-29-m4b4-dot-notation-design.md`, § Where this sits). M4b-4a
(dot notation, LVals, postponement, ident forms) shipped as #49–#52, and
M4b-4b (`⟨⟩`) shipped as #53. This spec covers **M4b-4c**, the last
piece. When it lands, M4b-4 is complete.

On `main` @ `198e73e`, `elabAppArgs`' eliminator branch is a **partial
seam** (`crates/leanr_elab/src/app/mod.rs:510-548`):

- `isRec` heads raise a named M4b-4c seam (`app/head.rs`,
  `recursor_head_seam`). The guard sits in two places that both have to
  be lifted: `elab_app_fn_id`'s `heed` gate and the dotIdent head
  (`head.rs:157`).
- The other four `shouldElabAsElim` disjuncts are **unguarded**:
  `isCasesOnRecursor`, `isRecOnRecursor`, `isBRecOnRecursor`, and the
  `@[elab_as_elim]` tag. Those heads take the ordinary path and emit a
  term the oracle does not. Two gates keep that divergence out of the
  corpus: `seam_audit.rs`'s
  `fixture_declares_no_undecoded_elab_attributes` bans eliminator names
  and the attribute.

Pinned oracle: `leanprover/lean4:v4.33.0-rc1`. These sources were opened
while writing this spec:

- `src/lean/Lean/Elab/App.lean`:
  - `ElabElimInfo`: `:976-1004`
  - `getElabElimExprInfo`: `:1006-1050`
  - `getElabElimInfo`: `:1052-1053`
  - `elabAsElim` attribute: `:1123-1138`
  - `ElabElim`: `:1140-1319`
  - `shouldElabAsElim`: `:1322-1328`
  - `elabAppArgs` diversion: `:1373-1383`
  - `elabAsElim?`: `:1397-1431`
- `src/lean/Lean/AuxRecursor.lean:20-51`
- `src/lean/Lean/Meta/KAbstract.lean`
- `src/lean/Lean/EnvExtension.lean:92-102` (`mkTagDeclarationExtension`)
- `src/lean/Lean/Attributes.lean:180-215` (`registerTagAttribute`)

Every line citation that goes into code comments is re-checked against
that source during review. Earlier citations have been off by 1-2 lines.

The pin is not bumped.

## Evidence

These were run, not read. Each term was checked with `#check` under
`pp.all` using the pinned `lean`, in scratch `prelude` files that import
`tests/fixtures/elab/Elab0.olean`. The second file also declares
`inductive False : Prop`, `@[elab_as_elim] theorem Eq.subst'`, and
`@[elab_as_elim] noncomputable def natElim` with the motive implicit.

| Term | Oracle |
|---|---|
| `(Nat.rec Nat.zero (fun _ ih => Nat.succ ih) n : Nat)` | `@Nat.rec.{1} (fun x => Nat) Nat.zero (fun x ih => Nat.succ ih) n`. The motive comes from `kabstract`ing `n` out of `Nat`. |
| `(Nat.casesOn n Nat.zero (fun m => m) : Nat)` | `@Nat.casesOn.{1} (fun x => Nat) n …`. Aux recursor, no attribute. |
| `(Nat.recOn n …)`, `(Nat.brecOn n (fun _ _ => Nat.zero) : Nat)` | Same shape. `brecOn`'s minor premise gets `@Nat.below.{1} (fun x => Nat) x`. |
| `Nat.rec Nat.zero (fun _ ih => ih) n`, no expected type | error `failed to elaborate eliminator, expected type is not available` |
| `Nat.rec (motive := fun _ => Nat) …`, `@Nat.rec (fun _ => Nat) …` | Standard path: a named motive or `@` opts out. Same term. |
| `(Nat.rec _ Nat.zero (fun _ ih => ih) n : Nat)` | **Application type mismatch.** `Nat.rec`'s motive is *implicit*, so the `_` is the `zero` minor. The "positional `_` motive" rule applies only to an **explicit** motive. |
| `(h.rec : Nat)`, `(False.rec _ h : Nat)`, `(False.rec (fun _ => Nat) h : Nat)`, with `h : False` | All three give `False.rec.{1} (fun x => Nat) h`. The first two take ElabElim (missing motive, or positional `_`); the third takes the standard path. |
| `(False.rec h : Nat)` | Standard path (the positional motive is not `_`), then app type mismatch: `h` is checked against the motive type. |
| `(Eq.subst' h p : Eq a b)` (tagged) | `@Eq.subst'.{1} Nat (fun x => @Eq Nat a x) a b h p`. `h` is a major via the first-order rule. |
| `(natElim Nat.zero (fun _ ih => ih) : Nat → Nat)` (tagged, under-applied) | `fun n => @natElim.{1} (fun x => Nat) … n`: the `forallTelescope` + `mkLambdaFVars` path. |

On the wire, checked with `readModuleData` on a compiled scratch
module:

- `Lean.auxRecExt` and `Lean.Elab.Term.elabAsElim` are each an array of
  `Name`, sorted by `Name.quickLt`.
- Each module holds **only its own** declarations
  (`addImportedFn := fun _ => {}`), so leanr unions the entries over the
  import closure.
- `Elab0.olean` has 152 `auxRecExt` entries.
- A Prop inductive (`False`) tags only `casesOn` and `recOn`.

## Scope

In scope:

- All five `shouldElabAsElim` disjuncts, decided exactly. This includes
  `isAuxRecursor`'s hard-coded `Eq.ndrec` / `Eq.ndrec_symm` /
  `Eq.ndrecOn`, and the `suffix` / `suffix_…` test
  (`AuxRecursor.lean:39-42`).
- The `elabAsElim?` gate and the `elabAppArgs` diversion.
- `ElabElim.main`, `finalize`, `revertArgs`, and `mkMotive`, including
  under- and over-application.
- Lifting both recursor seams, and inverting the `seam_audit` gates
  that excluded eliminators.

Out of scope, recorded under § Seams when the work lands:

- `@[elab_without_expected_type]`. It is still undecoded, and its
  `seam_audit` ban stays.
- `kabstract` `Occurrences` other than `.all`. `ElabElim` uses only
  `.all`.
- `trace[Elab.app.elab_as_elim]`.
- The `numScopeArgs` gap from M4b-4a P2, if an eliminator query hits
  it. It gets recorded, not fixed here.

## Decisions

- **Decode both extensions (option A).** Rejected alternatives:
  - B: infer aux recursors from the name suffix plus the parent
    inductive. That is a heuristic, and it is wrong for a user-declared
    `T.recOn` under `genRecOn false`.
  - C: leave `@[elab_as_elim]` seamed. That contradicts M4b-4c owning
    the whole `shouldElabAsElim`.
- **`get_elab_elim_info` lives in leanr_elab** (`app/elim_info.rs`). The
  oracle defines it in `Elab/App.lean`, and it needs nothing beyond
  telescopes and `collect_fvars`.
- **`kabstract` lives in leanr_meta** (`kabstract.rs`). It is a new
  algorithm, not an accessor, and is flagged under the
  accessor-precedent rule. It is additive, TCB-neutral (no kernel or
  olean change), and behavior-neutral: no existing caller changes.
- **Two plans, one PR each** (§ Delivery).

## Architecture

### P1 — leanr_olean: two typed decodes

`ModuleData` gains:

- `aux_rec_entries: Vec<Name>` from `Lean.auxRecExt`
- `elab_as_elim_entries: Vec<Name>` from `Lean.Elab.Term.elabAsElim`

They sit next to the existing typed decodes (parser, matcher,
`instanceExtension`, `defaultInstanceExtension`). They decode the same
way: a bare array of `Name`. The bytes are untrusted
(`docs/THREAT_MODEL.md`), so a malformed entry is a decode error, never
a panic. The existing `ModuleData` fuzz and property targets cover the
two new fields.

### P1 — leanr_meta: environment predicates

At load, `MetaCtx` builds `aux_rec: HashSet<NameId>` and
`elab_as_elim: HashSet<NameId>` over the import closure, the same way
it builds `reducibility`. Public predicates, each a verbatim port:

- `is_aux_recursor(n)`: set membership, or `n` is `Eq.ndrec`,
  `Eq.ndrec_symm` or `Eq.ndrecOn`.
- `is_aux_recursor_with_suffix(n, sfx)`: `n` is `.str _ s` with
  `s == sfx || s.starts_with(sfx + "_")`, and `is_aux_recursor(n)`.
- `is_cases_on_recursor`, `is_rec_on_recursor`, `is_brec_on_recursor`.
- `has_elab_as_elim_tag(n)`.

### P1 — leanr_meta: `kabstract(e, p)`

This ports `KAbstract.lean` for `Occurrences.all`:

1. `e ← instantiateMVars e`.
2. If `p` is an fvar, return `e.abstract #[p]`.
3. Otherwise compute `p`'s `HeadIndex` and `headNumArgs`, then walk
   `e`, tracking the binder offset:
   - A subterm with loose bvars, or whose head index or argument count
     differs from `p`'s, is not tested; its children are visited.
   - Otherwise, if `isDefEq e p` succeeds, return `bvar offset`. If it
     fails, visit the children.
   - The child-visit order is the oracle's: `app` visits f then a;
     `letE` visits t, v, then b+1; binders visit the domain, then the
     body at +1. Both `isDefEq` side effects and the result depend on
     this order.

The mctx save/rollback is dead under `.all`, since every match is
included. The port leaves it out, with a comment saying so.

`HeadIndex` and `headNumArgs`: if `discr_path.rs` already has an
equivalent, extract it into a shared module rather than duplicate it.

### P1 — leanr_elab: `get_elab_elim_info(name)`

Ports `getElabElimExprInfo` (`app/elim_info.rs`). It returns
`ElabElimInfo { elim_expr, elim_type, motive_pos, majors_pos }`:

1. `mk_const_with_fresh_mvar_levels(name)`, then a reducing forall
   telescope over its type.
2. Run the motive checks, each with its own oracle error:
   - The result's head is an fvar with at least one argument, else
     "unexpected eliminator resulting type".
   - The motive's own telescope arity equals its argument count, else
     "unexpected number of arguments at motive type".
   - The motive's result is a sort, else "motive result type must be a
     sort".
   - The motive is one of the telescope's fvars, else "unexpected
     eliminator type".
3. Compute `motive_fvars`: the fvars of the motive's arguments, closed
   in reverse telescope order under "collect the fvars of the type of an
   fvar already in the set".
4. Compute `majors_pos`: every `i != motive_pos` such that `x_i` is in
   `motive_fvars`, or `x_i`'s type is first-order (every application is
   headed by a constant) and mentions an fvar in `motive_fvars`.

P1 ships **no elaborator-visible change**: the guards stay as they are.

### P2 — the gate: `app/elim.rs::elab_as_elim_info`

Ports `elabAsElim?` (`App.lean:1397-1431`). It returns `None` (standard
path) when any of these holds:

- `!heed_elab_as_elim`
- `explicit || ellipsis`
- the head is not `.const`
- `!should_elab_as_elim(name)`

`should_elab_as_elim` checks `isRec`, then `is_cases_on_recursor`,
`is_brec_on_recursor`, `is_rec_on_recursor`, and `has_elab_as_elim_tag`,
in that order.

Otherwise it calls `get_elab_elim_info`, runs a reducing telescope over
`f`'s type, and simulates argument consumption for the binders before
`motive_pos`:

- a named argument with the binder's user name is erased from the named
  arguments;
- otherwise an explicit binder drops one positional argument.

At the motive binder:

- a named argument for it → `None`;
- the binder is explicit and the next positional is `.expr` → `None`;
- the binder is explicit and the next positional is syntax not of kind
  `Lean.Parser.Term.hole` → `None`;
- anything else → `Some(info)`.

The last case includes an implicit motive and an explicit motive that
is missing or a positional `_`.

### P2 — the diversion in `elab_app_args`

This goes at the oracle's point, after `try_postpone_if_mvar(f_type)`,
and replaces the comment block at `app/mod.rs:510-548`. When the gate
returns `Some(info)`:

1. `try_postpone_if_none_or_mvar(expected)`.
2. No expected type → error `failed to elaborate eliminator, expected
   type is not available`.
3. `expected ← instantiateMVars expected`. If its head is an mvar, raise
   the same error.
4. Run `ElabElim::main` and return its result. `AppElab` is not
   constructed.

Seam removal:

- `recursor_head_seam` is deleted.
- `elab_app_fn_id`'s `heed` stays, because it is the oracle's own gate,
  but now it only feeds `heed_elab_as_elim`.
- The dotIdent head (`head.rs:157`) no longer seams. It reaches the gate
  like any other `.const` head.

### P2 — `ElabElim` (`app/elim.rs`)

`ElabElim` is a separate machine,
`ElimElab { ctx: { info, expected }, st: { f, f_type, named_args, args,
inst_mvars, idx, motive } }`. It does not extend `AppElab`: the
oracle's `ElabElim.M` has its own state, and sharing it would blur
`idx` and the motive bookkeeping.

**`get_next_arg(binder_name, bi)`**:

- a matching named argument is erased and returned as `Some`;
- else an explicit binder pops a positional argument (`Some`), or
  returns `Undef` if none are left;
- else `None`.

**`main`** loops on `whnfForall(f_type)`. A non-`forallE` type goes to
`finalize`. For each binder:

- **`idx == motive_pos`**:
  - `Some(arg)` → `elab_arg(arg, binder_type)`;
  - `None | Undef` → `mk_implicit_arg`. `Undef` is what makes
    `h.rec` work.

  Then `set_motive`.
- **`idx ∈ majors_pos`**:
  - `Some` → elaborate eagerly;
  - `Undef` → `finalize`;
  - `None` → `mk_implicit_arg`.
- **Otherwise**:
  - `Some(.stx)` → `postpone_elab_term(stx, binder_type)`;
  - `Some(.expr)` → `ensure_arg_type`;
  - `Undef` → `finalize`;
  - `None` → `mk_implicit_arg`.

`add_arg_and_continue` bumps `idx`, sets `f := f arg`, and sets
`f_type := body.instantiate_beta_rev_range(0, 1, [arg])`. It then calls
`save_arg_info`, which records `registerMVarArgName` for an mvar
argument. leanr has no such table yet. P2 adds one on `Elab`, used only
by error reporting.

`mk_implicit_arg` creates a synthetic mvar for an inst-implicit binder
(pushed to `inst_mvars`) and a natural mvar otherwise.

**`finalize`** runs these steps in order, each with the oracle's exact
message:

1. Unused named arguments → `failed to elaborate eliminator, unused
   named arguments: …`.
2. No motive → `…, insufficient number of arguments`.
3. `forallTelescope(f_type)` gives `xs`.
   - **Under-application** (`xs` non-empty):
     - for each `x`, `whnf(expected)` must be a `forallE` whose
       domain is `fullApproxDefEq`-equal to `inferType x`;
     - otherwise `…, insufficient number of arguments, expected type:`.
   - **Over-application** (`xs` empty): run `revert_args`:
     - fold the remaining arguments from the right;
     - elaborate each syntax argument with no expected type;
     - `instantiateMVars`, then `kabstract(expected, val)`;
     - `transform(usedLetOnly := true)` on the value's type;
     - `mkForall` with a fresh binder name;
     - apply the values to `f`;
     - then require `isTypeCorrect(expected)`.
4. The head of `f_type` must be the motive, else the internal error.
5. `mk_motive(discrs = f_type's args, expected)`:
   - fold the discriminants from the right;
   - `kabstract` each one;
   - `transform(usedLetOnly)` its type;
   - `mkLambda` with a fresh binder name.
6. `isTypeCorrect(motive_val)`, else `motive is not type correct`.
7. `isDefEq(motive, motive_val)`, else `invalid motive`.
8. `synthesize_app_inst_mvars(inst_mvars, result)`.
9. Return `mkLambdaFVars(xs, instantiateMVars(result))`.

Substrate P2 must confirm before relying on it:

- **`fullApproxDefEq`**: if leanr has no approximation-flag scope, add
  an additive `with_full_approx`.
- **`transform` with `usedLetOnly`**: `leanr_meta/src/transform.rs`
  exists; check whether it has the flag.
- **`mkFreshBinderName`**: the counter must match the oracle's byte for
  byte, or the motive's binder names differ. The corpus catches this.

## Errors

Every `throwError` above is ported with the oracle's text. Each error is
a corpus record, not only a unit test. The error list is:

- no expected type
- mvar-headed expected type
- insufficient arguments
- insufficient arguments with expected type
- unused named arguments
- over-applied expected type not type correct
- motive not type correct
- invalid motive

The four `getElabElimExprInfo` shape errors are unreachable from a
genuine recursor or an aux recursor. The attribute validates its target
when it is applied, so they are unreachable from a tagged declaration
too. They get unit tests on hand-built eliminator types only.

## Fixture

`Elab0.lean` gains (P2):

- `inductive False : Prop`: an explicit motive, `h.rec`, and the
  positional `_` motive.
- `@[elab_as_elim] theorem Eq.subst'`: a tagged eliminator whose
  `majors_pos` includes `h` through the first-order rule.
- `@[elab_as_elim] noncomputable def natElim` with an implicit motive:
  the under-application path. A tagged `def` needs `noncomputable`,
  because the codegen rejects `Nat.rec`.

`mise run fixtures:regen` regenerates the `.olean` and the corpus at the
pinned toolchain.

P1's decode and `ElabElimInfo` goldens need the tagged declarations
too, so P1 adds them to the fixture first. Elab-corpus *queries* that
use them wait for P2. To keep that safe, P1 changes
`fixture_declares_no_undecoded_elab_attributes` in two ways:

- it drops `elab_as_elim` from the source-attribute ban, since the
  extension is now decoded;
- it adds `Eq.subst'` and `natElim` to the query-name ban, because those
  heads still take the ordinary path until P2.

## Testing

**P1:**

- Decode goldens on `Elab0.olean`:
  - `aux_rec_entries` contains `Nat.casesOn`, `Nat.recOn`,
    `Nat.brecOn`, `False.casesOn`, `False.recOn`, and **no**
    `False.brecOn`;
  - `elab_as_elim_entries == [Eq.subst', natElim]`;
  - malformed-bytes cases return errors.
- Predicate unit tests:
  - `Nat.casesOn_1`-style suffixes are accepted;
  - `Nat.casesOnX` is rejected;
  - `Eq.ndrec` is an aux recursor;
  - a name in the tag set but with the wrong suffix is not.
- `kabstract` differential corpus in leanr_meta's oracle harness
  (`dump_defeq.lean`-style):
  - an fvar pattern;
  - a constant-application pattern;
  - same head but a different argument count (not tested);
  - a match under binders (bvar offset);
  - a subterm with loose bvars (skipped);
  - an mvar-instantiating match.
- `ElabElimInfo` goldens: `motive_pos` and `majors_pos` for `Nat.rec`,
  `Nat.casesOn`, `Eq.rec`, `False.rec`, `Eq.subst'` and `natElim`. The
  oracle values come from a `dump_elab.lean` extension.

**P2:** elab corpus (`elab-queries.jsonl`), one query per row of
§ Evidence, plus:

- a dot-ident head `(.rec … : …)`;
- `Nat.rec ..` (ellipsis → standard path);
- an over-application that exercises `revertArgs`;
- each error in § Errors;
- an eliminator under a binder with an mvar-headed expected type: it
  postpones, then resumes after the mvar is assigned.

Seam bookkeeping (P2):

- `seam_audit.rs`'s recursor rows (`:166-190`) flip to success.
- `fixture_declares_no_undecoded_elab_attributes` drops the
  eliminator-name query loop. That includes the `Eq.subst'` and
  `natElim` entries P1 added. The `elab_without_expected_type` source
  ban stays.
- `postpone_smoke.rs:216-224` asserts the oracle's postponed `?m` instead of
  the seam.
- The `app/mod.rs` dispatch table and the `dispatch.rs:178` row lose
  "partial".

**Mutation discipline.** Plan briefs have shipped tests that pass even
when the code they target is broken. Each plan's review applies these
mutations, runs the suite, watches it go red, and records survivors
under § Landed:

- delete each `should_elab_as_elim` disjunct (five mutations);
- drop the `starts_with(sfx + "_")` arm;
- invert the `hole`-kind check in the gate;
- drop `kabstract`'s head-index filter;
- fold `mk_motive` left instead of right;
- treat `Undef` at the motive as `finalize`;
- drop the first-order disjunct from `majors_pos`;
- skip the union over the import closure (current module only).

## Delivery

- **P1, substrate.** The two decodes, the environment predicates,
  `kabstract`, `get_elab_elim_info`, and the fixture's tagged
  declarations. No elaborator-visible change.
- **P2, elaborator.** The gate, the diversion, `ElabElim`, seam
  removal, the corpus, and the `seam_audit` inversion.

P2 depends on P1. Each plan gets its own PR, merged on green CI
(`mise run ci`, including `cargo fmt --check` and clippy).

## Landed

(Filled in as each plan merges: corrections, mutations run, seams left
open.)

### P1 (PR #54): eliminator substrate

P1 adds the decodes, the predicates, `kabstract` and
`get_elab_elim_info`. It changes **no elaborator-visible behavior**: the
elab corpus (`elab-queries.jsonl`, `structures.jsonl`) is untouched and
byte-identical, the `Task 7` refactors regenerate identical fixtures,
and the recursor seams in `app/mod.rs` and `app/head.rs` are unchanged.
P2 still owns the gate, the diversion and `ElabElim`. Full `mise run ci`
is green.

**Spec corrections** (the spec text above is the plan-time design):

- **The "union over the import closure" has no production caller in
  P1.** The only code that builds a multi-module closure and unions
  `aux_recs` / `elab_as_elim` by `extend` is
  `crates/leanr_meta/tests/synth_sweep.rs:609-624`, and that sweep is
  `#[ignore]`d, so no CI gate covers the union. Every other caller is a
  test harness replaying one import-free fixture, and `EnvExtensions`
  takes plain slices, exactly as for `coe_decls`. The spec's mutation
  "skip the union" therefore has nothing CI-visible to mutate in P1.
  Follow-up: gate the import-closure union (it belongs to whichever
  slice first builds a production multi-module `MetaCtx`).
- **No dedicated malformed-bytes test.** The new decode arms go through
  `name_req`, the same checked path every name decode uses, and
  `crates/leanr_olean/fuzz/fuzz_targets/module_data.rs` already fuzzes
  `ModuleData::parse` end to end.
- **The `ElabElimInfo` goldens cover every constant**, not only the six
  the spec lists: 878 records, of which 651 are oracle errors. This
  also pins the "not an eliminator" error path.
- **Measured `majors_pos`, oracle-dumped:** `Eq.subst'` = `[0,2,3,4]`
  (`α` and `a` enter through the first-order rule), `Nat.rec` = `[3]`,
  `Nat.casesOn` = `[1]`, `False.rec` = `[1]`, `Eq.ndrec` = `[0,1,4,5]`.
- **Naming.** The fields are `aux_recs` / `elab_as_elim: Vec<NameId>`,
  not the spec's `*_entries: Vec<Name>`, matching the `coe_decls`
  convention of the sibling decodes.
- **`HeadIndex` is a new module** (`leanr_meta/src/head_index.rs`):
  `discr_path.rs` has no equivalent to extract.
- **Plan correction, Task 6 `khead`.** The plan's record (`N.succ
  (N.succ one)` against `two`) did not discriminate the head-filter
  mutation: `headNumArgs` already excludes the candidate. The controller
  replaced it with `e = N.succ (redId one)`, `p = one`; the oracle
  answers `N.succ (redId #0)`, and without the head filter `redId one`
  (one argument, reducible, defeq) is abstracted too, giving `N.succ #0`.
- **Plan correction, Task 8.** `Eq.subst'` loses majors 2 and 4 (not 0
  and 2) when the first-order disjunct is dropped.

**`KNOWN_GAPS`** (`crates/leanr_elab/tests/elim_info_oracle.rs`): `lcAny`,
`lcErased`, `lcVoid`. They are unsafe axioms, and replay skips unsafe
constants (`crates/leanr_kernel/src/replay.rs:93`), so leanr does not
know them. The oracle answers "unexpected eliminator resulting type" for
all three; the gate asserts each still diverges. The other 875 records
agree. Related minor gap: `mk_const_with_fresh_mvar_levels_of` yields
empty levels for a missing constant where the oracle's `getConstInfo`
throws; no `elim.jsonl` name reaches it, and it is a caller precondition.

**Mutations run** (each applied, suite run, reverted):

- Decodes (T2): rename the `elabAsElim` key, rename the `auxRecExt` key.
  Both killed by the module-data golden.
- Predicates (T3): drop the `_` prefix arm, drop `&& is_aux_recursor`,
  drop the builtin `Eq.ndrec*` set. All killed by
  `aux_recursor_suffix_rules` (distinct assertions: `cases_1`,
  `untagged_cases`, `ndrec`).
- Predicates against the oracle corpus (T4): `aux_recs -> &[]` (304
  divergences), `elab_as_elim -> &[]` (2), drop the builtins (1), suffix
  exact-match only (150) are killed. **Corpus survivors, unit-killed:**
  drop `&& is_aux_recursor` and drop the `startsWith "{suffix}_"` arm
  survive the oracle corpus (Elab0 has no untagged `casesOn`/`recOn`/
  `brecOn` and no `casesOn_*` names) and are killed by T3's unit test.
- `kabstract` (T5): swapping the `app` visit order is killed by
  `kabstract_mvar_pattern_first_match_wins`. Disabling the fvar fast path
  survives: **equivalent except under `mdata` (untested)**, where the
  general path abstracts the whole `mdata x` to `#0` and `abstract` keeps
  the `mdata`.
- `kabstract` against the oracle (T6): delete the head-index check
  (`khead` red), delete the head-index and arg-count checks (red), `lam`
  body at `offset` instead of `offset+1` (`kbinder` red), `letE` body
  likewise (`klet` red), `is_def_eq` replaced by `==` (`kdelta` red).
- `get_elab_elim_info` (T8): dropping the first-order disjunct is killed
  by the gate (3 divergences: `Eq.subst'` loses 2 and 4, `Eq.ndrec` loses
  1 and 5, `CoeFun.coe` loses 2). Skipping the reverse closure is killed
  by the gate (106) and by `closure_runs_right_to_left`. Dropping the
  `motive_args.is_empty()` check is killed by the gate (163) and by the
  unit test. Running the closure left to right **survives the gate**
  (no Elab0 declaration depends on the order) and is killed by the
  hand-built unit test `closure_runs_right_to_left`.
- T7 (behavior-neutral refactors) has no mutations: the elab corpus
  stays green with byte-identical regenerated fixtures.
- Not run in P1, by correction above: "skip the union over the import
  closure". The gate-side mutations (`hole`-kind check, `mk_motive` fold
  order, `Undef` at the motive) belong to P2.

**Deferred minors** (not blocking): `seam_audit.rs` matches
`@[elab_as_elim]` by substring and bans `.rec` by substring rather than
suffix; the `aux_recs` golden does not assert the `quickLt` order; the
`_` rule is only unit-tested for `casesOn`; `ProjBig` saturates at
`u64::MAX`; the `kabstract` fvar fast path has no `mdata` test.

**Oracle-corpus gaps and follow-ups for P2** (first caller with fvar/mvar
patterns):

- The `kabstract` oracle corpus lacks spec § Testing P1's "fvar pattern"
  and "mvar-instantiating match" rows. Both are covered only by unit
  tests in `crates/leanr_meta/src/kabstract.rs` (the mvar expectation is
  quoted from a planning-time oracle run). P2 should add both as oracle
  records, plus an `mdata`-wrapped fvar test for the fast path.
- `crates/leanr_meta/tests/aux_recursor_oracle.rs` uses `decode_name`,
  which has no numeric name components, so the `_private.Elab0.0.*`
  records resolve to a different `NameId` (vacuous today: the oracle
  says false for all three). Switch to the Num-aware `name_id` from
  `crates/leanr_elab/tests/support/mod.rs`.

### P2 (PR #55): ElabElim

P2 ports `ElabElim` (`App.lean:1140-1319`), the `elabAsElim?` gate
(`App.lean:1397-1431`) and the diversion in `elab_app_args`
(`App.lean:1373-1383`), and removes the three recursor seams: the dotIdent arm's `heed`
block in `head.rs`'s `elab_app_fn`, `elab_app_fn_id`'s `heed` guard, and
the `recursor_head_seam` helper both called. Full
`mise run ci` is green. The elab corpus grows by 36 records (27 `elim/*`,
9 `elimErr/*`), `CORPUS_FLOOR` 276 -> 329, and no existing record moved.
**M4b-4 is complete.**

**Spec corrections found while planning:**

- **`elab_app_fn_id`'s `heed` is deleted, not kept.** `heedElabAsElim` is
  a `TermElabM` reader field that only the `induction` tactic clears
  (`Tactic/Induction.lean:806`), so in term elaboration it is always
  `true`. The leanr `heed` also tested `lvals.is_empty() && n_fields ==
  0`, which only placed the seam, and would have sent `h.rec` down the
  ordinary path. The gate lives entirely in `elab_app_args`, on the final
  head.
- **No `registerMVarArgName` table.** Its only reader is the oracle's
  error prose, which leanr defers (`args.rs`'s `mk_inst_mvar` is the
  precedent). `save_arg_info` is documented and left out.
- **`mkFreshBinderName` need not match byte for byte.** The canonical
  encoder erases binder names.
- **`isTypeCorrect` needed a real `Meta.check`** (`Check.lean:288-338`,
  `:365-370`). `assign.rs`'s `is_type_correct` was an `infer_type` proxy,
  and both `elimErr/motiveIncorrect` and `elimErr/overAppIncorrect` are
  well-typed under `infer_type`. Task 2 ports `check` in
  `leanr_meta/src/check.rs`. The old proxy keeps its behavior as
  `infer_type_succeeds`.
- **The elab corpus had no error records.** `dump_elab.lean` now has an
  `err` record kind for an `elimErrQueries` list only, carrying the first
  line of the first logged message (the oracle logs through `errToSorry`
  then aborts with `internal exception #3`).
- **New fixture declaration `preElim`**, an `@[elab_as_elim]` axiom with an
  explicit binder before the motive, for "insufficient number of
  arguments" (no motive yet).
- **`kabstract` fvar/mvar oracle records stay deferred.** The fvar fast
  path is pinned end to end by every `elim/*` query with a bound major.
  Two P2 paths do pass an mvar pattern: `revert_args` hands a
  postponed synthetic mvar to `kabstract` (exercised only trivially, by
  `elim/overPostponed`), and `mk_motive` would for a `_` major. The
  `mdata` fast path has a unit test.

**Deviations found during execution (controller rulings):**

- **T6-A/B: query sources respelled.** leanr's `fun` has two gaps in
  `builtin/binder/fun.rs`: `_` hole binders
  (`unsupported_binder_kind`) and multi-ident paren groups `(a b : T)`
  (`extract_paren_fun_binder`). The plan's queries used both, 22 records
  diverged, and none of the pre-existing corpus used either. The queries
  now spell `_` as a fresh name and split `(a b : T)`; the canonical
  encoder erases binder names, so `exp` is unchanged. **Follow-up:** port
  `expandFunBinders` for both forms in `fun.rs`. **Closed:** `fun.rs`
  now ports `expandFunBinders` (`_`, `typeAscription` and `paren`
  groups) and the queries are back to their original spelling; see
  § Follow-up: `expandFunBinders` below.
- **T6-C: `elim/namedMotive` / `elim/explicitAt` annotate `ih`.** These
  are standard-path controls (motive supplied). Original query
  `fun (n : Nat) => Nat.rec (motive := fun _ => Nat) Nat.zero (fun _ ih
  => ih) n` gives `ih : (fun _ => Nat) x` in leanr and `ih : Nat` in the
  oracle: `MetaCtx::instantiate_beta_rev_range` uses `head_beta`, not the
  oracle's nested `visit`, so a nested redex survives into a propagated
  binder type. This is a **silent wrong term with no seam**. **Follow-up,
  ranked HIGH:** port the full `instantiateBetaRevRange`. The reproducer
  is in the `metactx.rs` doc, whose false "unobservable" claim was fixed
  (doc-only).
- **T6-D: `elim/ndrec` dropped, `elim/eqRecTwoDiscrs` added.** `Eq.ndrec`
  is not an eliminator (`elab_as_elim_info` answers `None`); the oracle
  solves `?m.6 ?m.5 =?= Eq a a` by `foApprox`. The oracle's `TermElabM.run`
  is `withConfig setElabConfig` (`TermElabM.lean:2227`,
  `Elab/Config.lean:61-62`: `foApprox`/`ctxApprox` true), and leanr's
  `TermElabM` runs under `Config::default()`. **Follow-up:** model
  `setElabConfig` (a global change; needs a full corpus rerun). The new
  record is a two-discriminant `Eq.rec`. **Closed** by `2026-10-01-set-elab-config-design.md` (`elim/ndrec`
  reinstated).

**Mutations run** (each applied, suite run, reverted):

- `Meta.check` (T2): `check_app` -> `Ok(())`, let-value defeq check
  disabled, level-count check disabled, `ensure_type` -> plain
  `get_level`. All killed (`ill_typed_application_is_rejected_where_infer_type_succeeds`,
  `check_keeps_defeq_assignments`, `let_value_type_mismatch_is_rejected`,
  `wrong_universe_count_is_rejected`,
  `binder_type_mvar_with_mvar_type_is_type_correct_and_assigns_sort`).
  Not mutation-tested: `check_proj` and the forall/lambda telescope arms
  (no test exercises them).
- Gate (T5, `elim_smoke.rs`): drop each of the five `shouldElabAsElim`
  disjuncts, invert `!= hole`, drop `explicit || ellipsis`. All killed.
  **Survivors:** the pre-motive `bi == Default` arm and the named-arg
  erase. They only matter for an explicit motive after a pre-motive
  binder, and no fixture eliminator has one. A fix round also replaced an
  unchecked `xs[motive_pos]` with `xs.get`.
- `ElimElab` (T6, real corpus): `mk_motive` folds left (killed by
  `elim/eqRecTwoDiscrs`), `Undef` at motive -> `finalize` (`elim/hRec`,
  `elim/hRecArg`, `elimErr/insufficientExpected`), `is_type_correct` ->
  `infer_type().is_ok()` (`elimErr/motiveIncorrect`,
  `elimErr/overAppIncorrect`), `transform_used_let_only` -> identity
  (`elim/letDiscr`, `elim/letOver`), drop the mvar-headed-expected check
  (`elimErr/mvarExpected`, `elimErr/noExpected`). **Survivors:** removing
  `with_full_approx_def_eq`, and `revert_args` elaborating L->R. The
  inst-implicit path of `ElimElab` (`mk_implicit_arg` synthetic,
  `inst_mvars` push, `synthesize_app_inst_mvars_of`) is unexercised: no
  fixture eliminator has an inst-implicit binder.

**Open seams and follow-ups:**

- `@[elab_without_expected_type]` stays banned (`seam_audit.rs`).
- `kabstract` mvar-pattern oracle records (above).
- The `infer_type_succeeds` proxy in `assign.rs`'s `quasiPatternApprox`
  branch: route it through the real `check`.
- `trace[Elab.app.elab_as_elim]` is not modelled.
- `numScopeArgs`: no query hit that gap.
- `fun.rs` `expandFunBinders` (`_`, multi-ident): closed, see below.
  (`setElabConfig` is closed; see its own spec.) The `instantiate_beta_rev_range` nested-redex gap (was HIGH) is
  closed; see the follow-up note below.
- Fixture/record follow-ups from the final review: a `preElim2`-style
  fixture eliminator with an explicit binder before an explicit motive
  (kills the gate's pre-motive survivors); a two-extra-argument
  over-application record (targets the `revert_args` order survivor); an
  `[inst]`-binder eliminator record (exercises `ElimElab`'s inst-implicit
  path); a `check_proj` test.
- Deferred minors: stale `usedLetOnly := false` mentions in the
  `transform.rs` docs; `check_proj` and telescope-arm tests; the
  `seam_audit` `"M4b-4c"` needle forbids future M4b-4c-labelled seams by
  design.

M4b-4 is complete.

### Follow-up: `instantiateBetaRevRange` nested redexes (closed)

`MetaCtx::instantiate_beta_rev_range` substituted and then ran
`head_beta`, so a bvar-headed redex nested under a binder survived. The
full port of the oracle's `visit` (`InferType.lean:72-91`) already existed,
private to `infer.rs` (`instantiate_beta_rev`, used by `infer_app_type`).
The P2 doc's claim that no such walk existed was wrong.
`instantiate_beta_rev_range` keeps the oracle's two short-circuits and now
delegates its any-lambda arm to that port, so `leanr_meta` has one
transcription. The known-divergence test in `elim_smoke.rs` became two
corpus records, `elim/namedMotiveBareIh` and `elim/explicitAtBareIh`
(`CORPUS_FLOOR` 329 -> 331), whose oracle `exp` equals their annotated
twins'. No existing record moved. Mutation: restoring
`instantiate_rev` + `head_beta` turns the new
`instantiate_beta_rev_range_betas_a_redex_nested_under_a_binder` unit
test and both records red.

### Follow-up: `expandFunBinders` (closed)

`fun.rs` rejected `fun _ x` (hole binders) and `(a b : T)` / `(x y)`
groups, so the P2 queries had been respelled. `extract_fun_binder_views`
now ports `expandFunBinders` (`Binders.lean:360-406`, pinned
v4.33.0-rc1) with `getFunBinderIds?` (`:320-345`):

- `hole`: one `Default` binder, anonymous (the oracle mints a
  macro-scoped name; the canonical encoder erases binder names).
- `typeAscription`: each ident/`_` element of `x₁ … xₙ` binds with the
  shared type; `(x :)` gets a hole type. No global-name gate.
- `paren`: the same split with hole types, only when no ident resolves
  as a global (`resolve_global_name`); `(Nat)` is a pattern.
- Every pattern fallback, and every unlisted binder kind
  (`processAsPattern`), is the `pattern_binder_seam`, owned by the match
  slice.

Corpus: 12 `funx/*` records; the 31 respelled `elim*` sources restored
(`exp`/`err` byte-identical); `CORPUS_FLOOR` 333 -> 345. Mutations run,
each killed: drop the global gate; type only the first split ident;
error on an absent ascription type; accept a non-ident element as a
hole; bind only the first paren element.

Open seam: `ensureAtomicBinderName` is not ported. The oracle rejects
`fun (a.b : Nat) => …` ("invalid binder name `a.b`, it must be atomic",
probed), and leanr binds `a.b` as one component. This predates this
change (single-ident binders had it too).
