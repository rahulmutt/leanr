# M4b-3 close-out — implementation-detail binders, binder-annotation checks, `let`/`have` binder breadth, the `@($t)` wrap — design spec

## Where this sits

M4b-3 (the application elaborator) is complete: its last phase, P5 —
binder and argument breadth — merged in #44. P5's seam-audit record
(§ Amendment 9 of `2026-07-25-m4b3-application-elaborator-design.md`)
listed what the next slice inherits. This slice closes the concrete
items on that list before M4b-4 adds more binder producers (the match
compiler, and later tactics) on top of them:

1. **A live, silent divergence.** leanr installs a local instance for a
   user binder whose name starts with `__`; the oracle does not. leanr
   emits a different term with no error.
2. **A live acceptance gap** found while scoping item 1. leanr accepts
   `forall [i : Nat], Nat` and `forall [i : Nat -> Add Nat], Nat`; the
   oracle rejects both.
3. **`let`/`have`'s own binder list** still rejects implicit,
   strict-implicit and instance binders (a "later M4" seam).
4. **`@($t)` / `@$t`** still hit a "later M4" seam instead of
   elaborating `t` with implicit-lambda insertion disabled.
5. **`builtin/binder.rs`** is 1414 lines, past the ~1000-line ceiling.

Like the rest of M4b, this ships no independently useful
functionality. It removes one wrong-term divergence, one
accepts-what-Lean-rejects gap, and two named seams.

## Evidence

Every oracle claim below was checked two ways: the citation was
opened in the pinned source
(`~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/`), and
the behaviour was run on the pinned `lean` binary. The leanr column
was run against the committed `Elab0.olean` on `main` @ `33ebb32`.
Terms were probed in core Lean with a stand-in class `Foo`, then
checked on leanr with the fixture's `Add`.

### `__` binders

| Term | Oracle | leanr today |
|---|---|---|
| `fun (i : Foo Nat) => (Foo.bar (α := Nat) : Nat)` | uses local `i` | uses local `i` |
| `fun (__i : Foo Nat) => …` | uses global `instFooNat` | **uses local `__i`** |
| `fun [__i : Foo Nat] => …` | global | not probed on leanr |
| `∀ (__i : Foo Nat), … = …` | global | not probed on leanr |
| `let __i : Foo Nat := ⟨1⟩; …` | global | not probed on leanr |
| `have __i : Foo Nat := ⟨1⟩; …` | global | not probed on leanr |
| `let f [__i : Foo Nat] : Nat := …; f` | global inside `f`'s value | seam (item 3) |
| `fun (__i : Foo Nat) => __i` | resolves `__i` by name | — |

Mechanism. `LocalDeclKind.ofBinderName` (`Elab/BindersUtil.lean:21-25`)
classifies a name as `.implDetail` when `Name.isImplementationDetail`
holds (`Data/Name.lean:167-171`): the name's **root** string component
starts with `__`. `withNewLocalInstanceImp` (`Meta/Basic.lean:1383-1388`)
skips the local-instance push for such a declaration, and
`elabFunBinderViews` matches `kind` directly (`Elab/Binders.lean:444-445`).

**The kind is decided per call site, not per name.** `.ofBinderName` is
passed only where the oracle elaborates a user-written binder:
`elabBinderViews` (`Binders.lean:221`, used by `forall`, `depArrow` and
`let`/`have`'s own binders), `elabFunBinderViews` (`:434`),
`elabLetDeclAux`'s let-declaration (`:805`), and match patterns and
`do` (out of scope). Every other `withLocalDecl` — telescopes,
implicit-lambda binders, eta arguments — keeps `.default`, even for a
`__`-prefixed name.

### Binder annotations

| Term | Oracle |
|---|---|
| `fun [i : Nat] => i` | accepted — `elabFunBinderViews` has no check |
| `[i : Nat] → Nat`, `∀ [i : Nat], Nat`, `have f [i : Nat] : Nat := 0; 0`, `∀ [i : _], Nat` | "invalid binder annotation, type is not a class instance" |
| `∀ [i : Nat → Foo Nat], Nat` | "invalid parametric local instance" (parameter `Nat`) |
| `∀ [i : ∀ {a : Type}, Foo Nat], Nat` | same (parameter `Type`) |
| `∀ [i : ∀ (a : Type), Nat → Foo a], Nat` | same, on the **second** parameter (`Nat`) |
| `let f [i : Nat → Foo Nat] : Nat := 0; 0` | same |
| `∀ [i : ∀ (a : Type), Foo a], Nat` | accepted (forward dependency) |
| `∀ [i : ∀ [Foo Nat], Foo Nat], Nat` | accepted (instance-implicit parameter) |
| `∀ (i : Nat → Foo Nat), Nat` | accepted (only instance binders are checked) |

leanr today accepts `forall [i : Nat], Nat` and
`forall [i : Nat -> Add Nat], Nat`. No check exists anywhere in
`crates/leanr_elab`.

Mechanism: `elabBinderViews` (`Binders.lean:216-219`) runs, for an
instance-implicit binder and under `checkBinderAnnotations` (default
`true`), `isClass? type` and then `checkLocalInstanceParameters`
(`:199-206`): `whnf` the type; if it is a `forallE` whose binder is not
instance-implicit and whose body has no loose bvar 0, throw; otherwise
push the parameter with `withLocalDecl` and recurse on the instantiated
body.

### `let`/`have` own binder list

All accepted by the oracle; leanr rejects each with the "later M4" seam.

| Term | Oracle |
|---|---|
| `let f [i : Foo Nat] : Nat := Foo.bar (α := Nat); f` | `let f : [i : Foo Nat] → Nat := fun [i : Foo Nat] => @Foo.bar Nat i; @f instFooNat` |
| `let f [Foo Nat] : Nat := …; f` | same shape, anonymous instance binder |
| `let f {a : Type} (x : a) : a := x; f Nat.zero` | `@f Nat Nat.zero` |
| `let f ⦃a : Type⦄ (x : a) : a := x; f` | `f` (strict implicit not inserted) |
| `have` forms of the first and third rows | same, as `have` |

### `@($t)` / `@$t`

| Term | Oracle | leanr today |
|---|---|---|
| `(@(fun (a : Type) => a) : {a : Type} → Type)` | `fun (a : Type) => a` | seam |
| `(@((fun (a : Type) => a)) : {a : Type} → Type)` | same | seam |
| `(fun (a : Type) => a : {a : Type} → Type)` | type mismatch | type mismatch |
| `(@(fun (a : Type) => (Nat.zero : {b : Type} → Nat)) : {a : Type} → {b : Type} → Nat)` | `fun (a : Type) {b : Type} => Nat.zero` | seam |
| `@(fun (a : Type) => a)` | `fun (a : Type) => a` | seam |
| `(@(fun {a : Type} => Nat.zero) : {a : Type} → Nat)` | `fun {a : Type} => Nat.zero` | seam |
| `(@0 : {a : Type} → Nat)` | fails to synthesize `OfNat ({a : Type} → Nat) 0` | seam |
| `(0 : {a : Type} → Nat)` | `fun {a : Type} => 0` | same as oracle |
| `(@(Nat.zero : Nat) : {a : Type} → Nat)` | type mismatch | seam |
| `@(Nat.succ) Nat.zero` | "unexpected syntax" | `App.lean:2118` seam (unchanged, out of scope) |

Mechanism: `elabExplicit`'s `` `(@($t)) `` and `` `(@$t) `` arms
(`Elab/App.lean:2269-2270`) call `elabTerm t expectedType?
(implicitLambda := false)`. The flag gates `useImplicitLambda` in
`elabTermAux` (`Elab/Term/TermElabM.lean:1839`) for **that syntax only,
not its subterms** (doc, `:1876-1877`), but it **is** carried into a
macro's expansion (`:1837`). `Term.paren` is a macro in the oracle
(`expandParen`, `Elab/BuiltinNotation.lean:410`), which is why nested
parentheses keep the flag.

## Scope

In: the five items above. Out: see § Out of scope.

## Design

### 1. `binder.rs` split (pure move)

`crates/leanr_elab/src/builtin/binder.rs` becomes a directory module
`builtin/binder/`:

| File | Contents |
|---|---|
| `mod.rs` | `elab_type`, `BinderGroup`, `binder_info_of`, `extract_binder_group`, `push_binder_group`, and helpers used by more than one binder form; re-exports the entry points below |
| `forall.rs` | `elab_arrow`, `elab_binders_and_forall`, `elab_forall`, `elab_dep_arrow` |
| `fun.rs` | `propagate_expected_type`, `FunBinderView` and the fun-binder-view extractors, `elab_fun`, and the in-file test module (its four tests all exercise `propagate_expected_type`) |
| `let_like.rs` | `extract_let_id_name`, `push_let_binders`, `elab_let_like` |

A helper's home is decided by its actual call sites. The only external
importers are `dispatch.rs` and `elab.rs`; with the re-exports, the
`crate::builtin::binder::X` paths they use do not change. Live
citations of `binder.rs` elsewhere in `crates/leanr_elab` are rewritten
to the new file and, where they cite line numbers, to symbol names
(line cites drift; see `app/state.rs`'s `builtin/binder.rs:217,226`).
Historical plans and specs are records and are not edited.

This lands first, as its own commit, so every later diff is against the
smaller files.

### 2. Implementation-detail binders

**`leanr_meta`.**

- A new `LocalDeclKind { Default, ImplDetail }`, exported from the crate
  root, mirroring the oracle's type minus `auxDecl` (no producer in
  leanr).
- A classifier mirroring `LocalDeclKind.ofBinderName`: walk `NameRow`
  parents (`leanr_kernel/src/bank/names.rs`) to the root component;
  `ImplDetail` iff it is a `Str` row whose string starts with `"__"`. An
  anonymous name (`None`) and a `Num` root are `Default`. It reads name
  rows through the `MetaCtx`'s store (base and scratch). The exact
  signature is the plan's.
- New entry points `push_local_decl_with_kind` and
  `push_let_decl_with_kind`.
- `install_local_instance_for_last_pushed` gains a `kind` parameter (one
  caller, in `elab_fun`).
- The private `install_local_instance_for` gains a `kind` parameter and
  skips the push when it is `ImplDetail`. Its `lctx_snapshot` memo-drop
  stays unconditional.
- `push_local_decl` and `push_let_decl` keep their signatures and pass
  `Default`. Their existing call sites (about 60, mostly `leanr_meta`
  telescopes and tests; the handful in `builtin/binder.rs` move to the
  helper below) are oracle `.default` sites and do not change
  behaviour.
- The kind is **not stored**. `LocalDecl` lives in `leanr_kernel`
  (`local_ctx.rs`), which stays untouched; the only other in-elaborator
  consumer of the kind is `withLocalInstancesImp`
  (`Meta/Basic.lean:1941`), reached from `Match.lean:826`, so storing
  it is the match slice's job.
- `MetaCtx::is_class` widens from `pub(crate)` to `pub` (needed by
  item 3; additive, behaviour-neutral).

**`leanr_elab`.** One helper in `builtin/binder/mod.rs` —
`push_user_binder(elab, name, ty, bi)` and a let-declaration twin —
computes the kind and calls the `_with_kind` entry point. It is the only
way the three oracle `.ofBinderName` sites push:

| Oracle site | leanr site |
|---|---|
| `elabBinderViews` (`Binders.lean:221`) | `push_binder_group` (forall, depArrow, `let`/`have` bracketed binders) and `push_let_binders`' bare-ident arm |
| `elabFunBinderViews` (`:434`, `:444-445`) | `elab_fun`: `push_local_decl_without_instance`, then `install_local_instance_for_last_pushed(fvar, dom, kind)` |
| `elabLetDeclAux` (`:805`) | `elab_let_like`'s let-declaration push |

Anonymous pushes (holes, implicit-lambda binders), `app/args.rs`'s eta
argument (`_leanr_elab_*` fresh names), and `app/state.rs`'s
`forall_telescope_reducing` stay on `push_local_decl`, as `Default`.

**Rejected alternatives.**

- *Name test inside `install_local_instance_for`* (the fix § Amendment 9
  prescribed). One line, but it also skips `.default`-kind declarations:
  `leanr_meta`'s own telescopes (pinned to install by `assign.rs`'s
  `a_telescope_installs_local_instances_for_its_binders`) and
  `forall_telescope_reducing` over a constant whose parameter is named
  `__x`. It trades one divergence for another.
- *Elaborator-only gate* (user-binder sites skip the install via
  `push_local_decl_without_instance` plus a new
  `push_let_decl_without_instance`). No existing `leanr_meta` behaviour
  changes, but the rule becomes a caller-side convention — the shape P5's
  review flagged as "easy to forget exactly because nothing enforces
  it" — and a Meta-level check moves into the elaborator.

### 3. Binder-annotation check

In `push_binder_group`, after `elab_type` and before any push, when the
group's binder info is instance-implicit:

1. `is_class(dom)` is `None` → `ElabError::InvalidBinderAnnotation { ty }`.
2. Otherwise port `checkLocalInstanceParameters`: `whnf` the type; if it
   is not a `Forall`, return. If the binder is not instance-implicit and
   the body has no loose bvar 0 →
   `ElabError::InvalidParametricLocalInstance { param_ty }`. Otherwise
   push the parameter (`push_local_decl`, `Default` kind, as the
   oracle's `withLocalDecl`), instantiate the body with it, recurse,
   and restore the local context on every exit path
   (`lctx_checkpoint`/`lctx_restore`).

`elab_fun` does not run the check. `push_binder_group` is the only
leanr port of `elabBinderViews`, so the check covers forall, depArrow
and `let`/`have`'s own binders with no other site. The exact names of
the loose-bvar and instantiate helpers are the plan's, verified against
the code.

Unmodelled: `set_option checkBinderAnnotations false` — leanr has no
options, so the check always runs (the oracle default). The error
prose (the `.note` hint) is not modelled, as for every variant.

### 4. `let`/`have` binder breadth

Delete `push_let_binders`' non-default-binder-info guard. Nothing else
changes: item 3's check now lives in `push_binder_group`,
`elab_let_like` already abstracts value and type with
`mk_lambda`/`mk_forall` over fvars that carry their binder infos, and
P2a's instance-argument insertion handles an application of the
let-bound `f`. If a corpus record disagrees, the differential gate
finds it; nothing here is assumed beyond what the records confirm.

### 5. The `@($t)` / `@$t` wrap

**`elab.rs`.** `elab_term` becomes a thin call into a private
`elab_term_core(elem, kinds, expected, implicit_lambda: bool)`. A new
public `elab_term_without_implicit_lambda` calls it with `false`:

- `false` skips `use_implicit_lambda` entirely, including its
  `.postpone` arm (the oracle's `pure .no`).
- With `false`, a `Term.paren` node recurses on its inner term with
  `false` instead of dispatching. This models `:1837` carrying the flag
  into `expandParen`'s expansion, because leanr runs `paren` as an
  elaborator (`builtin/ascription.rs`'s `elab_paren`) where the oracle
  has a macro. `paren` is the only oracle macro leanr models as an
  elaborator.
- The flag is a parameter, never `TermElabM` state, so it cannot leak
  into subterms.

**`app/mod.rs`'s `elab_explicit`.** The ident/`explicitUniv` →
`elab_atom` arm and the proj/dotIdent → M4b-4 seam are unchanged. The
fallback arm becomes `elab.elab_term_without_implicit_lambda(inner, …)`.
One arm covers both oracle arms: `` `(@($t)) `` elaborates the paren's
inner term, which is exactly what the core's paren pass-through does
when handed the paren.

Unmodelled: `expandParen`'s `expandCDot?` — leanr does not parse `·`.

## Accessor ledger (`leanr_meta`)

| Change | Shape |
|---|---|
| `LocalDeclKind` + the binder-name classifier | additive |
| `push_local_decl_with_kind`, `push_let_decl_with_kind` | additive |
| `install_local_instance_for_last_pushed(…, kind)` | signature change, one caller |
| `install_local_instance_for(…, kind)` skips `ImplDetail` | **behaviour change** on a new path; every existing caller passes `Default` and is unchanged |
| `is_class`: `pub(crate)` → `pub` | visibility only |

The behaviour change is flagged, not folded into "additive". Neutrality
for existing callers is shown by the synthesis corpus staying
byte-identical, the full `leanr_meta` suite, and a new test that a
`__`-named class binder pushed through `push_local_decl` still installs.

## Error handling

Two new `ElabError` variants, each carrying the oracle's subject
expression:

- `InvalidBinderAnnotation { ty }` — `Binders.lean:218`.
- `InvalidParametricLocalInstance { param_ty }` — `Binders.lean:205`.

Retired seams: `push_let_binders`' "let: implicit/strict/instance binder
in let/have's own binder list — later M4" and `elab_explicit`'s "`@`
applied to `…` does not enter explicit mode … — later M4". No other
error changes.

## Verification

### Oracle records (`tests/fixtures/elab/dump_elab.lean`)

Four new query groups, each added by the commit that makes it pass:

- `closeoutImplDetailQueries` — the `__` forms of `fun (… : Add Nat)`,
  `fun [… : Add Nat]`, `forall (… : Add Nat)`, `let … : Add Nat`, `have
  … : Add Nat`, each with a body that synthesizes `Add Nat`, plus the
  non-`__` twins of the `fun`, `fun [·]` and `forall` forms (8 records).
  `let`/`have` carry no twin — see § Amendment 1.
- `closeoutBinderCheckQueries` — the accepted parametric instance
  binders, which the check must not reject: `forall [i : forall (a :
  Type), Add a], Nat`, `forall [i : forall [Add Nat], Add Nat], Nat`,
  and `forall (i : Nat -> Add Nat), Nat`. No existing record has a
  function-typed instance binder, so without these a mutation of the
  loose-bvar-0 condition would go uncaught by the corpus.
- `closeoutLetBinderQueries` — the accepted `let`/`have` rows above, with
  `Add`/`instAddNat` for `Foo`, including `let f [__i : Add Nat]`.
- `closeoutExplicitQueries` — the accepted `@` rows above, plus
  `@(Nat.succ Nat.zero)` (the retired seam's own example).

IDs take the form `closeout/<item>-<case>`. Every record uses constants
`Elab0` already declares (`Nat`, `Type`, `Add`, `instAddNat`, `Eq`). If
regeneration shows a record needs a new constant, it lands in a
separate fixture-only commit that re-checks every existing record
byte-for-byte (the P5 Task 0 precedent).

### Unit tests

- `leanr_meta`: the classifier (`__i` → `ImplDetail`; `_i`, `i`,
  anonymous → `Default`; `__a.b` → `ImplDetail`; `a.__b` → `Default`);
  `push_local_decl_with_kind(…, ImplDetail)` of a class-typed binder
  installs nothing; `push_local_decl` of a `__`-named class binder still
  installs.
- `leanr_elab`, the rejected rows (the corpus records only successes):
  every "invalid binder annotation" and "invalid parametric local
  instance" row; `fun [i : Nat] => i` still succeeds; `(@0 : {a : Type}
  -> Nat)` fails with an elaboration error that is not
  `UnsupportedSyntax` (the plan pins the variant after running it);
  `(@(Nat.zero : Nat) : {a : Type} -> Nat)` is a `TypeMismatch`;
  `@(Nat.succ) Nat.zero` is still the `App.lean:2118` seam;
  `@(Nat.zero).1` is still the M4b-4 seam.
- Flipped: `app_smoke.rs`'s `@(Nat.succ Nat.zero)` test expects success;
  `seam_audit.rs`'s `("@(Nat.succ Nat.zero)", "later M4")` entry is
  removed.

### Mutations (each run, each recorded in its task report)

| Mutation | Must fail |
|---|---|
| Delete the `ImplDetail` skip | the `__` records |
| Classify on the name inside `install_local_instance_for` | the telescope-still-installs test |
| Drop the `is_class` test | the invalid-binder-annotation tests |
| Invert the loose-bvar-0 condition | the parametric-instance tests and the `closeoutBinderCheckQueries` records |
| Drop the recursion | the second-parameter test |
| Run the check in `elab_fun` too | the `fun [i : Nat] => i` test |
| Pass `true` from `elab_explicit` | the paren `@` records |
| Drop the paren pass-through | the nested-paren record |
| Make the flag sticky state | the subterm record |
| Route non-paren `@$t` through `elab_atom` | the `@0` test |

### Branch gate (before the PR)

- Elaboration corpus: 134 → 134 + N as a pure append; zero changed or
  removed lines.
- Synthesis corpus: 32, byte-identical; `mise run meta:fast` passes.
- `leanr_kernel`: `git diff --stat` empty. `lean-toolchain`: unbumped.
  `Elab0.lean`: unchanged unless a fixture-only commit was needed.
- Split commit: `git diff -M` shows moves only.
- `mise run ci` (fmt, clippy, full suite) before every push.
- Every citation in the plan opened against the pinned source; every
  accepts/rejects claim run on the binary.

## Seams and deferrals

Still open after this slice, each with its owner:

| Seam | Owner |
|---|---|
| Storing `LocalDeclKind` on declarations (`withLocalInstancesImp`, `Match.lean:826`) | the match slice (M4b-4) |
| `@$t` as an application head (`App.lean:2118`) | none — the oracle rejects it too |
| `checkBinderAnnotations := false` | the slice that adds options |
| `expandCDot?` inside `@(…)` | the parser slice that adds `·` |
| `useImplicitLambda`'s `.postpone` arm | M4b-4 |
| `get_instances` re-entrancy (latent) | first environment carrying matchers |
| A `let`/`have`-bound local instance consumed through synthesis leaks an unabstracted `fvar` (`mk_let_expr` skips `elimMVarDeps`) | its own follow-up slice (§ Amendment 1) |

## Out of scope

- M4b-4 constructs (dot notation and LVals, `elabAsElim`, `binop%`,
  `⟨⟩`, match).
- `do`-notation and match-pattern `ofBinderName` sites.
- Macro-scope hygiene.
- `with_assignable_synthetic_opaque`'s drop guard (P3 follow-up 4).
- `lean-toolchain` bump.

## Amendment 1 (2026-09-11, planning): the let-bound local-instance leak

Found while building the plan's red list: the candidate records were
dumped from the pinned oracle and appended to a scratch copy of the
corpus on `main`. Four of them tripped `oracle_elab`'s leaked-`fvar`
assertion: `let`/`have` binding a class-typed local, with a body whose
instance argument the synthesis fixpoint fills in.

**The divergence.** On leanr, `let i : Add Nat := instAddNat;
Add.add Nat.zero Nat.zero` elaborates (through
`elab_term_and_synthesize`) to a term whose instance argument is an
unabstracted `fvar`; the oracle emits `bvar 0`. The same body under
`fun (i : Add Nat) => …` is correct. It is pre-existing and not caused
by anything in this spec.

**Cause.** `MetaCtx::mk_let_expr` abstracts with a bare
`abstract_fvars` and never runs `elim_mvar_deps`, unlike `mk_binding`
(behind `mk_lambda`/`mk_forall`). The postponed instance metavariable is
assigned the let-bound `fvar` after the `let` has closed. The
elimMVarDeps slice deliberately refused let-declarations
(`2026-09-09-elim-mvar-deps-design.md` § "Let-declarations: a refusal,
not an arm"): the oracle's `mkAuxMVarType` ldecl arm needs a `nondep`
bit that `leanr_kernel`'s `LocalDecl` does not carry.

**Ruling (project owner, 2026-09-11): seam it here, fix it in its own
slice.** In this slice:

- `closeoutImplDetailQueries` drops the `let i`/`have i` twins. The
  `let __i`/`have __i` records stay: once item 2 lands, `__i` is not a
  local instance, synthesis picks the global `instAddNat`, and nothing
  leaks.
- `seam_audit.rs` gains a test pinning the current wrong answer (an
  `fvar` instance argument). It follows the precedent of
  `postponed_coe_under_a_binder_abstracts_via_elim_mvar_deps`, which
  pinned its own wrong answer until the elimMVarDeps slice flipped it.
- `mk_let_expr`'s doc records the gap and names that test.

The follow-up slice must choose where the `nondep` bit lives: a
`leanr_meta` side table, or a kernel `LocalDecl` field. The latter
touches the TCB and must be flagged.

## Landed

Measured against merge-base `33ebb32`:

- Elaboration corpus 134 → 160, a pure append (`26 0`); zero removed or
  changed lines. Synthesis corpus byte-identical.
- `leanr_kernel`, `lean-toolchain`, `Elab0.lean`/`Elab0.olean`: untouched.
- `leanr_meta/src`: `lib.rs | 2 +`, `local_decl_kind.rs | 139
  ++++++++++++++++++++++++`, `metactx.rs | 177
  +++++++++++++++++++++++++------` (3 files changed, 284 insertions(+),
  34 deletions(-)) — exactly the accessor ledger above.
- `mise run ci`: pass.
- Mutations: every row of § Verification's mutation table was run and
  failed as listed (task reports).
- Still open, as designed: § Seams and deferrals, including § Amendment 1's
  let-bound local-instance leak, pinned by `seam_audit.rs`'s
  `a_let_bound_local_instance_consumed_by_synthesis_leaks_an_fvar`.
- A ruling made during execution: `let_like.rs`'s `push_let_binders` hole
  arm pushes through `push_user_binder` (the brief's routing), while
  § Design 2 says anonymous pushes (holes) stay on `push_local_decl`. The
  behaviour is identical — an anonymous name classifies as `Default` — so
  this is recorded as a noted drift from § Design 2's wording, not a
  behaviour change.
- Mutation provenance: two § Verification rows were exercised by tests
  other than the ones named. "Delete the `ImplDetail` skip" was run
  against `leanr_meta`'s unit test in Task 2, and against the
  `closeout/impl-detail-*` records in Task 3. "Run the check in
  `elab_fun` too" was killed by the oracle record
  `closeout/binder-check-fun-unchecked` rather than a unit test. Task 4
  also added a `binder_smoke.rs` test,
  `checked_parameter_does_not_leak_past_the_check`, which kills dropping
  the local-context restore; that row is not in the table.
