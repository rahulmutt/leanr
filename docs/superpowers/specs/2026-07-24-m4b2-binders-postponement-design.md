# M4b-2 — binder elaborators and the synthetic-mvar postponement ladder — design spec

## Where this sits

M4b-1 shipped `leanr_elab`: the crate seam, the
`SyntaxKind → elaborator` dispatch table, the `TermElabM` state layered
over `leanr_meta`'s `MetaM` core, the differential oracle harness
(`oracle_elab.rs` + `elab-queries.jsonl`), and the **leaf** elaborators
(string / sort / global-ident / ascription / hole). The entry point
stops at `elab_term → instantiate_mvars`; nothing elaborates under a
binder, and the deferred scheduling fields (`synthetic_mvars`,
`mvar_error_infos`, `let_recs_to_lift`) are intentionally absent.

M4b-2 is the next slice of the term elaborator. It adds the **binder
forms** and the **postponement / synthetic-mvar ladder** — the fixpoint
scheduler the M4b-1 spec named as *the actual fidelity risk* of all of
M4b. Per the M4b slicing:

| Slice | Content |
|---|---|
| M4b-1 (shipped) | crate skeleton, dispatch, oracle harness, leaf elaborators |
| M4b-2 plan 1 (shipped) | binder foundation: `forall`+`arrow`+`depArrow` + `MetaCtx` local-context accessors |
| **M4b-2 plans 2-3 (this spec)** | binder elaborators `fun` (plan 2) and `let`/`have` (plan 3) — **no scheduler** |
| M4b-3 | the application elaborator (`elabApp`) + coercion insertion + num/char literals + **the `synthesizeSyntheticMVars` fixpoint** |
| M4b-4 | `elabAsElim`, dot notation, `binop%`, anonymous constructor `⟨⟩` |
| later M4 | macro expansion + `by` tactic blocks (**`show` lands here**, see § Scope correction), structure instances, match/equation compiler, `do` |

Pinned oracle: `leanprover/lean4:v4.33.0-rc1` (`lean-toolchain`). All
oracle citations below are against that toolchain's
`src/lean/Lean/{Elab,Parser}`.

## Amendment (2026-07-24, post-plan-1): the fixpoint moves to M4b-3

This spec originally paired the `synthesizeSyntheticMVars` fixpoint with
`fun` in plan 2. Reality-checking plan 2 against the shipped plan-1 code
and the pinned grammar surfaced a finding of the same class as M4b-1's
"num/char are not leaves" and plan-1's "no thin fixpoint" corrections:

> **No closed source term in M4b-2's grammar creates a synthetic mvar the
> fixpoint must drain.** `fun` postponement fires only when the expected
> type is an *unassigned expr mvar* — which arises only in an argument
> position whose parameter type is a metavariable, i.e. requires
> **application** (`elabApp`, M4b-3). Ascription supplies a concrete
> expected type (→ the `∀` path, no postpone); a bare `fun` has expected
> `None` (→ the `None` path, no postpone). `TypeClass` mvars likewise have
> no source producer until `elabApp`. The default-instance drain and the
> `mvarErrorInfos` error pass have no differential coverage either (the
> oracle dumper emits an unresolved hole as a bare `mvar`, not an error).

The entire scheduler ladder is therefore forward-investment the
differential oracle cannot exercise until M4b-3. Per the project's
verify-driven discipline (fields arrive with the code that uses them; no
speculative surface), **the whole fixpoint — postponement resume,
`TypeClass` drain, `synthesizeUsingDefault`, `mvarErrorInfos`, the ladder
fields, the entry-point pipeline change, `mayPostpone` threading — moves
to M4b-3**, landing with `elabApp`, the first construct that creates each
of these mvars from source and gives every one differential oracle
coverage. What remains in M4b-2 is the two remaining binder forms, `fun`
(plan 2) and `let`/`have` (plan 3), each fully oracle-verifiable with **no
scheduler machinery**. The § Plan 2 and § Out-of-scope sections below are
rewritten to match; the original § canonical entry-point pipeline and the
Plan 3 section stand (the entry point stays `elab_term_ensuring_type →
instantiate_mvars`, now unchanged through all of M4b-2).

## What M4b-2 ships — and the stated non-shipping

Like all of M4a and M4b-1, **M4b-2 does not ship independently useful
user value**, and this is recorded rather than papered over: an elaborator
that handles binders but not application still cannot elaborate a real
declaration. What M4b-2 delivers is a `leanr_elab` term elaborator for
the binder forms (`∀`/`→`/`(x:A)→B`, `fun`, `let`/`have`),
**independently verified** against the pinned oracle by the hermetic
`oracle_elab.rs` regression gate. The postponement scheduler that M4b's
fidelity ultimately rides on moves to M4b-3 with `elabApp` — its first
source producer (§ Amendment). User-facing value arrives when the
elaborator handles
enough of the language to elaborate a real declaration — an M4
milestone-level claim, not a per-slice one.

## Scope correction: `show` moves out of M4b-2

The M4b-1 roadmap table lists `show` under M4b-2. Inspection of the
pinned toolchain shows part of `show` depends on capabilities M4b-2 does
not have, exactly as num/char turned out not to be leaves during M4b-1
planning:

- `show $type by $tac` is expanded by a **macro** (`expandShow`,
  `BuiltinNotation.lean:109`) into `show $type from by $tac`, and then
  needs a **`by` tactic block**. Macro expansion in dispatch and tactic
  blocks are both explicitly-deferred capabilities.
- `show $type from $val` (`elabShow`, `BuiltinNotation.lean:114`) does
  **not** build an `Expr` directly. It elaborates `type`, then reflects
  the elaborated type back into `Syntax` via `exprToSyntax` and
  re-elaborates `have this : type := val; this`. `exprToSyntax` is a
  delaborator-class capability `leanr` does not have.

Shipping only the `from` arm via an Expr-level or syntax-level
re-derivation of the `have`-desugaring would leave `show` half-built in
M4b-2 and re-touch it when the `by` arm lands — the pipeline-churn we
otherwise avoid. **Decision:** `show` (both arms) moves to the slice that
first has macro expansion + `by`, where `expandShow`/`exprToSyntax` have
a natural home. The roadmap table above reflects this. M4b-2's binder
set is therefore **`fun` / `forall`(+`arrow`+`depArrow`) / `let` /
`have`**.

## Global constraints

- **Kernel/olean TCB is byte-untouched.** `leanr_kernel` continues to
  depend on no workspace crate. Its `LocalContext`
  (`mk_local_decl`/`mk_let_decl`/`save`/`restore`), `abstract_fvars`,
  and `mk_pi`/`mk_lambda` already exist and are reused as-is.
- **`leanr_meta/src` accessor precedent.** Per the amended M4b
  constraint (M4b-1 precedent: `MetaCtx::store()`/`store_mut()`), M4b-2
  may add purely-**additive**, **TCB-neutral**, **behavior-neutral**
  public accessors on `leanr_meta` that the `leanr_elab` layer genuinely
  needs. Any non-additive / behavior-changing `leanr_meta` change must
  still be flagged. M4b-2's additions are the plan-1 local-context
  accessor family (`lctx_checkpoint`/`push_local_decl`/`lctx_restore` +
  `mk_forall`, shipped) and plan 2's `mk_lambda`. `MVarDecl` reads
  (`mctx().decl`/`is_assigned`/`assignment`) are already public, so no new
  read-accessor is needed.
- **Named-seam discipline.** Every new dispatch arm is a named seam;
  unregistered kinds fall through to `ElabError::UnsupportedSyntax`
  (never a panic, never a wrong `ExprId`).
- **Oracle discipline.** Correctness is byte-for-byte agreement with the
  pinned oracle's canonical `Expr`, via `oracle_elab.rs`. The
  `lean-toolchain` pin is not bumped in this slice.

## Architecture

### The canonical entry-point pipeline

The eventual pipeline (M4b-3 onward) is:

```
elab_term(elem, expected)         // dispatch → leaf / binder elaborator
  → synthesize_synthetic_mvars()  // the fixpoint: drain postponed + pending-instance mvars
  → instantiate_mvars(e)          // final substitution before the oracle compare
```

That is the **eventual (M4b-3+) shape**. Through all of M4b-2 the entry
point stays M4b-1's `elab_term_ensuring_type → instantiate_mvars`, with
**no** `synthesize_synthetic_mvars` step — see § Amendment. The reason is
the dumper: `dump_elab.lean` elaborates every term with
`expectedType := none` and does **not** run the top-level unassigned-mvar
error report — it emits an unresolved hole as a bare `mvar` (committed
record `hole/bare` → `{"k":"mvar","i":0}`), not an error. Every M4b-2 term
(the three type-formers, `fun`, `let`/`have`) fully elaborates with no
synthetic mvar the fixpoint must drain — even `∀ (x : _), x` and
`fun x => x` emit a bare-`mvar` domain, no error, no scheduling. A
fixpoint step would be a pure no-op on every M4b-2 corpus entry, so it is
deferred to M4b-3, where `elabApp` first produces synthetic mvars from
source and the step becomes both necessary and differentially verifiable.
This respects the project's "no speculative surface" discipline (the same
reason M4b-1 deferred these fields and plan 1 shipped no thin fixpoint).

### Plan decomposition

M4b-2 is decomposed into three plans, each a single PR with its own
hermetic oracle tier extending `oracle_elab.rs` + `elab-queries.jsonl`,
mirroring M4a's rhythm (foundation → hard core → breadth):

| Plan | New capability | Oracle tier added |
|---|---|---|
| **Plan 1** (shipped, #28) | `MetaCtx` local-context accessor family (`lctx_checkpoint`/`push_local_decl`/`lctx_restore` + `mk_forall`); the three universal-quantifier forms `forall`/`arrow`/`depArrow`. **No** ladder fields and **no** fixpoint (the design's "thin fixpoint" was dropped: the oracle dumper emits an unresolved hole as a bare `mvar`, not an error, so there was nothing oracle-verifiable to ship). Entry point unchanged. | `∀`/`→`/`(x:A)→B` terms |
| **Plan 2** (this spec) | `fun` (`basicFun` arm) + `MetaCtx::mk_lambda`. **No scheduler** — see § Amendment. The postpone branch (expected = unassigned expr mvar) is a **named seam** unreachable from M4b-2 source. | `fun` terms (expected `None` and expected `∀`), incl. elided binder → bare-mvar domain |
| **Plan 3** | `let` + `have` (letE/letFun-family forms + expected-type propagation); no new scheduler machinery | `let` / `have` terms |

## Plan 1 — local-context foundation, scheduler seam, universal-quantifier forms

> **Superseded — historical (shipped as #28).** This section records the
> *original* plan-1 design. What actually shipped differs in two ways,
> both now canonical (see the plan-1 implementation plan and § Amendment):
> (1) the closure `with_local_decl(name, ty, bi, f)` sketched below became
> the flat `lctx_checkpoint` / `push_local_decl` / `lctx_restore` trio
> (the closure could not reach the outer `TermElabM` state); (2) the
> "TermElabM ladder fields" and "thin-but-real fixpoint" subsections were
> **not** built — the entry point stayed `elab_term_ensuring_type →
> instantiate_mvars`, since the dumper emits an unresolved hole as a bare
> `mvar` (no error to verify). The universal-quantifier forms and the
> `mk_forall` accessor shipped as described. Read the subsections below
> for context, not as the shipped surface.

### The `MetaCtx` accessor family (additive, TCB-neutral, behavior-neutral)

`MetaCtx` already holds an ambient `lctx: LocalContext` and
`fvar_gen: FVarIdGen`, both `pub(crate)`, both already consumed by
`infer_type`/`whnf`/`is_def_eq`; `assign.rs` already uses the
`save → mk_local_decl → restore` idiom internally. The elab layer cannot
reach these fields, so M4b-2 exposes a small family:

```rust
// Scope a cdecl: mint fvar (name : ty) into self.lctx, run f with it in
// scope, RESTORE lctx on EVERY exit path (Ok or Err). Exactly the
// save → mk_local_decl → restore idiom assign.rs uses internally.
pub fn with_local_decl<R>(
    &mut self, name: Option<NameId>, ty: ExprId, bi: BinderInfo,
    f: impl FnOnce(&mut MetaCtx, ExprId) -> Result<R, MetaError>,
) -> Result<R, MetaError>;

// Scope an ldecl (Plan 3 customer, designed now).
pub fn with_let_decl<R>(
    &mut self, name: Option<NameId>, ty: ExprId, val: ExprId,
    f: impl FnOnce(&mut MetaCtx, ExprId) -> Result<R, MetaError>,
) -> Result<R, MetaError>;

// Binder builders: abstract body over fvars, build the node. Thin
// wrappers over the kernel's abstract_fvars + mk_pi/mk_lambda, using
// the internal scratch + guard the elab layer cannot reach.
pub fn mk_forall(&mut self, fvars: &[ExprId], body: ExprId) -> Result<ExprId, MetaError>;
pub fn mk_lambda(&mut self, fvars: &[ExprId], body: ExprId) -> Result<ExprId, MetaError>;
pub fn mk_let_expr(&mut self, fvar: ExprId, ty: ExprId, val: ExprId, body: ExprId) -> Result<ExprId, MetaError>;
```

These are additive and behavior-neutral: they expose capability that
`leanr_meta` already exercises internally, add no new state, and change
no existing path. `base` handling (persistent-store dedup for interned
fvar/name/nat ids) is internal to each accessor, matching the kernel's
own `mk_local_decl` base parameter.

### TermElabM ladder fields (populated, not scaffolded)

The three M4b-1-deferred fields arrive with the code that uses them:

```rust
synthetic_mvars: Vec<SyntheticMVarDecl>,   // processed in registration order
mvar_error_infos: Vec<MVarErrorInfo>,      // ref syntax + kind, for the final error pass
let_recs_to_lift: Vec<LetRecToLift>,       // declared; no producer until `let rec` (later slice)
```

`let_recs_to_lift` has no M4b-2 producer (`let rec` is a later slice); it
is declared for structural parity with the oracle's `TermElabM` state and
carries a stated "no producer yet" note, not speculative logic.

### The thin-but-real fixpoint (Plan 1)

`synthesize_synthetic_mvars` is wired into the entry point in Plan 1.
Even before postponement exists it has a real job: after `elab_term`, it
walks unassigned mvars and, finding an unassigned `Natural` mvar minted
by an M4b-1 `_` hole with no assignment, records an `MVarErrorInfo` and
surfaces the oracle-faithful placeholder error. Its error tier is
therefore verifiable in Plan 1, before any postponement machinery.

### The universal-quantifier elaborators

The pinned toolchain splits the universal quantifier into **three**
builtin elaborators over three distinct syntax kinds — Plan 1 handles all
three, each its own named dispatch arm:

- `Lean.Parser.Term.forall` → `elabForall` (`Binders.lean:278`) — `∀ (x : T), B`
- `Lean.Parser.Term.arrow` → `elabArrow` (`Binders.lean:293`) — `A → B`
- `Lean.Parser.Term.depArrow` → `elabDepArrow` (`Binders.lean:310`) — `(x : A) → B`

They are first because they are pure type-formers: none postpones, and
each elaborates against `expected := Sort ?u` (never an arbitrary
expected type). Flow for `∀ (x : T), B` (the other two are the
elided-binder and single-binder shapes of the same telescope):

1. Parse binder group(s) → `(name, domain-syntax, BinderInfo)`.
2. Per binder: `dom = elab_term(domain, expected = Sort ?u_fresh)`;
   ensure it is a type (whnf to a sort, else oracle-faithful error).
3. `with_local_decl(name, dom, bi, |ctx, fvar| …)` — recurse into the
   next binder / the body under the extended context.
4. Body: `B = elab_term(body, expected = Sort ?)`, also ensured a type.
5. `mk_forall(&fvars, B)` abstracts and builds the nested `forallE`.

Multi-binder groups nest `with_local_decl` left-to-right, collect
`fvars` in order, then one `mk_forall` over all of them (matching the
kernel's telescope abstraction).

## Plan 2 — the `fun` elaborator (no scheduler)

Per § Amendment, the `synthesizeSyntheticMVars` fixpoint moves to M4b-3.
Plan 2 ships `fun` alone, in the two expected-type shapes reachable from
closed M4b-2 source, each differentially oracle-verified with **no**
synthetic-mvar machinery.

### The enabling fact

An unassigned binder-type mvar behaves exactly like an M4b-1 `_` hole:
`instantiate_mvars` leaves it as a bare `mvar`, and the oracle dumper
(`expectedType := none`) emits the same bare `mvar`. So `fun (x) => …`
with an elided, uninferrable binder type produces a `lam` whose domain is
a bare `mvar` — no error, no fixpoint. The shipped `mk_fresh_expr_mvar`
(M4b-1) is the binder-type source; nothing new is scheduled.

### Grammar (confirmed against leanr's own parser, `term.rs:461-528`)

```
fun      := ("λ" | "fun") (basicFun | matchAlts)
basicFun := many1(funBinder), optType, ("↦" | "=>"), body
funBinder := strictImplicit | implicit | instBinder | term@maxPrec
```

- Only the **`basicFun`** arm is in scope; the **`matchAlts`** arm
  (pattern-matching `fun`) is a **named seam** → the match slice (M4b-4).
- A `funBinder` is **not** an `explicitBinder` node. A bare ident (`x`)
  and a parenthesised binder (`(x : T)` / `(x)`) both arrive through the
  `term@maxPrec` alternative — `x` as a bare ident token, `(x : T)` as a
  `paren`/`typeAscription` **term** node. So `fun`'s binder extraction is
  its **own** logic, deliberately **not** a reuse of plan 1's
  `extract_binder_group` (which reads `explicitBinder`-family nodes).
- `strictImplicit` / `implicit` / `instBinder` funBinders → **named seam
  → M4b-3** (they need the implicit/instance-argument handling that
  arrives with `elabApp`); no corpus term uses them.
- **`optType`** (the `fun x : T => e` return-type ascription) → **named
  seam → M4b-3**; keeps plan 2 to the minimal oracle-coverable core.

### The `fun` elaborator

`Lean.Parser.Term.fun` → `elabFun` (`Binders.lean:678`) → `elabFunBinders`.
Whnf the expected type once, then:

- **expected is `∀ A, B` (after whnf):** per binder, take the domain from
  `A` (elided binder ⇒ `dom := A`; explicit `(x : T)` ⇒ elaborate `T` and
  `is_def_eq(T, A)`), scope `push_local_decl (x : dom)`, recurse on the
  telescope with expected `B`; body elaborated with the residual expected;
  `mk_lambda` over the collected fvars.
- **expected is None:** per binder, explicit `(x : T)` ⇒ elaborate `T`;
  elided `x` ⇒ fresh `mk_fresh_expr_mvar` domain (surfaces as a bare
  `mvar`); scope `push_local_decl`; body elaborated with expected None;
  `mk_lambda`.
- **expected is an unassigned expr mvar `?m` (after whnf):** the oracle's
  `postpone_elab_term` path. **Unreachable from any M4b-2 source term**
  (needs application to arise), so this branch is a **named seam** →
  M4b-3: it returns `ElabError::UnsupportedSyntax` with a
  "fun postponement requires application (M4b-3)" note rather than
  shipping a resume path the oracle cannot exercise this slice.

Binder scoping reuses plan 1's `lctx_checkpoint`/`push_local_decl`/
`lctx_restore` trio (restore on every exit path, `Err` included) exactly
as the `∀` telescope driver does.

### New accessor: `MetaCtx::mk_lambda` (additive, TCB-neutral)

The `mkLambdaFVars` twin of plan 1's `mk_forall`: the same
`abstract_fvars` + build loop, emitting `Expr::lam` instead of
`Expr::forallE`. Additive and behavior-neutral under the M4b accessor
precedent (`with_let_decl` / `mk_let_expr` remain plan 3's additions).

### Entry point / state: unchanged

No `synthesize_synthetic_mvars`, no ladder fields, no `may_postpone`
threading. The pipeline stays `elab_term_ensuring_type →
instantiate_mvars` exactly as plan 1 left it.

## Plan 3 — `let` and `have`

Neither form adds scheduler machinery; both build on the Plan 1 lctx
seam.

- **`let`** (`Lean.Parser.Term.let` → `elabLetDecl`, `Binders.lean:939`):
  `let x : T := v; body` → elaborate `T` as a type, `v` with expected
  `T`, scope `with_let_decl (x : T := v)`, elaborate `body` (expected
  propagated), build via `mk_let_expr` → `Expr.letE`. Elided type
  (`let x := v`) infers `T` from `v`.
- **`have`** (`Lean.Parser.Term.have` → `elabHaveDecl`,
  `Binders.lean:942`): same binder shape. Its exact output node — the
  `letFun`/`letE`-family shape and whether the value is retained — is
  **pinned against the oracle corpus during Plan 3**, not asserted here,
  since the `have`/`let_fun` desugaring is exactly the kind of "obvious"
  shape that M4b-1's num/char finding warns against guessing.

## Verification

- **Corpus.** `elab-queries.jsonl` grows one tier per plan
  (plan 1: `∀`/`→`/`(x:A)→B` — shipped; plan 2: `fun`; plan 3:
  `let`/`have`). Inputs stay **closed source-text** — `fun (x:A) => x`
  is closed even though its body elaborates under a local context — so
  the harness shape from M4b-1 carries over: leanr parse (its own
  parser) → elaborate → `instantiate_mvars` → byte-compare against the
  oracle's canonical `Expr` after canonicalization. (No
  `synthesize_synthetic_mvars` step — that pipeline change lands in
  M4b-3 with the fixpoint; see § Amendment.)
- **Plan 2 corpus terms** (all closed, all oracle-verified): `fun (x :
  Nat) => x`; `fun (x : Nat) (y : Nat) => x` (nested `lam`, body `bvar
  1`); `fun x => x` (elided → `lam` with a bare-`mvar` domain);
  `(fun x => x : Nat → Nat)` (∀ expected, elided domain from `A`);
  `(fun (x : Nat) => x : Nat → Nat)` (∀ expected, explicit domain via
  `is_def_eq`).
- **Regeneration.** The oracle-side dumper (`dump_elab.lean` behind
  `mise run fixtures:regen`) is extended with the new terms; the
  committed `Elab0.olean` gains any constants they reference. Hermetic —
  CI never installs Lean (`docs/ORACLE.md`).
- **Gate wiring.** The existing `oracle_elab.rs` regression gate runs
  under `mise run meta:fast` and plain `mise run test`; no new nightly.

## Error handling

- Every new dispatch arm (`forall`/`arrow`/`depArrow`/`fun`/`let`/`have`)
  is a named seam; unknown kinds still fall through to
  `UnsupportedSyntax`. Within `fun`, the `matchAlts` arm, the
  implicit/strict/instance funBinders, `optType`, and the
  expected-unassigned-mvar postpone branch are each their own named seam
  → M4b-3 / match slice (§ Plan 2).
- An elided, uninferrable `fun` binder type is **not** an error: it is a
  fresh mvar that `instantiate_mvars` leaves as a bare `mvar` (§ Plan 2
  enabling fact), matching the oracle dumper's `expectedType := none`
  emission. Type-mismatch on the `∀`-expected explicit-binder path flows
  through the existing `is_def_eq` seam (`ElabError::TypeMismatch`);
  coercion insertion on that mismatch is M4b-3.
- The plan-1 telescope bracket (`lctx_checkpoint` / `push_local_decl` /
  `lctx_restore`, and plan 3's `with_let_decl`) restores the local
  context on **every** exit path including `Err`, so a failed body
  elaboration never leaks a decl into the ambient `lctx`.
- The fixpoint's error pass (`mvarErrorInfos`) is deferred to M4b-3 with
  the rest of the scheduler (§ Amendment).

## Out of scope (each names the slice that owns it)

- application / `@` / named / optional args, coercions, num/char
  literals — M4b-3
- **the entire `synthesizeSyntheticMVars` fixpoint** (postponement
  resume, `TypeClass` drain, `synthesizeUsingDefault`, `mvarErrorInfos`),
  the `TermElabM` ladder fields, the entry-point pipeline change, and
  `mayPostpone` threading — M4b-3 (§ Amendment; each first gets a source
  producer and differential coverage there)
- `fun`'s `matchAlts` (pattern-matching) arm — M4b-4 / match slice;
  `fun` implicit/strict/instance funBinders and `optType` — M4b-3
- `elabAsElim`, dot notation, `binop%`, anonymous constructor `⟨⟩` —
  M4b-4
- macro expansion in dispatch, `by` tactic blocks, **`show`** (both
  arms), `suffices`, `let rec` / `let_recs_to_lift` producer — later M4
- `letI` / `haveI` / `let_delayed` (distinct builtin kinds) — not in
  this slice's binder set; a later slice as needed
