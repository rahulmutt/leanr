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
| **M4b-2 (this spec)** | binder elaborators (`fun`/`forall`+`arrow`+`depArrow`/`let`/`have`) + the `synthesizeSyntheticMVars` fixpoint |
| M4b-3 | the application elaborator (`elabApp`) + coercion insertion + num/char literals |
| M4b-4 | `elabAsElim`, dot notation, `binop%`, anonymous constructor `⟨⟩` |
| later M4 | macro expansion + `by` tactic blocks (**`show` lands here**, see § Scope correction), structure instances, match/equation compiler, `do` |

Pinned oracle: `leanprover/lean4:v4.33.0-rc1` (`lean-toolchain`). All
oracle citations below are against that toolchain's
`src/lean/Lean/{Elab,Parser}`.

## What M4b-2 ships — and the stated non-shipping

Like all of M4a and M4b-1, **M4b-2 does not ship independently useful
user value**, and this is recorded rather than papered over: an elaborator
that handles binders but not application still cannot elaborate a real
declaration. What M4b-2 delivers is a `leanr_elab` term elaborator for
binder forms plus a faithful postponement scheduler, **independently
verified** against the pinned oracle by the hermetic `oracle_elab.rs`
regression gate. User-facing value arrives when the elaborator handles
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
  still be flagged. M4b-2's additions are the `with_local_decl` accessor
  family (§ Plan 1) and, if needed, a read-accessor for `MVarDecl`
  (§ Plan 2).
- **Named-seam discipline.** Every new dispatch arm is a named seam;
  unregistered kinds fall through to `ElabError::UnsupportedSyntax`
  (never a panic, never a wrong `ExprId`).
- **Oracle discipline.** Correctness is byte-for-byte agreement with the
  pinned oracle's canonical `Expr`, via `oracle_elab.rs`. The
  `lean-toolchain` pin is not bumped in this slice.

## Architecture

### The canonical entry-point pipeline

The final pipeline is:

```
elab_term(elem, expected)         // dispatch → leaf / binder elaborator
  → synthesize_synthetic_mvars()  // the fixpoint: drain postponed + pending-instance mvars
  → instantiate_mvars(e)          // final substitution before the oracle compare
```

**The `synthesize_synthetic_mvars` step lands in Plan 2, not Plan 1** —
a correction discovered during planning against the actual dumper. The
oracle dumper (`dump_elab.lean`) elaborates every term with
`expectedType := none` and does **not** run the top-level unassigned-mvar
error report: it emits an unresolved top-level hole as a bare `mvar`
(committed record `hole/bare` → `{"k":"mvar","i":0}`), not an error. A
Plan-1 fixpoint that errored on unassigned holes would therefore diverge
from the oracle. Plan 1's terms (the three type-former forms) fully
elaborate with no synthetic mvars — even `∀ (x : _), x` emits a `pi`
whose domain is a bare `mvar`, no error. So Plan 1 keeps M4b-1's entry
point (`elab_term → instantiate_mvars`) unchanged; the pipeline step +
fixpoint arrive in Plan 2 with postponement and the matching
`withSynthesize` change to the dumper. Inserting a step that is a no-op
for Plan 1 terms keeps every Plan 1 corpus entry green, so deferring it
costs no re-verification — and it respects the project's "no speculative
surface" discipline (the same reason M4b-1 deferred these fields).

### Plan decomposition

M4b-2 is decomposed into three plans, each a single PR with its own
hermetic oracle tier extending `oracle_elab.rs` + `elab-queries.jsonl`,
mirroring M4a's rhythm (foundation → hard core → breadth):

| Plan | New capability | Oracle tier added |
|---|---|---|
| **Plan 1** | `MetaCtx` `with_local_decl` accessor family; TermElabM ladder fields; canonical entry point with a real-but-thin fixpoint (drains nothing postponed yet; reports unassigned `_` holes); the three universal-quantifier forms `forall`/`arrow`/`depArrow` | `∀`/`→`/`(x:A)→B` terms; unassigned-hole error parity |
| **Plan 2** | the `synthesizeSyntheticMVars` **fixpoint proper** (postponed-term resumption, pending- + default-instance draining, `mvarErrorInfos`); `fun` (its first real customer) | `fun` terms; postpone→resume terms |
| **Plan 3** | `let` + `have` (letE/letFun-family forms + expected-type propagation); no new scheduler machinery | `let` / `have` terms |

## Plan 1 — local-context foundation, scheduler seam, universal-quantifier forms

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

## Plan 2 — the `synthesizeSyntheticMVars` fixpoint and `fun`

This plan concentrates M4b's stated fidelity risk. It mirrors the
oracle's `synthesizeSyntheticMVars` exactly.

### State

```rust
struct SyntheticMVarDecl { mvar: MVarId, ref_syntax: SynElem, kind: SyntheticMVarKind }

enum SyntheticMVarKind {
    TypeClass,                 // pending instance search (built now; see stated exception)
    Postponed { expected: Option<ExprId>, lctx: LocalContext, level_names: Vec<NameId> },
    // Coe { … }    → M4b-3       (named, not built)
    // Tactic { … } → later M4    (named, not built)
}
```

A `Postponed` decl carries its **own** `lctx` snapshot (like an mvar's
declared local context): the fixpoint runs at the entry point after the
outer elaboration has already restored the ambient `lctx`, so resumption
must restore the saved context rather than assume the ambient one.
`SynElem` is a rowan `NodeOrToken` (a cheap Arc-backed cursor), so
capturing `ref_syntax` is cheap.

### The fixpoint

`synthesize_synthetic_mvars` (oracle `synthesizeSyntheticMVars`), run
once at the entry point after `elab_term`, before `instantiate_mvars`:

1. **Step pass** — walk `synthetic_mvars` in registration order; per
   pending, unassigned mvar dispatch on kind:
   - `TypeClass` → run the already-shipped `mctx.synth_instance(ty)`;
     assign + drop on success, keep if stuck.
   - `Postponed { expected, lctx, level_names }` → **resume**: restore
     the saved `lctx`/`level_names`, re-run
     `elab_term(ref_syntax, expected, may_postpone = false)`,
     `is_def_eq`-assign the result into the mvar. A resumption that no
     longer postpones is progress.
   - Track whether the pass assigned anything.
2. **No progress + may_postpone** → `synthesize_using_default` (apply
   default instances at successively lower priority,
   `may_postpone = false`); if it assigns anything, loop to step 1.
3. **Still stuck** → drain `mvar_error_infos` into oracle-faithful
   errors ("don't know how to synthesize implicit argument" /
   placeholder).
4. **Termination:** every pass either strictly shrinks the pending set
   or transitions to the default→error phase; the pending set is finite
   and never grows during synthesis, so the loop is bounded.

If reading a pending `TypeClass` mvar's goal type requires an `MVarDecl`
read that `leanr_meta` does not already expose, Plan 2 adds an
additive read-accessor under the accessor precedent.

### The `fun` elaborator

`Lean.Parser.Term.fun` → `elabFun` (`Binders.lean:678`) → `elabFunBinders`.
The fixpoint's first real customer:

- **expected is `∀ A, B` (after whnf):** match the binder domain against
  `A` (explicit binder type ⇒ `is_def_eq dom A`; elided ⇒ `dom := A`),
  elaborate the body with expected `B` under `with_local_decl (x : dom)`,
  then `mk_lambda`.
- **expected is an unassigned mvar `?m`:** `postpone_elab_term` — mint a
  `Postponed` synthetic mvar capturing
  `(ref_syntax, expected, lctx.clone(), level_names.clone())`, return it
  as the result. The outer elaboration proceeds; the fixpoint resumes it
  once `?m` is (maybe) assigned.
- **expected is None:** each binder elaborated by its explicit type
  (elided-and-uninferrable ⇒ oracle-faithful "failed to infer binder
  type" error), body with expected None; `mk_lambda`.

### Stated exception: `TypeClass` has no M4b-2 source producer

M4b-2 has no application elaborator, so nothing **creates** a `TypeClass`
synthetic mvar from source — instance arguments arrive with `elabApp` in
M4b-3. Per the "full ladder now" scope decision, the `TypeClass` +
default-instance drain code is **built** in Plan 2 but has **no green
entry in the differential corpus** this slice. It is instead covered by
a targeted `leanr_elab` unit test that directly injects a `TypeClass`
synthetic mvar over a real instance goal (e.g. `Inhabited Nat`) and
asserts the fixpoint drains it via `synth_instance`. The
oracle-differential corpus exercises only `Postponed` (via `fun`) in this
slice. This mirrors M4b-1's stated-exception discipline.

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
  (`∀`/`→`/`(x:A)→B`; `fun` + postpone→resume; `let`/`have`). Inputs
  stay **closed source-text** — `fun (x:A) => x` is closed even though
  its body elaborates under a local context — so the harness shape from
  M4b-1 carries over: leanr parse (its own parser) → elaborate →
  `synthesize_synthetic_mvars` → `instantiate_mvars` → byte-compare
  against the oracle's canonical `Expr` after canonicalization.
- **Regeneration.** The oracle-side dumper (`dump_elab.lean` behind
  `mise run fixtures:regen`) is extended with the new terms; the
  committed `Elab0.olean` gains any constants they reference. Hermetic —
  CI never installs Lean (`docs/ORACLE.md`).
- **The `TypeClass`/default-instance drain** is covered by the targeted
  unit test (§ Plan 2 stated exception), not the differential corpus.
- **Gate wiring.** The existing `oracle_elab.rs` regression gate runs
  under `mise run meta:fast` and plain `mise run test`; no new nightly.

## Error handling

- Every new dispatch arm (`forall`/`arrow`/`depArrow`/`fun`/`let`/`have`)
  is a named seam; unknown kinds still fall through to
  `UnsupportedSyntax`.
- New oracle-faithful `ElabError` variants as needed: unassigned-mvar /
  placeholder (Plan 1), "failed to infer binder type" for elided,
  uninferrable `fun` binders (Plan 2), type-mismatch via the existing
  `ensure_has_type` → `is_def_eq` seam.
- `with_local_decl` / `with_let_decl` restore the local context on
  **every** exit path including `Err`, so a failed body elaboration never
  leaks a decl into the ambient `lctx`.
- The fixpoint's error pass (`mvar_error_infos`) reports remaining
  unassigned synthetic mvars with the oracle's message shape, verified by
  the error-parity corpus entries.

## Out of scope (each names the slice that owns it)

- application / `@` / named / optional args, coercions, num/char
  literals — M4b-3
- `elabAsElim`, dot notation, `binop%`, anonymous constructor `⟨⟩` —
  M4b-4
- macro expansion in dispatch, `by` tactic blocks, **`show`** (both
  arms), `suffices`, `let rec` / `let_recs_to_lift` producer — later M4
- `letI` / `haveI` / `let_delayed` (distinct builtin kinds) — not in
  this slice's binder set; a later slice as needed
