# M4b-4a P4 — identifier forms Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** The last three dot-notation forms elaborate as the pinned oracle does:
- dotted identifiers that end in fields: `fun (x : Nat) => x.succ` is `Nat.succ x`, and `Nat.zero.succ` is `Nat.succ Nat.zero`;
- the pipeline projection: `p |>.2` is `p.snd`;
- the dot identifier: `Nat.succ .zero` is `Nat.succ Nat.zero`.

A named pattern outside a pattern gets the oracle's error. After this plan, no seam in the crate names M4b-4a.

**Architecture:**
- `resolve.rs` gains the reduced `resolveLocalName` / `resolveGlobalName`. Each takes the interned prefixes of a dotted identifier and returns the resolved local or constant plus the number of trailing components that are fields.
- `app/head.rs`:
  - The identifier arm becomes `elab_app_fn_id`, a port of `elabAppFnId` → `resolveName` → `elabAppFnResolutions`. The first field `LVal` carries `suffix`.
  - It gains `pipeProj`, `dotIdent` and `namedPattern` arms.
- New `app/dot_ident.rs` ports `resolveDottedIdentFn`, with `withForallBody` and `whnfCoreUnfoldingAnnotations`.
- `app/lval.rs` gains the two `c ++ suffix` unknown-constant arms.
- `dispatch.rs` routes `pipeProj`, `dotIdent` and `namedPattern`.
- No `leanr_meta` change: every accessor used is already `pub`.

**Tech Stack:** Rust (`leanr_elab` only), Lean 4 `v4.33.0-rc1` as the differential oracle, `mise` tasks.

**Spec:** `docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md`. Before starting any task, read § P4, § Errors, § Seams after P4, § Testing, the P2 and P3 amendments under § Next, and all of § Landed.

## Decisions taken while planning

- **The `numScopeArgs` gap is routed around, not fixed** (user decision, 2026-09-30, carried over from P3). If a record below fails in leanr for a reason that is not P4's:
  1. Check out `main`, rebuild, and confirm the same failure with the nearest P1–P3-reachable form of the term (for example `(x).f` for `x.f`).
  2. Drop the record from `p4Queries`.
  3. Write the term, leanr's error and the confirming command into the task report, and into spec § Landed › P4's follow-ups (Task 4).

  Never patch `leanr_meta`'s defeq in this slice. Every record below was run through `dump_elab.lean`'s own entry point while planning, against the Task 1 fixture.
- **Identifier splitting keeps `intern_dotted`'s convention.** That means split on every `.` and keep `«»` verbatim.
  - The reason is that binder names are interned whole, as ONE component (`builtin/binder/mod.rs`'s `intern_binder_name`). An identifier's first prefix therefore finds a binder of the same text only if both sides keep the escapes.
  - Unescaping only the identifier side would break `fun («x» : Nat) => «x»`, which works today.
  - Escape handling stays P1's open follow-up ("`«»` escapes in identifiers are not handled"). Measured consequence: the oracle accepts `fun («x» : Nat) => x.succ`, `Nat.«zero».succ` and `fun (s : S2) => s.«toS1».a`; leanr keeps rejecting them. These are reject-only divergences, and Task 4 records them.

## Spec deviations (found while planning, all measured)

Task 4 records each of these in the spec as a P4 amendment.

1. **`resolveDottedIdentFn`'s local-context candidate is not ported** (`App.lean:2034-2037`).
   - It resolves `fullName = C ++ id`, which always has two or more components. Oracle locals are atomic: `ensureAtomicBinderName`, `Binders.lean:188-191`, measured as "invalid binder name `x.a`, it must be atomic". So only an auxiliary `let rec`/`where` declaration can match.
   - leanr's local context holds none, and leanr's binder names are single components, so the arm is unreachable in both.
   - This follows the P3 `AmbiguousField` precedent: it is owned by the `let rec`/`where` slice together with the declarations that reach it. Its `throwInvalidExplicitUniversesForLocal` (`:2035-2036`) goes with it.
2. **New variant: `InvalidExplicitUniversesForLocal`** (`TermElabM.lean:2160-2161`), raised by `resolveName`'s `processLocal` (`:2172-2179`).
   - Today leanr silently drops the levels on `fun (x : Nat) => x.{0}` and elaborates `x`. The oracle rejects it: "invalid use of explicit universe parameters, `x` is a local variable".
   - This is a silent over-acceptance, and P4 closes it.
3. **New variant: `NamedPatternOutsidePattern { as_function }`**. The oracle has two throw sites, and they were measured:
   - `fun (x : Nat) => x@Nat.zero` gives `elabNamedPatternErr`'s message (`BuiltinTerm.lean:443-444`). `elabNamedPattern := elabAtom` (`App.lean:2247`) is registered too, but it is not the one that answers.
   - `fun (x : Nat) => x@Nat.succ Nat.zero` gives `elabAppFn`'s "Expected a function, but found the named pattern" (`App.lean:2098-2100`).
4. **`LVal::FieldName.suffix` is the rejoined field text (`Option<String>`), and `fullRef` is not added.**
   - `suffix?` only feeds the unknown-constant error `c ++ suffix` (`App.lean:1584-1586`, `:1606-1608`), whose leanr form is `UnknownIdent(String)`.
   - `fullRef` is only the error position (UI).
5. **Reserved names are a named follow-up, not a seam.** The oracle's `realizeGlobalName` (`TermElabM.lean:2189`) realizes reserved names on demand: `pick.eq_1` elaborates to the equation lemma (measured). leanr splits it into `pick` plus a field `eq_1` and reports `UnknownIdent("pick.eq_1")`. This is reject-only. Owner: the slice that grows `resolve_global`.
6. **`whnfCoreUnfoldingAnnotations` is ported, but nothing observable depends on it.** An annotated expected type that it would unfold (`optParam Nat Nat.zero`) fails as a namespace (`optParam.zero`) and reaches the same constant through the `unfoldDefinition?` retry. Only the oracle's logged intermediate errors differ, and leanr has no log (the existing § Seams row).
7. **`resolveLocalName`'s longest-prefix order is not observable.** With single-component local names only one prefix can ever match. The loop is ported as the oracle writes it.

## Global Constraints

- The oracle is `leanprover/lean4:v4.33.0-rc1` (`lean-toolchain`). Never bump it.
- Before writing an oracle `file:line` citation into code or tests, open it against `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/Lean/...`. Every citation in this plan was opened while writing it. Citations in this repo drift by 1–2 lines, so re-open any you copy anyway.
- `leanr_meta` and `leanr_kernel` are untouched.
- No new dependencies.
- Named-seam discipline:
  - A construct owned by a later slice raises `ElabError::UnsupportedSyntax` naming its owner.
  - A genuine oracle error gets a typed variant.
  - Every new variant in this plan is an oracle error. `ElabError::is_oracle_error` (`error.rs:234`) lists only the non-oracle variants, so it needs no change, and `resolve_lval_loop` and the dot-identifier retry both retry on new variants.
- Every committed `elab-queries.jsonl` record stays byte-identical except those this plan adds. Check with `git diff tests/fixtures/elab/elab-queries.jsonl | grep '^-[^-]'`, which must print nothing.
- **Every new test is shown to discriminate.** The implementer applies the mutation named in the task, watches the test go red, reverts, and records the command and its output in the task report.
  - This repo's plans have repeatedly named mutations their tests do not kill. Treat every "Mutation" line below as a hypothesis until you have run it.
  - If a mutation survives, strengthen the test. Never delete the mutation.
- Before every push: `mise run ci`, blocking, to completion (fmt, clippy, full suite). A subagent must not background it: run it in the foreground and wait for `CI_EXIT`.
- Build only under `/workspace`, never `/tmp` (a 20Gi EmptyDir; a second cargo target there got the pod evicted).
- Fixture regeneration (never `mise run fixtures:regen`, which also touches Mathlib):
  ```
  cd tests/fixtures/elab && lean Elab0.lean -o Elab0.olean && cd ../../.. && mise run fixtures:regen-elab
  ```
- Oracle checks use a prelude-mode scratch file in the scratchpad (never committed):
  ```
  prelude
  import Elab0
  set_option pp.explicit true
  set_option pp.fieldNotation false
  #check <term>
  ```
  Run it as `cd tests/fixtures/elab && LEAN_PATH=$PWD lean /path/to/Chk.lean`. Quote the oracle's message beside every rejection assertion.
- Tree shapes quoted below come from `./target/debug/leanr parse --dump <file>` run on `#check` lines, which prints the canonical tree. If a shape helper returns `IllFormedSyntax` on a well-formed input, print `non_trivia_children` of the node in a scratch test and fix the helper; do not change the parser.

## Review Focus

These are the five failure modes most likely to bite a user that no happy-path record would catch without a deliberate test. Each has a test, added in the owning task.

1. **A local shadows a global even when the whole dotted name is a declared constant.** `resolveName` tries every local prefix before any global (`TermElabM.lean:2180-2181`). So `fun (Nat : Nat) => Nat.succ` is `Nat.succ Nat` (a `Nat`), not the constant `Nat.succ` (a function). Record `p4/local-shadows-global`, Task 1.
2. **Explicit universes attach to the LAST field, never to the resolved constant or local** (`mkConsts`, `TermElabM.lean:2148`; `processLocal`, `:2172-2179`).
   - `polyZero.val.{0}` elaborates.
   - `polyZero.{0}` is "too many explicit universe levels".
   - `fun (x : Nat) => x.{0}` is an error, not a silently dropped level.
   - Task 1.
3. **The `c ++ suffix` unknown-constant error needs a constant base and belongs to the first field only** (`App.lean:1584-1586`, `:1606-1608`).
   - `Nat.succ.foo` → `UnknownIdent("Nat.succ.foo")`.
   - `fun (f : Nat -> Nat) => f.foo` → `InvalidField` naming `Function.foo`, because the base is an fvar.
   - `fun (s : S1) => s.imp.succ` → `InvalidField` naming `Function.succ`, because the second field has no suffix.
   - Task 1.
4. **A `.c` under a pi-typed expected type must not leak the telescope's binders.** `withForallBody` enters `(y : Nat) → Nat` with an fvar named `y`, and that fvar must be gone afterwards. `(fun (g : (y : Nat) -> Nat) (n : Nat) => n) .succ y` is "Unknown identifier `y`" in the oracle. Task 3.
5. **A `.c` whose expected type is not known yet postpones, then resumes.**
   - `Eq .zero Nat.zero` elaborates once the second argument fixes `α` (record `p4/dot-postponed`).
   - When the type never becomes known, the answer is `InvalidDottedIdent { NoExpectedType }`, not a stuck mvar or a seam: `(fun x => x) .zero`, `.zero`, `@.succ`.
   - Task 3.

---

## Measured oracle behaviour (the corpus and rejections below)

Every row was run with the scratch-file recipe above. The `polyZero` rows ran against the Task 1 fixture.

| Term | Oracle (`pp.explicit`) |
|---|---|
| `fun (p : Prod Nat Nat) => p.fst` | `fun p => @Prod.fst Nat Nat p` |
| `fun (p : Prod Nat Nat) => p.fst.succ` | `fun p => Nat.succ (@Prod.fst Nat Nat p)` |
| `fun (s : S3) => s.a` | `fun s => S1.a (S2.toS1 (S3.toS2 s))` |
| `fun (x : Nat) => x.succ` | `fun x => Nat.succ x` |
| `fun (s : S1) => s.addTo Nat.zero` | `fun s => S1.addTo Nat.zero s` |
| `fun (s : S1) => s.addTo` | `fun s n => S1.addTo n s` |
| `fun (x : Poly Nat) => x.val.{0}` | `fun x => @Poly.val.{0} Nat x` |
| `fun (x : S3Alias) => x.a` | `fun x => S1.a (S2.toS1 (S3.toS2 x))` |
| `fun (f : Nat → Nat) => f.twice` | `fun f => Function.twice f` |
| `fun (Nat : Nat) => Nat.succ` | `fun Nat => _root_.Nat.succ Nat` |
| `Nat.zero.succ` / `Nat.zero.succ.succ` | `Nat.succ Nat.zero` / `Nat.succ (Nat.succ Nat.zero)` |
| `Nat.succ.twice` | `Function.twice Nat.succ` |
| `polyZero.val` / `polyZero.val.{0}` | `@Poly.val.{0} Nat polyZero` (both) |
| `fun (p : Prod Nat Nat) => p \|>.2` | `fun p => @Prod.snd.{0, 0} Nat Nat p` |
| `fun (p : Prod Nat Nat) => p \|>.1.{0}` | `fun p => @Prod.fst.{0, 0} Nat Nat p` |
| `fun (s : S1) => s \|>.addTo Nat.zero` | `fun s => S1.addTo Nat.zero s` |
| `fun (s : S1) => s \|>.addTo (n := Nat.zero)` | `fun s => S1.addTo Nat.zero s` |
| `fun (s : S1) => s \|>.addTo` | `fun s n => S1.addTo n s` |
| `Nat.zero \|>.succ` | `Nat.succ Nat.zero` |
| `fun (x : Poly Nat) => x \|>.val.{0}` | `fun x => @Poly.val.{0} Nat x` |
| `fun (p : Prod Nat Nat) => p \|>.1 \|>.succ` | `fun p => Nat.succ (@Prod.fst.{0, 0} Nat Nat p)` |
| `fun (p : Prod Nat Nat) => p \|>.fst.succ` | same |
| `(fun x => x \|>.1) (Prod.mk Nat.zero Nat.zero)` | `(fun x => @Prod.fst.{0, 0} Nat Nat x) (@Prod.mk.{0, 0} Nat Nat Nat.zero Nat.zero)` |
| `(.zero : Nat)` / `Nat.succ .zero` | `Nat.zero` / `Nat.succ Nat.zero` |
| `Function.twice .succ Nat.zero` | `Function.twice Nat.succ Nat.zero` |
| `(.succ : Nat → Nat)` / `(.succ : Nat → NatAlias)` | `Nat.succ` (both) |
| `(.zero : NatAlias)` / `withDefault .zero` | `Nat.zero` / `withDefault Nat.zero` |
| `Eq .zero Nat.zero` | `@Eq.{1} Nat Nat.zero Nat.zero` |
| `(.mk Nat.zero Nat.zero : Prod Nat Nat)`, the `@.mk Nat Nat …`, `.mk.{0,0}`, `.mk.{0}` and `.mk .zero .zero` forms | `@Prod.mk.{0, 0} Nat Nat Nat.zero Nat.zero` |
| `(.mk : Nat → Nat → Prod Nat Nat)` | `@Prod.mk.{0, 0} Nat Nat` |

Rejections:

| Term | Oracle message |
|---|---|
| `fun (x : Nat) => x.{0}` | "invalid use of explicit universe parameters, `x` is a local variable" |
| `fun (x : Nat) => x.foo`, `Nat.zero.foo`, `fun (p : Prod Nat Nat) => p.fst.foo` | "Invalid field `foo`: The environment does not contain `Nat.foo` …" |
| `fun (f : Nat → Nat) => f.foo` | "… does not contain `Function.foo` …" |
| `fun (s : S1) => s.imp.succ` | "… does not contain `Function.succ` … from an expression @S1.imp s" |
| `Nat.foo` / `Nat.foo.bar` / `Nat.succ.foo` / `Nat.rec.foo` | "Unknown constant `Nat.foo`" / "`Nat.foo.bar`" / "`Nat.succ.foo`" / "`Nat.rec.foo`" |
| `Nat.zero.succ.{0}` | "too many explicit universe levels for `Nat.succ`" |
| `polyZero.{0}` | "too many explicit universe levels for `polyZero`" |
| `fun (x : Poly Nat) => x.val.{0,0}` | "too many explicit universe levels for `Poly.val`" |
| `pick.eq_1` | ACCEPTED: `pick.eq_1 (x y : Nat) : @Eq Nat (pick x y) x` (deviation 5) |
| `fun (p : Prod Nat Nat) => p \|>.3` | "Invalid projection: Index `3` is invalid for this structure; it must be between 1 and 2" |
| `fun x => x \|>.1` | "Invalid projection: Type of x is not known; cannot resolve projection `1`" |
| `fun (x : Nat) => x \|>.succ.{0}` | "too many explicit universe levels for `Nat.succ`" |
| `fun (x : Nat) => x@Nat.zero` | "`<identifier>@<term>` is a named pattern and can only be used in pattern matching contexts" |
| `fun (x : Nat) => x@Nat.succ Nat.zero` | "Expected a function, but found the named pattern x@Nat.succ" |
| `(.a.b : Nat)` | "Invalid dotted identifier notation: The name `a.b` must be atomic" |
| `.zero`, `(fun x => x) .zero` | "Invalid dotted identifier notation: The expected type of `.zero` could not be determined" |
| `(.foo : Type)` | "Invalid dotted identifier notation: Not supported on type universe" |
| `fun (α : Type) (f : α → Nat) => f .foo` | "… The expected type of `.foo` α is not of the form `C ...` or `... → C ...` where C is a constant" |
| `Nat.succ .foo` | "Unknown constant `Nat.foo`" |
| `(.foo : NatAlias)` | "Unknown constant `NatAlias.foo`" then "Unknown constant `Nat.foo`" (both logged; the LAST is thrown) |
| `(.zero : S3Alias)` / `(.zero : Prod Nat Nat)` | "Unknown constant `S3.zero`" (last) / "`Prod.zero`" |
| `(.zero.{0} : Nat)` | "too many explicit universe levels for `Nat.zero`" |
| `(fun (g : (y : Nat) -> Nat) (n : Nat) => n) .succ y` | "Unknown identifier `y`" |

---

## File Structure

| File | Responsibility | Task |
|---|---|---|
| `tests/fixtures/elab/Elab0.lean`, `Elab0.olean` | `polyZero` | 1 |
| `crates/leanr_elab/src/resolve.rs` | `resolve_local_name`, `resolve_global_name` (replace `resolve_global`) | 1 |
| `crates/leanr_elab/src/app/head.rs` | `elab_app_fn_id`, `intern_prefixes`, `field_lvals`, `pipe_proj_parts`, the pipeProj / namedPattern / dotIdent arms | 1, 2, 3 |
| `crates/leanr_elab/src/app/lval.rs` | `LVal::FieldName.suffix`, the two `c ++ suffix` arms; `node`/`app_fn`/`render` to `pub(super)` | 1, 3 |
| `crates/leanr_elab/src/elab.rs` | `local_ident_of` through `resolve_local_name` | 1 |
| `crates/leanr_elab/src/error.rs` | `InvalidExplicitUniversesForLocal`, `NamedPatternOutsidePattern`, `InvalidDottedIdent` + reason | 1, 2, 3 |
| `crates/leanr_elab/src/app/mod.rs` | `elab_pipe_proj`; `@.f` in `peel_head` / `elab_explicit` | 2, 3 |
| `crates/leanr_elab/src/app/dot_ident.rs` (new) | `resolve_dotted_ident_fn`, `with_forall_body`, `whnf_core_unfolding_annotations` | 3 |
| `crates/leanr_elab/src/dispatch.rs` | routing + registration of the three kinds | 2, 3 |
| `crates/leanr_elab/src/lib.rs` | export `InvalidDottedIdentReason` | 3 |
| `crates/leanr_elab/tests/lval_smoke.rs` | P4 rejections | 1, 2, 3 |
| `crates/leanr_elab/tests/seam_audit.rs` | flipped seam cases, `M4b-4a P4` needle | 2, 3, 4 |
| `crates/leanr_elab/tests/oracle_elab.rs` | corpus floor | 1, 2, 3 |
| `tests/fixtures/elab/dump_elab.lean`, `elab-queries.jsonl` | `p4Queries` | 1, 2, 3 |
| spec § Next (P4 amendments), § Landed › P4 | record | 4 |

---

### Task 1: The field split in identifiers (`resolveName`)

**Files:**
- Modify: `tests/fixtures/elab/Elab0.lean` (append after `end P3`, the file's last line); regenerate `Elab0.olean`
- Modify: `crates/leanr_elab/src/resolve.rs` (whole file)
- Modify: `crates/leanr_elab/src/app/head.rs` (ident arm `:79-89`, `elab_ident_head` `:238-338`, proj arm `:109-129`, `intern_components` `:440-455`, unit test `:541-589`)
- Modify: `crates/leanr_elab/src/app/lval.rs` (`LVal` `:16-33`, `resolve_lval_aux` Forall arm `:354-378`, catch-all arms `:387-390`)
- Modify: `crates/leanr_elab/src/elab.rs` (`local_ident_of` `:588-615`)
- Modify: `crates/leanr_elab/src/error.rs` (one variant)
- Modify: `tests/fixtures/elab/dump_elab.lean` (`p4Queries`, `main`'s list), `tests/fixtures/elab/elab-queries.jsonl` (regenerated)
- Modify: `crates/leanr_elab/tests/oracle_elab.rs` (floor), `crates/leanr_elab/tests/lval_smoke.rs`

**Interfaces:**
- Produces, in `resolve.rs`:
  - `pub fn resolve_local_name(mctx: &MetaCtx, prefixes: &[NameId]) -> Option<(ExprId, usize)>`
  - `pub fn resolve_global_name(view: &EnvView, prefixes: &[NameId], display: &str) -> Result<(NameId, usize), ElabError>`

  In both, `prefixes[k]` names the identifier's first `k + 1` components, and the `usize` is the number of trailing components that are fields.
- Produces, in `head.rs`:
  - `pub(crate) fn intern_prefixes(elab: &mut TermElabM, parts: &[&str]) -> Result<Vec<NameId>, ElabError>`. `intern_components` becomes its last element.
  - `fn field_lvals(field: &SynElem, kinds: &KindInterner, levels: &[LevelId]) -> Result<Vec<LVal>, ElabError>`. Task 2 reuses it.
- Produces: `LVal::FieldName { r#ref, name, levels, suffix: Option<String> }`. Every existing constructor passes `suffix: None`.
- Produces: `ElabError::InvalidExplicitUniversesForLocal(ExprId)`.

- [ ] **Step 1: Add the fixture declaration**

Append to `tests/fixtures/elab/Elab0.lean`:

```lean

-- === M4b-4a P4: identifier forms ===
-- A GLOBAL constant of a universe-polymorphic structure type:
-- `polyZero.val.{0}` puts the explicit level on the FIELD (`mkConsts`,
-- TermElabM.lean:2148), not on `polyZero`, which has no level params.
def polyZero : Poly Nat := Poly.mk Nat.zero
```

Run:
```bash
cd tests/fixtures/elab && lean Elab0.lean -o Elab0.olean && cd ../../.. \
  && mise run fixtures:regen-elab \
  && git diff --stat tests/fixtures/elab/elab-queries.jsonl tests/fixtures/elab/structures.jsonl
```
Expected: the olean builds, with only the pre-existing unused-variable warnings, and neither `.jsonl` changes (`polyZero` is a `def`, not a structure).

- [ ] **Step 2: Write the failing corpus records**

In `tests/fixtures/elab/dump_elab.lean`, after `p3Queries`:

```lean
-- M4b-4a P4: identifier forms (`resolveName`'s field split,
-- TermElabM.lean:2170-2192; `elabAppFnResolutions`, App.lean:1926-1950;
-- `pipeProj`, App.lean:2085-2097, :2250-2258; `resolveDottedIdentFn`,
-- App.lean:1985-2058). Every source was run through this file's own
-- entry point while planning (plan § Measured oracle behaviour).
def p4Queries : List (String × String) :=
  [ ("p4/local-field",          "fun (p : Prod Nat Nat) => p.fst")
  , ("p4/local-field-chain",    "fun (p : Prod Nat Nat) => p.fst.succ")
  , ("p4/local-inherited",      "fun (s : S3) => s.a")
  , ("p4/local-method",         "fun (x : Nat) => x.succ")
  , ("p4/local-method-arg",     "fun (s : S1) => s.addTo Nat.zero")
  , ("p4/local-method-eta",     "fun (s : S1) => s.addTo")
  , ("p4/local-univ-last",      "fun (x : Poly Nat) => x.val.{0}")
  , ("p4/local-alias",          "fun (x : S3Alias) => x.a")
  , ("p4/local-function",       "fun (f : Nat -> Nat) => f.twice")
  , ("p4/local-shadows-global", "fun (Nat : Nat) => Nat.succ")
  , ("p4/global-field",         "Nat.zero.succ")
  , ("p4/global-field-chain",   "Nat.zero.succ.succ")
  , ("p4/global-function",      "Nat.succ.twice")
  , ("p4/global-field-plain",   "polyZero.val")
  , ("p4/global-univ-last",     "polyZero.val.{0}")
  ]
```

Append `++ p4Queries` to the query list in `main` (the `for (id, src) in … ++ p3Queries do` line). Regenerate:

```bash
mise run fixtures:regen-elab 2>&1 | tail -5 \
  && wc -l tests/fixtures/elab/elab-queries.jsonl \
  && git diff tests/fixtures/elab/elab-queries.jsonl | grep '^-[^-]'
```
Expected:
- no `dump_elab: … error` lines;
- `249` lines (234 + 15);
- the grep prints nothing.

In `crates/leanr_elab/tests/oracle_elab.rs`, raise `CORPUS_FLOOR` to 249 and add under the P3 lines: `// 234 -> 249 (M4b-4a P4 task 1): the 15 p4/local-* and p4/global-* records.`

Run: `cargo test -p leanr_elab --test oracle_elab 2>&1 | tail -30`
Expected: FAIL. Every `p4/local-*` and `p4/global-*` record reports `UnknownIdent`, except `p4/local-shadows-global`, which reports a term mismatch: leanr resolves the full global `Nat.succ` today.

- [ ] **Step 3: Write the failing rejection tests**

Append to `crates/leanr_elab/tests/lval_smoke.rs`:

```rust
/// M4b-4a P4: the field split in identifiers (`resolveName`,
/// TermElabM.lean:2170-2192; `elabAppFnResolutions`, App.lean:1926-1950).
/// Each message is the pinned oracle's (plan § Measured oracle behaviour).
#[test]
fn identifier_field_split_rejections_match_the_oracle() {
    // A field that is neither a structure field nor a method. The base
    // `Nat.zero`'s type is the constant `Nat`, so the structure arm
    // answers (App.lean:1578), not the suffix arm. "Invalid field `foo`:
    // The environment does not contain `Nat.foo`"
    for src in [
        "fun (x : Nat) => x.foo",
        "Nat.zero.foo",
        "fun (p : Prod Nat Nat) => p.fst.foo",
    ] {
        match support::elab_and_synthesize(src) {
            Err(ElabError::InvalidField {
                reason: InvalidFieldReason::NotFound { full_name },
                ..
            }) => assert_eq!(full_name, "Nat.foo", "{src}"),
            other => panic!("{src}: expected InvalidField NotFound, got {other:?}"),
        }
    }
    // Review Focus 3: `c ++ suffix` (App.lean:1584-1586, :1606-1608) fires
    // only for a CONSTANT base, and `suffix?` is ALL the split-off fields
    // (`toName fields`, :1946-1950). `Nat : Type` takes the catch-all arm,
    // `Nat.succ : Nat → Nat` and `Nat.rec` the function arm. `Nat.rec.foo`
    // also shows the recursor guard stays off when fields follow (the
    // head `elabAppArgs` sees is not `Nat.rec`). "Unknown constant `…`"
    for (src, name) in [
        ("Nat.foo", "Nat.foo"),
        ("Nat.foo.bar", "Nat.foo.bar"),
        ("Nat.succ.foo", "Nat.succ.foo"),
        ("Nat.rec.foo", "Nat.rec.foo"),
    ] {
        match support::elab_and_synthesize(src) {
            Err(ElabError::UnknownIdent(s)) => assert_eq!(s, name, "{src}"),
            other => panic!("{src}: expected UnknownIdent({name}), got {other:?}"),
        }
    }
    // Review Focus 3: an fvar base never takes the suffix arm; the second
    // field carries no suffix. "… does not contain `Function.foo`",
    // "… does not contain `Function.succ` … from an expression @S1.imp s"
    for (src, full) in [
        ("fun (f : Nat -> Nat) => f.foo", "Function.foo"),
        ("fun (s : S1) => s.imp.succ", "Function.succ"),
    ] {
        assert_eq!(
            field_reason(src),
            InvalidFieldReason::NotFound { full_name: full.to_string() },
            "{src}"
        );
    }
    // Review Focus 2: `processLocal` (TermElabM.lean:2172-2179). "invalid
    // use of explicit universe parameters, `x` is a local variable"
    assert!(matches!(
        support::elab_and_synthesize("fun (x : Nat) => x.{0}"),
        Err(ElabError::InvalidExplicitUniversesForLocal(_))
    ));
    // Review Focus 2: levels go to the last field (`mkConsts`,
    // TermElabM.lean:2148). "too many explicit universe levels for
    // `Nat.succ`" / "… for `polyZero`" / "… for `Poly.val`"
    for src in [
        "Nat.zero.succ.{0}",
        "polyZero.{0}",
        "fun (x : Poly Nat) => x.val.{0,0}",
    ] {
        assert!(
            matches!(
                support::elab_and_synthesize(src),
                Err(ElabError::TooManyUniverseLevels(_))
            ),
            "{src}"
        );
    }
}
```

Run: `cargo test -p leanr_elab --test lval_smoke identifier_field_split 2>&1 | tail -20`
Expected: FAIL to compile (`InvalidExplicitUniversesForLocal` does not exist).

- [ ] **Step 4: Add the error variant**

In `crates/leanr_elab/src/error.rs`, after `PlaceholderAsFunction`:

```rust
    /// oracle: `throwInvalidExplicitUniversesForLocal`
    /// (`TermElabM.lean:2160-2161`), from `resolveName`'s `processLocal`
    /// (`:2172-2179`): explicit universes on an identifier that resolves
    /// to a local with no fields left over, e.g. `x.{0}`. With fields
    /// (`x.val.{0}`) the levels belong to the last field instead.
    InvalidExplicitUniversesForLocal(ExprId),
```

- [ ] **Step 5: Rewrite `resolve.rs`**

Replace the module doc's first paragraph (up to "…`.foo` dot-identifier resolution.") with:

```rust
//! Reduced name resolution. Oracle: `resolveName`
//! (`Lean/Elab/Term/TermElabM.lean:2170-2192`) over `resolveLocalName`
//! (`Lean/ResolveName.lean:460-622`) and `ResolveName.resolveGlobalName`
//! (`:194-217`), which split a dotted identifier into a head and trailing
//! field components.
//!
//! **Scope.** Global resolution is exact-name, with `currNamespace :=
//! .anonymous` and no `open`: the `open` / alias / `export` / `_root_`
//! slice owns `resolveUsingNamespace`, `resolveOpenDecls`, aliases and
//! `resolveExact`'s `_root_` stripping. Reserved names
//! (`realizeGlobalName`, e.g. `f.eq_1`) are not realized. The local side
//! has no auxiliary declarations (`let rec` / `where` has no producer), so
//! `matchAuxRecDecl?` and the `globalDeclFound` / `skipAuxDecl`
//! workaround, which only ever skips aux decls, have nothing to act on.
```

Keep the paragraph about the `AmbiguousIdent` branch. Replace `resolve_global` with:

```rust
/// oracle: `resolveLocalName` (`ResolveName.lean:460-622`), reduced (see
/// the module doc). Its `loop` (`:595-621`) tries the whole name first and
/// then ever shorter prefixes; the first prefix that is a local's user
/// name wins, and the components it dropped become fields. `prefixes[k]`
/// names the first `k + 1` components. Returns the local and the number
/// of field components.
///
/// The order is the oracle's but is not observable yet: leanr interns a
/// binder's name as ONE component (`builtin/binder/mod.rs`'s
/// `intern_binder_name`), so only `prefixes[0]` can ever match.
pub fn resolve_local_name(mctx: &MetaCtx, prefixes: &[NameId]) -> Option<(ExprId, usize)> {
    let n = prefixes.len();
    prefixes
        .iter()
        .enumerate()
        .rev()
        .find_map(|(k, &p)| mctx.lctx_lookup_by_name(p).map(|fvar| (fvar, n - 1 - k)))
}

/// oracle: `ResolveName.resolveGlobalName` (`ResolveName.lean:194-217`)
/// with `ns := .anonymous` and no `open`s. Its `loop` strips trailing
/// components until what is left names a declared constant, so the
/// LONGEST declared prefix wins and the stripped components become
/// fields: `Nat.zero.succ` is `Nat.zero` plus the field `succ`, not
/// `Nat` plus `zero.succ`.
///
/// `display` is the identifier's raw source text, used verbatim in
/// either error. A prefix is often a SCRATCH-region `NameId`
/// (`app::head::intern_prefixes` mints one for any name not already
/// interned in the persistent store), which `view.store` alone cannot
/// render; see `app::head::unknown_ident_via_real_scratch_pipeline`.
pub fn resolve_global_name(
    view: &EnvView,
    prefixes: &[NameId],
    display: &str,
) -> Result<(NameId, usize), ElabError> {
    let n = prefixes.len();
    for (k, &p) in prefixes.iter().enumerate().rev() {
        // One namespace (the root) and no `open`s: at most one candidate
        // per prefix. The `AmbiguousIdent` arm is kept for the `open`
        // slice, whose candidates can number more than one.
        let candidates: Vec<NameId> = view.get(p).is_some().then_some(p).into_iter().collect();
        match candidates.len() {
            0 => continue,
            1 => return Ok((candidates[0], n - 1 - k)),
            _ => return Err(ElabError::AmbiguousIdent(display.to_string())),
        }
    }
    Err(ElabError::UnknownIdent(display.to_string()))
}
```

Imports: `use leanr_kernel::bank::{ExprId, NameId};` and `use leanr_meta::MetaCtx;`.

Rewrite the unit tests. Add two helpers to the test module:

```rust
    fn child(env: &mut Environment, parent: NameId, s: &str) -> NameId {
        let store = env.store_mut();
        let sid = store.intern_str(None, s).unwrap();
        store.name_str(None, Some(parent), sid).unwrap()
    }

    fn admit_axiom(env: &mut Environment, name: NameId) {
        let prop = {
            let store = env.store_mut();
            let zero = store.level_zero(None).unwrap();
            store.expr_sort(None, zero).unwrap()
        };
        env.admit_unchecked(ConstantInfo::Axiom(AxiomVal {
            val: ConstantVal { name, level_params: vec![], ty: prop },
            is_unsafe: false,
        }))
        .unwrap();
    }
```

Rewrite `env_with_foo` to use `admit_axiom`. Update the two existing tests to call `resolve_global_name(&view, &[foo], "Foo")` (expect `(foo, 0)`) and `resolve_global_name(&view, &[nope], "Nope")` (expect `UnknownIdent("Nope")`). Add:

```rust
    /// `resolveGlobalName`'s `loop` (ResolveName.lean:197-216): the longest
    /// declared prefix wins; the rest are fields.
    #[test]
    fn longest_declared_prefix_wins_and_the_rest_are_fields() {
        let (mut env, foo) = env_with_foo();
        let foo_bar = child(&mut env, foo, "bar");
        let foo_bar_baz = child(&mut env, foo_bar, "baz");
        let prefixes = [foo, foo_bar, foo_bar_baz];
        {
            let view = env.view();
            assert_eq!(
                resolve_global_name(&view, &prefixes, "Foo.bar.baz").unwrap(),
                (foo, 2)
            );
        }
        admit_axiom(&mut env, foo_bar);
        let view = env.view();
        assert_eq!(
            resolve_global_name(&view, &prefixes, "Foo.bar.baz").unwrap(),
            (foo_bar, 1)
        );
    }
```

- [ ] **Step 6: `intern_prefixes`, `field_lvals` and the `suffix` field**

In `crates/leanr_elab/src/app/head.rs`, replace `intern_components`'s body so it delegates:

```rust
/// Intern every prefix of a dotted name: `prefixes[k]` is the name of
/// `parts[..=k]`. Same store discipline as `intern_components` (below),
/// which is the last element. `resolve::resolve_local_name` /
/// `resolve_global_name` need every prefix, and chaining `name_str`
/// mints them all anyway.
pub(crate) fn intern_prefixes(
    elab: &mut TermElabM,
    parts: &[&str],
) -> Result<Vec<NameId>, ElabError> {
    let base = elab.view.store;
    let mut prefixes = Vec::with_capacity(parts.len());
    let mut id: Option<NameId> = None;
    for part in parts {
        let store = elab.mctx.store_mut();
        let s = store
            .intern_str(Some(base), part)
            .map_err(leanr_meta::MetaError::from)?;
        let n = store
            .name_str(Some(base), id, s)
            .map_err(leanr_meta::MetaError::from)?;
        prefixes.push(n);
        id = Some(n);
    }
    Ok(prefixes)
}

pub(crate) fn intern_components(elab: &mut TermElabM, parts: &[&str]) -> Result<NameId, ElabError> {
    intern_prefixes(elab, parts)?
        .last()
        .copied()
        .ok_or_else(|| ElabError::IllFormedSyntax("empty name".to_string()))
}
```

Keep `intern_components`' existing doc comment.

In `crates/leanr_elab/src/app/lval.rs`, give `LVal::FieldName` the field and replace the enum doc's "The `suffix?`/`fullRef` fields … added there." sentence:

```rust
    FieldName {
        r#ref: SynElem,
        name: String,
        levels: Vec<LevelId>,
        /// oracle: `suffix?` — `some` only on the FIRST field split off an
        /// identifier (`elabAppFnResolutions`, `App.lean:1936`), holding
        /// ALL the split-off fields rejoined (`toName fields`, `:1946-1950`).
        /// Read only by the `c ++ suffix` unknown-constant arms of
        /// `resolve_lval_aux`. `fullRef` (the error position) is not ported.
        suffix: Option<String>,
    },
```

Move the proj arm's `_ =>` branch (the `elabFieldName` one, `head.rs:109-129`), together with the `fieldIdx` branch, into:

```rust
/// oracle: `elabFieldIdx` / `elabFieldName` (`App.lean:2067-2078`): the
/// LVals a `.field` suffix contributes. Shared by `Term.proj` and
/// `Term.pipeProj`. `levels` go to the LAST component; `suffix? := none`,
/// since a projection's field "can't be part of a composite name" (`:2072`).
fn field_lvals(
    field: &SynElem,
    kinds: &KindInterner,
    levels: &[LevelId],
) -> Result<Vec<LVal>, ElabError> {
    Ok(match kinds.name(field.kind()) {
        "fieldIdx" => {
            let text = field.to_string();
            let idx = text
                .trim()
                .parse::<usize>()
                .map_err(|_| ElabError::IllFormedSyntax(format!("fieldIdx `{text}`")))?;
            vec![LVal::FieldIdx {
                r#ref: field.clone(),
                idx,
                levels: levels.to_vec(),
            }]
        }
        _ => {
            let text = field.to_string();
            let comps = ident_components(text.trim())?;
            let last = comps.len() - 1;
            comps
                .into_iter()
                .enumerate()
                .map(|(i, c)| LVal::FieldName {
                    r#ref: field.clone(),
                    name: c,
                    levels: if i == last { levels.to_vec() } else { Vec::new() },
                    suffix: None,
                })
                .collect()
        }
    })
}
```

The proj arm becomes:

```rust
        ("Lean.Parser.Term.proj", _) => {
            let (base, field) = proj_parts(elem)?;
            let mut new = field_lvals(&field, kinds, explicit_levels)?;
            new.extend(lvals);
            elab_app_fn(elab, &base, kinds, &[], new, call)
        }
```

Keep the oracle-citation comments that sat on the moved branches, on `field_lvals`' arms.

- [ ] **Step 7: `elab_app_fn_id`**

Replace the ident arm:

```rust
        ("<ident>", leanr_syntax::tree::NodeOrToken::Token(tok)) => Ok(vec![elab_app_fn_id(
            elab,
            elem,
            tok.text(),
            explicit_levels,
            lvals,
            call,
            kinds,
        )?]),
```

Replace `elab_ident_head` with the function below. Move its long comments over, unchanged except for the `heed` change: the `elabAsElim` guard comment, the M4b-2 local-first comment, and the doc paragraphs on `mkConst` / `explicit_levels`.

```rust
/// oracle: `elabAppFnId` (`App.lean:1952-1958`): `resolveName'`
/// (`TermElabM.lean:2201-2208`) over `resolveName` (`:2170-2192`), then
/// `elabAppFnResolutions` (`App.lean:1926-1950`), which turns the
/// split-off field components into `LVal`s in front of the pending ones.
fn elab_app_fn_id(
    elab: &mut TermElabM,
    elem: &SynElem,
    raw: &str,
    explicit_levels: &[LevelId],
    lvals: Vec<LVal>,
    call: AppCall,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    // `intern_dotted`'s convention (split on every `.`, `«»` kept), so a
    // single-component prefix is the same `NameId` a binder of that text
    // has (plan § Decisions).
    let parts: Vec<&str> = raw.split('.').collect();
    let prefixes = intern_prefixes(elab, &parts)?;
    // `resolveName`: every local prefix before any global (`:2180-2181`).
    let (f, n_fields, proj_levels) =
        if let Some((fvar, n_fields)) = resolve_local_name(&elab.mctx, &prefixes) {
            // `processLocal` (`:2172-2179`).
            if n_fields == 0 && !explicit_levels.is_empty() {
                return Err(ElabError::InvalidExplicitUniversesForLocal(fvar));
            }
            (fvar, n_fields, explicit_levels.to_vec())
        } else {
            let (cname, n_fields) = resolve_global_name(&elab.view, &prefixes, raw)?;
            // `mkConsts` (`:2145-2158`): with fields, the explicit levels
            // belong to the last field and the constant gets fresh ones.
            let (const_levels, proj_levels): (&[LevelId], &[LevelId]) = if n_fields == 0 {
                (explicit_levels, &[])
            } else {
                (&[], explicit_levels)
            };
            // `elabAsElim?` runs on the FINAL head (`App.lean:1373`). With
            // LVals pending, or fields split off, the constant is not that
            // head, so the recursor guard must not fire.
            let heed = !call.explicit && !call.ellipsis && lvals.is_empty() && n_fields == 0;
            let info = elab
                .view
                .get(cname)
                .expect("resolve_global_name only returns names EnvView::get resolves");
            if heed && matches!(info, leanr_kernel::ConstantInfo::Rec(_)) {
                return Err(ElabError::UnsupportedSyntax(format!(
                    "`{raw}` is a recursor — the oracle elaborates eliminator-headed \
                     applications with `ElabElim.main` (`shouldElabAsElim`, App.lean:1322-1328; \
                     diverted at :1373), which needs `motivePos` — M4b-4c"
                )));
            }
            let display = parts[..parts.len() - n_fields].join(".");
            (
                mk_const(elab, cname, const_levels, &display)?,
                n_fields,
                proj_levels.to_vec(),
            )
        };
    // `elabAppFnResolutions` (`:1933-1938`).
    let fields = &parts[parts.len() - n_fields..];
    let suffix = (!fields.is_empty()).then(|| fields.join("."));
    let mut all: Vec<LVal> = fields
        .iter()
        .enumerate()
        .map(|(i, c)| LVal::FieldName {
            r#ref: elem.clone(),
            name: (*c).to_string(),
            levels: if i + 1 == n_fields { proj_levels.clone() } else { Vec::new() },
            suffix: if i == 0 { suffix.clone() } else { None },
        })
        .collect();
    all.extend(lvals);
    crate::app::lval::elab_app_lvals(elab, f, all, call, kinds)
}
```

Replace `use crate::resolve::resolve_global;` with `use crate::resolve::{resolve_global_name, resolve_local_name};`.

Update the unit test `unknown_ident_via_real_scratch_pipeline`, and in its doc replace the `elab_ident_head` / `resolve_global` names with `elab_app_fn_id` / `resolve_global_name`. It now goes through `elab_app_fn`:

```rust
        let elem = parsed.tree.root().first_child_or_token().expect("a term");
        assert!(matches!(elem, NodeOrToken::Token(_)), "expected a bare ident token");
        let call = crate::app::AppCall {
            named_args: Vec::new(),
            args: Vec::new(),
            expected: None,
            explicit: false,
            ellipsis: false,
            stx: elem.clone(),
        };
        match super::elab_app_fn(&mut elab, &elem, &parsed.tree.kinds, &[], Vec::new(), call) {
            Err(crate::ElabError::UnknownIdent(s)) => assert_eq!(s, "Bar"),
            other => panic!("expected UnknownIdent(\"Bar\"), got {other:?}"),
        }
```

- [ ] **Step 8: The `c ++ suffix` arms**

In `lval.rs`'s `resolve_lval_aux`, bind `suffix` in the Forall/`FieldName` arm's pattern. Replace its trailing comment and `Err(...)`:

```rust
            // `:1584-1586`: a field split off an identifier whose base is a
            // constant names the constant `c ++ suffix`.
            if let (Node::Const { name: Some(c), .. }, Some(suffix)) = (node(elab, app_fn(elab, e)), suffix) {
                return Err(ElabError::UnknownIdent(format!("{}.{suffix}", render(elab, c))));
            }
            // `:1588`.
            Err(field_err(name, InvalidFieldReason::NotFound { full_name: full }))
```

Replace the catch-all `FieldName` arm:

```rust
        // `:1605-1612`: `c ++ suffix` (`:1607-1608`) first, as above.
        (_, LVal::FieldName { name, suffix, .. }) => {
            if let (Node::Const { name: Some(c), .. }, Some(suffix)) = (node(elab, app_fn(elab, e)), suffix) {
                return Err(ElabError::UnknownIdent(format!("{}.{suffix}", render(elab, c))));
            }
            Err(field_err(name, InvalidFieldReason::NotConstApp))
        }
```

Both are ordinary oracle errors, so `resolve_lval_loop` still retries them through `unfold_definition` (`App.lean:1688-1694`), as the oracle does.

- [ ] **Step 9: `local_ident_of` through `resolve_local_name`**

In `crates/leanr_elab/src/elab.rs`, `isLocalIdent?` is "`resolveLocalName` returns `some (fvar, [])`" (`TermElabM.lean:1723-1730`). Replace the lookup:

```rust
    let parts: Vec<&str> = tok.text().split('.').collect();
    let prefixes = crate::app::head::intern_prefixes(elab, &parts)?;
    Ok(match crate::resolve::resolve_local_name(&elab.mctx, &prefixes) {
        Some((fvar, 0)) => Some(fvar),
        _ => None,
    })
```

In its doc comment, replace "this crate has no field-projection resolution to produce a leftover suffix, so 'found in the local context under this exact name' is the whole test" with "`resolve::resolve_local_name` is `resolveLocalName`, leftover fields and all; a result with fields is not a local identifier".

This preserves behaviour: with single-component binder names, the old exact lookup and the new "no leftover fields" test accept the same identifiers. The existing implicit-lambda postponement tests (`seam_audit.rs`'s `implicit_lambda_postpone_is_no_longer_a_seam`, P2's `p2/*` records) cover it, so it needs no new test and no mutation.

- [ ] **Step 10: Run**

Run: `cargo test -p leanr_elab 2>&1 | tail -40`
Expected: PASS, with 249 records. `resolve.rs`'s unit tests pass too.

- [ ] **Step 11: Show the tests discriminate**

Apply each mutation, run the Step 10 command, confirm red, then revert:
- **A:** in `resolve_global_name`, iterate prefixes forward (shortest first; drop `.rev()`). `p4/global-field` must go red (it becomes `Nat` plus `zero.succ`, then `UnknownIdent`), and so must the unit test.
- **B:** in `elab_app_fn_id`, try `resolve_global_name` before `resolve_local_name`. `p4/local-shadows-global` must go red.
- **C:** give the constant the explicit levels even with fields (`(explicit_levels, explicit_levels)`). `p4/global-univ-last` must go red with `TooManyUniverseLevels`.
- **D:** delete the `InvalidExplicitUniversesForLocal` check. The `x.{0}` assertion must go red.
- **E:** put `suffix` on every field (`suffix: suffix.clone()`). The `s.imp.succ` assertion must go red with `UnknownIdent`.
- **F:** make `suffix` the first field only (`fields.first().map(|s| s.to_string())`). The `Nat.foo.bar` assertion must go red.
- **G:** delete the catch-all arm's suffix check. The `Nat.foo` and `Nat.foo.bar` assertions must go red with `InvalidField NotConstApp`.
- **H:** delete the Forall arm's suffix check. The `Nat.succ.foo` assertion must go red.
- **I:** drop `&& n_fields == 0` from `heed`. The `Nat.rec.foo` assertion must go red with the M4b-4c seam.

Record all nine outputs.

- [ ] **Step 12: Commit**

```bash
git add tests/fixtures/elab crates/leanr_elab
git commit -m "M4b-4a P4: the field split in identifiers (resolveName)"
```

---

### Task 2: `pipeProj` and `namedPattern`

**Files:**
- Modify: `crates/leanr_elab/src/app/mod.rs` (`elab_pipe_proj` after `elab_atom`)
- Modify: `crates/leanr_elab/src/app/head.rs` (two arms, `pipe_proj_parts`, `is_lval_head`)
- Modify: `crates/leanr_elab/src/dispatch.rs` (`elaborator_name_for`, `dispatch`)
- Modify: `crates/leanr_elab/src/error.rs` (one variant)
- Modify: `crates/leanr_elab/tests/lval_smoke.rs`, `crates/leanr_elab/tests/seam_audit.rs` (`unregistered_kinds_are_named_by_kind`, `:286-322`)
- Modify: `tests/fixtures/elab/dump_elab.lean`, `elab-queries.jsonl`, `crates/leanr_elab/tests/oracle_elab.rs`

**Interfaces:**
- Consumes (Task 1): `field_lvals`.
- Produces:
  - `pub fn elab_pipe_proj(elab: &mut TermElabM, node: &SyntaxNode, kinds: &KindInterner, expected: Option<ExprId>) -> Result<ExprId, ElabError>`;
  - `ElabError::NamedPatternOutsidePattern { as_function: bool }`.

- [ ] **Step 1: Write the failing corpus records**

Append to `p4Queries`, before its closing `]`:

```lean
  , ("p4/pipe-idx",             "fun (p : Prod Nat Nat) => p |>.2")
  , ("p4/pipe-idx-univ",        "fun (p : Prod Nat Nat) => p |>.1.{0}")
  , ("p4/pipe-args",            "fun (s : S1) => s |>.addTo Nat.zero")
  , ("p4/pipe-named",           "fun (s : S1) => s |>.addTo (n := Nat.zero)")
  , ("p4/pipe-eta",             "fun (s : S1) => s |>.addTo")
  , ("p4/pipe-global",          "Nat.zero |>.succ")
  , ("p4/pipe-univ",            "fun (x : Poly Nat) => x |>.val.{0}")
  , ("p4/pipe-chain",           "fun (p : Prod Nat Nat) => p |>.1 |>.succ")
  , ("p4/pipe-fields",          "fun (p : Prod Nat Nat) => p |>.fst.succ")
  , ("p4/pipe-postponed",       "(fun x => x |>.1) (Prod.mk Nat.zero Nat.zero)")
```

Regenerate as in Task 1 Step 2. Expected: `259` lines, no stderr errors, and the `^-[^-]` grep prints nothing. Raise the floor to 259 with `// 249 -> 259 (M4b-4a P4 task 2): the 10 p4/pipe-* records.`

Run: `cargo test -p leanr_elab --test oracle_elab 2>&1 | tail -20`
Expected: FAIL. The `p4/pipe-*` records report `UnsupportedSyntax("Lean.Parser.Term.pipeProj")`.

- [ ] **Step 2: Write the failing rejection tests and flip the seam test**

Append to `lval_smoke.rs`:

```rust
/// M4b-4a P4: `e |>.f args` (`elabPipeProj`, App.lean:2250-2258, into
/// `elabAppFn`'s pipeProj arms, :2085-2097) and named patterns outside a
/// pattern.
#[test]
fn pipe_projection_and_named_pattern_rejections_match_the_oracle() {
    // "Invalid projection: Index `3` is invalid for this structure; it
    // must be between 1 and 2"
    assert_eq!(
        proj_reason("fun (p : Prod Nat Nat) => p |>.3"),
        InvalidProjectionReason::IndexOutOfRange { idx: 3, num_fields: 2 }
    );
    // Postponed, then resumed with postponement off. "Invalid
    // projection: Type of x is not known; cannot resolve projection `1`"
    assert_eq!(
        proj_reason("fun x => x |>.1"),
        InvalidProjectionReason::TypeUnknown
    );
    // The `.{us}` of `$e |>.$f.{us}` (`:2094-2097`) reaches `Nat.succ`.
    // "too many explicit universe levels for `Nat.succ`"
    assert!(matches!(
        support::elab_and_synthesize("fun (x : Nat) => x |>.succ.{0}"),
        Err(ElabError::TooManyUniverseLevels(_))
    ));
    // A whole term: `elabNamedPatternErr` (BuiltinTerm.lean:443-444).
    // "`<identifier>@<term>` is a named pattern and can only be used in
    // pattern matching contexts"
    assert!(matches!(
        support::elab_and_synthesize("fun (x : Nat) => x@Nat.zero"),
        Err(ElabError::NamedPatternOutsidePattern { as_function: false })
    ));
    // An application head: `elabAppFn` (App.lean:2098-2100). "Expected a
    // function, but found the named pattern x@Nat.succ"
    assert!(matches!(
        support::elab_and_synthesize("fun (x : Nat) => x@Nat.succ Nat.zero"),
        Err(ElabError::NamedPatternOutsidePattern { as_function: true })
    ));
}
```

In `seam_audit.rs`'s `unregistered_kinds_are_named_by_kind`, both cases are now registered. Replace the `cases` list with one kind that is still unrouted:

```rust
        // M4b-4b: the anonymous constructor is parsed (`leanr_syntax`
        // `term.rs`) and deliberately unrouted. (`Term.pipeProj`,
        // `Term.dotIdent` and `Term.namedPattern` are registered since
        // M4b-4a P4, `Term.proj` since P1 task 5.)
        ("⟨Nat.zero, Nat.zero⟩", "Lean.Parser.Term.anonymousCtor"),
```

Then rewrite the doc comment's last sentences: "… `Term.anonymousCtor` has no elaborator yet: M4b-4b owns it. (`Term.proj`, `Term.pipeProj`, `Term.dotIdent` and `Term.namedPattern` were routed by M4b-4a P1 and P4, with their arms.)"

Run: `cargo test -p leanr_elab --test lval_smoke --test seam_audit 2>&1 | tail -20`
Expected: FAIL to compile (`NamedPatternOutsidePattern` does not exist).

- [ ] **Step 3: Add the error variant**

In `error.rs`, after `InvalidExplicitUniversesForLocal`:

```rust
    /// A named pattern `x@p` outside a pattern. Two oracle throw sites,
    /// both measured: `elabNamedPatternErr` (`BuiltinTerm.lean:443-444`)
    /// answers for a whole term (`as_function: false`), and `elabAppFn`'s
    /// arm (`App.lean:2098-2100`) for an application head
    /// (`as_function: true`).
    NamedPatternOutsidePattern { as_function: bool },
```

- [ ] **Step 4: Route `pipeProj` and `namedPattern`**

In `app/mod.rs`, after `elab_atom`:

```rust
/// oracle: `elabPipeProj` (`App.lean:2250-2258`). `$e |>.$f$[.{us}]? args*`
/// is `elabAppAux` on `$e |>.$f$[.{us}]?` with the trailing arguments
/// expanded (`expandArgs`); `head::elab_app_fn`'s pipeProj arm then reads
/// only `e`, `f` and the levels. `universeConstraintsCheckpoint` is not
/// per-call, as for `elab_app`.
pub fn elab_pipe_proj(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let ch = non_trivia_children(node);
    let args_node = ch
        .get(4)
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::IllFormedSyntax("pipeProj: no argument list".to_string()))?;
    let items = non_trivia_children(args_node);
    let (named_args, args, ellipsis) = expand::expand_args(&items, kinds)?;
    let elem = SynElem::Node(node.clone());
    elab_app_aux(elab, &elem, kinds, named_args, args, ellipsis, expected, elem.clone())
}
```

In `head.rs`, next to `proj_parts`:

```rust
/// `Term.pipeProj`'s children (`term_app.rs`'s `register_pipe_proj`;
/// confirmed with `leanr parse --dump` while planning):
///
/// ```text
///   [0] e   [1] "|>."   [2] field: fieldIdx node | <ident> token
///   [3] null: `optional explicitUnivSuffix`, empty or [".{", levels, "}"]
///   [4] null: `many argument` (`app::elab_pipe_proj` takes it apart)
/// ```
///
/// Returns `e`, the field and the level syntax (separators dropped, as
/// `app::explicit_univ_parts` does).
fn pipe_proj_parts(elem: &SynElem) -> Result<(SynElem, SynElem, Vec<SynElem>), ElabError> {
    let bad = |what: &str| ElabError::IllFormedSyntax(format!("pipeProj: {what}"));
    let node = elem.as_node().ok_or_else(|| bad("not a node"))?;
    let ch = non_trivia_children(node);
    if ch.len() != 5 {
        return Err(bad("expected `[e, \"|>.\", field, univs, args]`"));
    }
    let suffix = ch[3].as_node().ok_or_else(|| bad("univ suffix is not a node"))?;
    let sch = non_trivia_children(suffix);
    let lvls = match sch.get(1).and_then(|el| el.as_node()) {
        Some(list) => non_trivia_children(list).into_iter().step_by(2).collect(),
        None if sch.is_empty() => Vec::new(),
        None => return Err(bad("malformed `.{..}` suffix")),
    };
    Ok((ch[0].clone(), ch[2].clone(), lvls))
}
```

Add two arms to `elab_app_fn`, after the proj arm:

```rust
        // oracle: `` `($e |>.$idx:fieldIdx) `` / `` `($e |>.$field:ident) ``
        // and their `.{us}` forms (`App.lean:2085-2097`), the same
        // `elabFieldIdx` / `elabFieldName` as a projection. The trailing
        // arguments were taken off by `app::elab_pipe_proj`.
        ("Lean.Parser.Term.pipeProj", _) => {
            let (base, field, lvls) = pipe_proj_parts(elem)?;
            let levels = elab_explicit_univs(elab, &lvls, kinds)?;
            let mut new = field_lvals(&field, kinds, &levels)?;
            new.extend(lvals);
            elab_app_fn(elab, &base, kinds, &[], new, call)
        }
        // oracle: `` `($_:ident@$_:term) `` (`App.lean:2098-2100`).
        ("Lean.Parser.Term.namedPattern", _) => {
            Err(ElabError::NamedPatternOutsidePattern { as_function: true })
        }
```

Narrow `is_lval_head` to `"Lean.Parser.Term.dotIdent"` only, and update its doc and the seam message to name only `dotIdent` (`App.lean:2106-2109`), still "— M4b-4a P4" until Task 3.

In `dispatch.rs`, add `"Lean.Parser.Term.pipeProj" => Some("pipeProj")` and `"Lean.Parser.Term.namedPattern" => Some("namedPattern")` to `elaborator_name_for`. Add to `dispatch`, after the proj arm:

```rust
        // oracle: `@[builtin_term_elab pipeProj] elabPipeProj`
        // (`App.lean:2250-2258`).
        ("Lean.Parser.Term.pipeProj", NodeOrToken::Node(node)) => {
            crate::app::elab_pipe_proj(elab, node, kinds, expected)
        }
        // oracle: `elabNamedPatternErr` (`BuiltinTerm.lean:443-444`).
        // `elabNamedPattern := elabAtom` (`App.lean:2247`) is registered
        // too; measured, the error below is the one a whole term gets.
        ("Lean.Parser.Term.namedPattern", NodeOrToken::Node(_)) => {
            Err(ElabError::NamedPatternOutsidePattern { as_function: false })
        }
```

- [ ] **Step 5: Run**

Run: `cargo test -p leanr_elab 2>&1 | tail -40`
Expected: PASS, with 259 records.

- [ ] **Step 6: Show the tests discriminate**

Apply, run the Step 5 command, confirm red, revert:
- **J:** in `elab_pipe_proj`, pass `Vec::new()` for `named_args` and `args`. `p4/pipe-args` and `p4/pipe-named` must go red.
- **K:** in the pipeProj arm, pass `&[]` instead of `&levels`. The `x |>.succ.{0}` assertion must go red. (`p4/pipe-univ` may not: the dropped level is a fresh mvar that unifies to `0`.)
- **L:** swap the two `as_function` values. Both named-pattern assertions must go red.
- **M:** make the pipeProj arm pass `lvals` BEFORE the field's (`let mut new = lvals; new.extend(field_lvals(..)?)`). `p4/pipe-chain` must go red.

- [ ] **Step 7: Commit**

```bash
git add tests/fixtures/elab crates/leanr_elab
git commit -m "M4b-4a P4: pipeProj and namedPattern"
```

---

### Task 3: `.c` dot identifiers (`resolveDottedIdentFn`) and `@.c`

**Files:**
- Create: `crates/leanr_elab/src/app/dot_ident.rs`
- Modify: `crates/leanr_elab/src/app/mod.rs` (`pub mod dot_ident;`; `ExplicitHead`, `explicit_head_shape`, `elab_explicit`, `peel_head`, `dot_ident_seam`)
- Modify: `crates/leanr_elab/src/app/head.rs` (dotIdent arm; delete `is_lval_head` and its seam arm)
- Modify: `crates/leanr_elab/src/app/lval.rs` (`node`, `app_fn`, `render` → `pub(super)`)
- Modify: `crates/leanr_elab/src/dispatch.rs`, `crates/leanr_elab/src/error.rs`, `crates/leanr_elab/src/lib.rs`
- Modify: `crates/leanr_elab/tests/lval_smoke.rs`, `crates/leanr_elab/tests/seam_audit.rs` (`deferred_constructs_are_named_seams`, `:156-209`)
- Modify: `tests/fixtures/elab/dump_elab.lean`, `elab-queries.jsonl`, `crates/leanr_elab/tests/oracle_elab.rs`

**Interfaces:**
- Consumes: `TermElabM::try_postpone_if_none_or_mvar` / `try_postpone_if_mvar` (`postpone.rs`), and `MetaCtx::{whnf_core, unfold_definition_pub, instantiate_mvars, instantiate1, push_local_decl, lctx_checkpoint, lctx_restore}`, all already `pub`. From head.rs it uses `mk_const`, `intern_components` and `ident_components`.
- Produces:
  - `pub(crate) fn resolve_dotted_ident_fn(elab: &mut TermElabM, raw: &str, explicit_levels: &[LevelId], expected: Option<ExprId>) -> Result<ExprId, ElabError>`;
  - `ElabError::InvalidDottedIdent { id: String, reason: InvalidDottedIdentReason }`;
  - `pub enum InvalidDottedIdentReason { NotAtomic, NoExpectedType, Sort, NotConstApp, UnknownConstant { full_name: String } }`, exported from `lib.rs`.

- [ ] **Step 1: Write the failing corpus records**

Append to `p4Queries`:

```lean
  , ("p4/dot-ascribed",         "(.zero : Nat)")
  , ("p4/dot-arg",              "Nat.succ .zero")
  , ("p4/dot-pi",               "Function.twice .succ Nat.zero")
  , ("p4/dot-pi-ascribed",      "(.succ : Nat -> Nat)")
  , ("p4/dot-unfold",           "(.zero : NatAlias)")
  , ("p4/dot-pi-unfold",        "(.succ : Nat -> NatAlias)")
  , ("p4/dot-optparam",         "withDefault .zero")
  , ("p4/dot-postponed",        "Eq .zero Nat.zero")
  , ("p4/dot-args",             "(.mk Nat.zero Nat.zero : Prod Nat Nat)")
  , ("p4/dot-explicit",         "(@.mk Nat Nat Nat.zero Nat.zero : Prod Nat Nat)")
  , ("p4/dot-univs",            "(.mk.{0,0} Nat.zero Nat.zero : Prod Nat Nat)")
  , ("p4/dot-univ-prefix",      "(.mk.{0} Nat.zero Nat.zero : Prod Nat Nat)")
  , ("p4/dot-partial",          "(.mk : Nat -> Nat -> Prod Nat Nat)")
  , ("p4/dot-nested",           "(.mk .zero .zero : Prod Nat Nat)")
```

Regenerate. Expected: `273` lines, no stderr errors, and the grep prints nothing. Raise the floor to 273 with `// 259 -> 273 (M4b-4a P4 task 3): the 14 p4/dot-* records.`

Run: `cargo test -p leanr_elab --test oracle_elab 2>&1 | tail -20`
Expected: FAIL. The `p4/dot-*` records report `UnsupportedSyntax("Lean.Parser.Term.dotIdent")` or the `M4b-4a P4` head seam.

- [ ] **Step 2: Write the failing rejection tests and flip the seam cases**

Append to `lval_smoke.rs` (and import `InvalidDottedIdentReason` beside the other reasons):

```rust
fn dotted_reason(src: &str) -> InvalidDottedIdentReason {
    match support::elab_and_synthesize(src) {
        Err(ElabError::InvalidDottedIdent { reason, .. }) => reason,
        other => panic!("{src}: expected InvalidDottedIdent, got {other:?}"),
    }
}

/// M4b-4a P4: `resolveDottedIdentFn` (App.lean:1985-2058). Each message is
/// the pinned oracle's (plan § Measured oracle behaviour).
#[test]
fn dot_identifier_rejections_match_the_oracle() {
    // `:1986-1987`: "The name `a.b` must be atomic"
    assert_eq!(dotted_reason("(.a.b : Nat)"), InvalidDottedIdentReason::NotAtomic);
    // Review Focus 5. `:1988-1990`: postponed, then resumed with no
    // expected type. `@.succ` is `elabAppFn`'s `@.$id` arm (:2115),
    // formerly a P4 seam. `(fun x => x) .zero` resumes against the
    // still-unassigned `?α` and throws at `:2044-2045`. "The expected type
    // of `.zero` could not be determined"
    for src in [".zero", "@.succ", ".succ Nat.zero", "(fun x => x) .zero"] {
        assert_eq!(
            dotted_reason(src),
            InvalidDottedIdentReason::NoExpectedType,
            "{src}"
        );
    }
    // `:2041-2042`: "Not supported on type universe"
    assert_eq!(dotted_reason("(.foo : Type)"), InvalidDottedIdentReason::Sort);
    // `:2046-2048`: "The expected type of `.foo` α is not of the form `C ...`"
    assert_eq!(
        dotted_reason("fun (α : Type) (f : α -> Nat) => f .foo"),
        InvalidDottedIdentReason::NotConstApp
    );
    // `:2038-2040`, with the `unfoldDefinition?` retry (`:2050-2057`)
    // throwing the LAST failure: the oracle logs "Unknown constant
    // `NatAlias.foo`", then throws "Unknown constant `Nat.foo`" (and
    // `S3Alias.zero` → `S3.zero`).
    for (src, full) in [
        ("Nat.succ .foo", "Nat.foo"),
        ("(.foo : NatAlias)", "Nat.foo"),
        ("(.zero : S3Alias)", "S3.zero"),
        ("(.zero : Prod Nat Nat)", "Prod.zero"),
    ] {
        assert_eq!(
            dotted_reason(src),
            InvalidDottedIdentReason::UnknownConstant { full_name: full.to_string() },
            "{src}"
        );
    }
    // `mkConst resolvedName explicitUnivs` (`:2033`): "too many explicit
    // universe levels for `Nat.zero`"
    assert!(matches!(
        support::elab_and_synthesize("(.zero.{0} : Nat)"),
        Err(ElabError::TooManyUniverseLevels(_))
    ));
}

/// Review Focus 4: `withForallBody` (App.lean:2009-2015) enters
/// `(y : Nat) → Nat` with a local `y` and must drop it afterwards; the
/// next argument's `y` is then unknown. Oracle: "Unknown identifier `y`".
#[test]
fn dot_identifier_telescope_does_not_leak_its_binders() {
    match support::elab_and_synthesize("(fun (g : (y : Nat) -> Nat) (n : Nat) => n) .succ y") {
        Err(ElabError::UnknownIdent(s)) => assert_eq!(s, "y"),
        other => panic!("expected UnknownIdent(y), got {other:?}"),
    }
}
```

In `seam_audit.rs`'s `deferred_constructs_are_named_seams`, delete the `("@.succ", "M4b-4a P4")` and `(".succ Nat.zero", "M4b-4a P4")` rows. Replace each row's comment with a one-line note that the case "is `InvalidDottedIdent { NoExpectedType }` since M4b-4a P4 (`lval_smoke.rs`)".

Run: `cargo test -p leanr_elab --test lval_smoke 2>&1 | tail -20`
Expected: FAIL to compile (`InvalidDottedIdentReason` does not exist).

- [ ] **Step 3: Add the error variant**

In `error.rs`, after `NamedPatternOutsidePattern`:

```rust
    /// oracle: `resolveDottedIdentFn`'s throws (`App.lean:1985-2058`);
    /// `id` is the identifier after the dot, as written. Prose deferred
    /// (design spec § Errors).
    InvalidDottedIdent {
        id: String,
        reason: InvalidDottedIdentReason,
    },
```

and, after `InvalidFieldReason`:

```rust
/// Which `resolveDottedIdentFn` throw an `ElabError::InvalidDottedIdent`
/// stands for.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InvalidDottedIdentReason {
    /// `App.lean:1986-1987` — "The name `id` must be atomic".
    NotAtomic,
    /// `throwNoExpectedType` (`App.lean:1997-2007`), thrown with no
    /// expected type (`:1989-1990`) or with an mvar-headed one (`:2044-2045`).
    NoExpectedType,
    /// `App.lean:2041-2042` — "Not supported on type universe".
    Sort,
    /// `App.lean:2046-2048` — "is not of the form `C ...` or `... → C ...`".
    NotConstApp,
    /// `App.lean:2038-2040` — `throwUnknownIdentifierAt` "Unknown constant
    /// `full_name`", the last one tried after every `unfoldDefinition?` step.
    UnknownConstant { full_name: String },
}
```

In `lib.rs`: `pub use error::{ElabError, InvalidDottedIdentReason, InvalidFieldReason, InvalidProjectionReason};`.

- [ ] **Step 4: Write `app/dot_ident.rs`**

In `lval.rs`, change `fn node`, `fn app_fn` and `fn render` to `pub(super) fn`. Add `pub mod dot_ident;` to `app/mod.rs`'s module list. Create:

```rust
//! M4b-4a P4: `.c` dot identifiers. Oracle: `resolveDottedIdentFn`
//! (`Lean/Elab/App.lean:1985-2058`, pinned v4.33.0-rc1). Design:
//! docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md § P4.
//!
//! Not ported:
//! - the local-context candidate (`:2034-2037`), since `C ++ id` is never
//!   atomic and only a `let rec` / `where` aux declaration could match
//!   (plan § Spec deviations 1);
//! - the logged earlier failures (`:2056`), because leanr has no message
//!   log (spec § Seams after P4);
//! - `addCompletionInfo` and the `reverseFieldLookup` hint, which are
//!   UI only.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId, NameId};
use leanr_meta::MetaError;

use crate::app::head::{ident_components, intern_components, mk_const};
use crate::app::lval::{app_fn, node, render};
use crate::elab::TermElabM;
use crate::error::{ElabError, InvalidDottedIdentReason};

fn dotted_err(id: &str, reason: InvalidDottedIdentReason) -> ElabError {
    ElabError::InvalidDottedIdent {
        id: id.to_string(),
        reason,
    }
}

/// oracle: `resolveDottedIdentFn` (`App.lean:1985-2058`). Returns the one
/// resolution: candidate resolution is exact-name (spec § Seams after
/// P4), so there is never more than one.
pub(crate) fn resolve_dotted_ident_fn(
    elab: &mut TermElabM,
    raw: &str,
    explicit_levels: &[LevelId],
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    // `id.getId.eraseMacroScopes` (`App.lean:2080`), escape-aware: `.«a.b»`
    // is atomic. This name is only ever appended to a constant's
    // namespace, never matched against a binder, so the escape convention
    // of plan § Decisions does not apply.
    let comps = ident_components(raw)?;
    // `:1986-1987`.
    if comps.len() != 1 {
        return Err(dotted_err(raw, InvalidDottedIdentReason::NotAtomic));
    }
    let id = comps[0].as_str();
    // `:1988`.
    elab.try_postpone_if_none_or_mvar(expected)?;
    // `:1989-1990`.
    let Some(expected) = expected else {
        return Err(dotted_err(id, InvalidDottedIdentReason::NoExpectedType));
    };
    // `:1994-1995`.
    with_forall_body(elab, expected, |elab, result_type| {
        go(elab, id, explicit_levels, result_type, expected)
    })
}

/// `withForallBody` (`App.lean:2009-2015`): `whnfCoreUnfoldingAnnotations`,
/// then, while the result is a pi, enter every syntactic binder
/// (`forallTelescope`, non-reducing) and repeat on the body. The
/// telescope's locals are dropped on EVERY exit path (Review Focus 4). A
/// resolution is a closed constant, so it never refers to them.
fn with_forall_body<R>(
    elab: &mut TermElabM,
    ty: ExprId,
    k: impl FnOnce(&mut TermElabM, ExprId) -> Result<R, ElabError>,
) -> Result<R, ElabError> {
    let checkpoint = elab.mctx.lctx_checkpoint();
    let result = (|| {
        let mut cur = whnf_core_unfolding_annotations(elab, ty)?;
        while matches!(node(elab, cur), Node::Forall { .. }) {
            while let Node::Forall {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = node(elab, cur)
            {
                let fvar = elab.mctx.push_local_decl(binder_name, binder_type, binder_info)?;
                cur = elab.mctx.instantiate1(body, fvar)?;
            }
            cur = whnf_core_unfolding_annotations(elab, cur)?;
        }
        k(elab, cur)
    })();
    elab.mctx.lctx_restore(checkpoint);
    result
}

/// oracle: `whnfCoreUnfoldingAnnotations` (`Meta/WHNF.lean:980-981`) —
/// `whnfHeadPred` (`:962-970`) with `isTypeAnnotation` (`Expr.lean:1725-1729`):
/// `whnfCore`, and while the head is `outParam` / `semiOutParam` /
/// `optParam` / `autoParam`, unfold it and repeat. Not observable in
/// accepted terms (plan § Spec deviations 6).
fn whnf_core_unfolding_annotations(
    elab: &mut TermElabM,
    e: ExprId,
) -> Result<ExprId, ElabError> {
    let mut e = e;
    loop {
        e = elab.mctx.whnf_core(e)?;
        if !is_type_annotation(elab, e)? {
            return Ok(e);
        }
        match elab.mctx.unfold_definition_pub(e)? {
            Some(u) => e = u,
            None => return Ok(e),
        }
    }
}

/// oracle: `Expr.isTypeAnnotation` (`Expr.lean:1725-1729`).
fn is_type_annotation(elab: &mut TermElabM, e: ExprId) -> Result<bool, ElabError> {
    let Node::Const { name: Some(c), .. } = node(elab, app_fn(elab, e)) else {
        return Ok(false);
    };
    for n in ["outParam", "semiOutParam", "optParam", "autoParam"] {
        if c == intern_components(elab, &[n])? {
            return Ok(true);
        }
    }
    Ok(false)
}

/// `go` (`App.lean:2016-2058`): resolve against `result_type`'s head;
/// on an oracle error, unfold `result_type` and retry. Postponement,
/// seams and `Meta` / `Internal` failures pass through
/// (`ElabError::is_oracle_error`, the `.internal` rethrow at `:2058`).
fn go(
    elab: &mut TermElabM,
    id: &str,
    explicit_levels: &[LevelId],
    result_type: ExprId,
    expected: ExprId,
) -> Result<ExprId, ElabError> {
    let result_type = elab.mctx.instantiate_mvars(result_type)?;
    match resolve_against(elab, id, explicit_levels, result_type, expected) {
        Ok(e) => Ok(e),
        Err(err) if err.is_oracle_error() => match elab.mctx.unfold_definition_pub(result_type)? {
            Some(t) => with_forall_body(elab, t, |elab, t| go(elab, id, explicit_levels, t, expected)),
            // `:2055-2057`: the oracle logs the earlier failures, then
            // throws this one.
            None => Err(err),
        },
        Err(err) => Err(err),
    }
}

/// The `try` body of `go` (`App.lean:2019-2048`).
fn resolve_against(
    elab: &mut TermElabM,
    id: &str,
    explicit_levels: &[LevelId],
    result_type: ExprId,
    expected: ExprId,
) -> Result<ExprId, ElabError> {
    let head = app_fn(elab, result_type);
    // `:2020`.
    elab.try_postpone_if_mvar(head)?;
    match node(elab, head) {
        Node::Const { name: Some(decl), .. } => {
            let decl_str = render(elab, decl);
            // `isInaccessiblePrivateName` / `privateToUserName`
            // (`:2024-2027`): leanr models no private names.
            if decl_str.starts_with("_private.") {
                return Err(ElabError::UnsupportedSyntax(format!(
                    "`.{id}` against the private type `{decl_str}` (`isInaccessiblePrivateName`, \
                     App.lean:2024) — the slice that models private names"
                )));
            }
            // `fullName := declName ++ id` (`:2027`), one string
            // component under `decl`'s own `NameId`.
            let full = child_name(elab, decl, id)?;
            // `resolveGlobalName … fullName |>.filter (·.2.isEmpty)`
            // (`:2029-2031`): exact name only (spec § Seams after P4).
            if elab.view.get(full).is_some() {
                let display = render(elab, full);
                return mk_const(elab, full, explicit_levels, &display);
            }
            // `:2038-2040`.
            Err(dotted_err(
                id,
                InvalidDottedIdentReason::UnknownConstant {
                    full_name: format!("{decl_str}.{id}"),
                },
            ))
        }
        // `:2041-2042`.
        Node::Sort { .. } => Err(dotted_err(id, InvalidDottedIdentReason::Sort)),
        // `:2043-2048`: syntactic `getAppFn.isMVar` on the ORIGINAL
        // expected type, not instantiated.
        _ => {
            if matches!(node(elab, app_fn(elab, expected)), Node::MVar { .. }) {
                Err(dotted_err(id, InvalidDottedIdentReason::NoExpectedType))
            } else {
                Err(dotted_err(id, InvalidDottedIdentReason::NotConstApp))
            }
        }
    }
}

/// `parent ++ s` for an atomic `s`. `base = Some(view store)`, so a
/// declared name dedups to its persistent id (`head::intern_components`).
fn child_name(elab: &mut TermElabM, parent: NameId, s: &str) -> Result<NameId, ElabError> {
    let base = elab.view.store;
    let store = elab.mctx.store_mut();
    let sid = store.intern_str(Some(base), s).map_err(MetaError::from)?;
    let n = store
        .name_str(Some(base), Some(parent), sid)
        .map_err(MetaError::from)?;
    Ok(n)
}
```

Check `mk_const`'s and `ident_components`' visibility. Both are `pub(crate)` in `head.rs`, so nothing changes.

- [ ] **Step 5: Route the dot identifier and `@.c`**

In `head.rs`, delete `is_lval_head` and its seam arm, and add after the namedPattern arm:

```rust
        // oracle: `` `(.$id:ident) `` / `` `(.$id:ident.{$us,*}) ``
        // (`App.lean:2106-2109`) → `elabDottedIdent` (`:2079-2082`):
        // `resolveDottedIdentFn`, then `elabAppFnResolutions` with no
        // fields. `.{us}` arrive as `explicit_levels` (`app::peel_head`).
        ("Lean.Parser.Term.dotIdent", _) => {
            let raw = dot_ident_text(elem)?;
            let f = crate::app::dot_ident::resolve_dotted_ident_fn(
                elab,
                &raw,
                explicit_levels,
                call.expected,
            )?;
            Ok(vec![crate::app::lval::elab_app_lvals(elab, f, lvals, call, kinds)?])
        }
```

and:

```rust
/// `Term.dotIdent`'s identifier: children `[".", <ident>]`
/// (`term_app.rs`'s `register_dot_ident`).
fn dot_ident_text(elem: &SynElem) -> Result<String, ElabError> {
    let bad = || ElabError::IllFormedSyntax("dotIdent: expected `[\".\", ident]`".to_string());
    let node = elem.as_node().ok_or_else(bad)?;
    match non_trivia_children(node).get(1) {
        Some(leanr_syntax::tree::NodeOrToken::Token(t)) => Ok(t.text().to_string()),
        _ => Err(bad()),
    }
}
```

In `app/mod.rs`:
- delete `ExplicitHead::DotIdent` and `dot_ident_seam`;
- `explicit_head_shape` maps `"Lean.Parser.Term.dotIdent"` to `ExplicitHead::Atom` (the `@.$_:ident` rows, `App.lean:2115-2116`, `:2267-2268`);
- delete the `DotIdent` arms in `elab_explicit` and `peel_head`;
- update `ExplicitHead`'s doc table and the `peel_head` / `elab_explicit` docs, which say `@.f` is a P4 seam, to say it is an `elabAtom` shape like the others;
- update `elab_atom`'s doc to "…leanr routes the first three, `proj` (since M4b-4a P1) and `dotIdent` (since P4)".

In `dispatch.rs`, add `"Lean.Parser.Term.dotIdent" => Some("dotIdent")` to `elaborator_name_for` and, after the pipeProj arm:

```rust
        // oracle: `@[builtin_term_elab dotIdent] elabDotIdent := elabAtom`
        // (`App.lean:2248`).
        ("Lean.Parser.Term.dotIdent", NodeOrToken::Node(_)) => {
            crate::app::elab_atom(elab, elem, kinds, expected)
        }
```

- [ ] **Step 6: Run**

Run: `cargo test -p leanr_elab 2>&1 | tail -40`
Expected: PASS, with 273 records.

If `p4/dot-postponed` fails, the postponed argument's resume is P2's machinery (`elab.rs`'s `elab_using_elab_fns`, `synthetic/ladder.rs`'s `resume_postponed`). Confirm with the nearest P2 form, `(fun x => x.1) (Prod.mk Nat.zero Nat.zero)`, before applying the § Decisions policy.

- [ ] **Step 7: Show the tests discriminate**

Apply, run the Step 6 command, confirm red, revert:
- **N:** delete `with_forall_body`'s `lctx_restore` (keep the checkpoint). `dot_identifier_telescope_does_not_leak_its_binders` must go red.
- **O:** in `with_forall_body`, skip the telescope (call `k(elab, cur)` straight after the first `whnf_core_unfolding_annotations`). `p4/dot-pi` must go red.
- **P:** in `go`, return `Err(err)` without the unfold retry. `p4/dot-unfold` must go red.
- **Q:** make the retry return the FIRST error (keep `err` and discard the retry's error). The `(.foo : NatAlias)` assertion must go red with `NatAlias.foo`.
- **R:** delete BOTH postponement calls: `try_postpone_if_none_or_mvar` (`:1988`) and `resolve_against`'s `try_postpone_if_mvar` (`:2020`). `p4/dot-postponed` must go red.
- **R′:** delete only the `:1988` call. EXPECTED TO SURVIVE.
  - The `:2020` call postpones the same fixture inputs, because an mvar-headed expected type has an mvar-headed result type.
  - A missing expected type is `NoExpectedType` whether or not it postpones first.
  - Record the run. Task 4 lists each call as unpinned on its own.
- **S:** in `resolve_against`'s `_` arm, always return `NotConstApp`. The `(fun x => x) .zero` assertion must go red.
- **T:** in `explicit_head_shape`, map dotIdent to `Other`. `p4/dot-explicit` must go red.
- **U:** replace `whnf_core_unfolding_annotations`'s body with `Ok(elab.mctx.whnf_core(e)?)`. EXPECTED TO SURVIVE (plan § Spec deviations 6). Run it anyway and record that every record stays green, as the evidence for the deviation.

- [ ] **Step 8: Commit**

```bash
git add tests/fixtures/elab crates/leanr_elab
git commit -m "M4b-4a P4: dot identifiers (resolveDottedIdentFn) and @.c"
```

---

### Task 4: Reconcile seams and docs, record the slice

**Files:**
- Modify: `crates/leanr_elab/src/dispatch.rs` (module doc, deferral table, the "still deliberately NOT routed" paragraph)
- Modify: `crates/leanr_elab/src/app/mod.rs` (module-doc seam table, `elab_app_aux` doc)
- Modify: `crates/leanr_elab/src/app/lval.rs` (module doc)
- Modify: `crates/leanr_elab/tests/seam_audit.rs` (needle, `:690-790`)
- Modify: `docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md` (§ Next P4 amendments, § Landed › P4)

- [ ] **Step 1: Find every remaining reference**

Run: `grep -rn "M4b-4a P4\|pipeProj/dotIdent\|dot_ident_seam\|is_lval_head" crates/leanr_elab/src crates/leanr_elab/tests`
Expected: only documentation rows that Step 2 rewrites, and no live (non-comment) source line. A live line is a seam this plan missed: stop and report it.

- [ ] **Step 2: Update the tables**

- `dispatch.rs`:
  - add "Reconciled an ELEVENTH time by M4b-4a P4: `Term.pipeProj`, `Term.dotIdent` and `Term.namedPattern` are routed (`app/head.rs`, `app/dot_ident.rs`), so dot notation is no longer deferred.";
  - change the table row to `Term.pipeProj / dotIdent / namedPattern .... P4 SHIPPED (M4b-4a) — app/head.rs, app/dot_ident.rs`;
  - rewrite the paragraph beginning "`Term.proj` IS routed" so it says only `choice` remains unrouted in this family.
- `app/mod.rs`: in the seam table, change the row to `pipeProj / dotIdent / namedPattern heads, `@.f` .. P4 SHIPPED (M4b-4a) — head.rs, dot_ident.rs`. In `elab_app_aux`'s doc, drop "`pipeProj`/`dotIdent`/`namedPattern` — M4b-4a P4;" from the list of named seams.
- `lval.rs` module doc: add one sentence saying P4 added `suffix` and the two `c ++ suffix` arms.
- `resolve.rs`: nothing further (Task 1 rewrote its doc).

- [ ] **Step 3: Add the needle and show it is not vacuous**

In `seam_audit.rs`'s `no_seam_message_names_a_completed_slice`:
- append `"M4b-4a P4"` to `needles`;
- update the assertion message to "… and M4b-4a P1, P2, P3, P4 are complete …";
- extend the doc comment in the existing style: "**`M4b-4a P4` was added by M4b-4a P4 task 4, and measured non-vacuous.** …". Also retarget its example sentence ("`app/mod.rs`'s `@.f` arm names 'M4b-4a P4'"), which is no longer true, to a live seam that still names an incomplete slice. Find one with `grep -rn '— M4b-4c' crates/leanr_elab/src`.

Measure it:
1. Add a live line `let _ = "M4b-4a P4";` to `app/dot_ident.rs`.
2. Run `cargo test -p leanr_elab --test seam_audit no_seam_message_names_a_completed_slice`. It must fail, naming that line.
3. Remove the line and run it again. It must pass.

Record both runs.

- [ ] **Step 4: Record the slice in the spec**

In `docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md`:

1. Under § Next, after the P3 amendments, add **"P4 amendments (found while planning, measured)"**, with this plan's seven § Spec deviations and the § Decisions escape convention, one bullet each, with their citations.
2. Under § Landed, add `### P4 — identifier forms (PR #<n>)`:
   - what landed: `resolve_local_name` / `resolve_global_name`, `elab_app_fn_id` with `suffix`, the two `c ++ suffix` arms, `pipeProj`, `namedPattern`, `resolve_dotted_ident_fn` with `withForallBody` and `whnfCoreUnfoldingAnnotations`, and `@.c`;
   - the corpus: 39 `p4/*` records, 273 in total;
   - where the rejections live: `lval_smoke.rs`;
   - that the P2 note is closed: "For P4: dotted identifiers on a local … give `UnknownIdent`";
   - open follow-ups:
     - the escape-convention divergences (`fun («x» : Nat) => x.succ`, `Nat.«zero».succ`, `s.«toS1».a`);
     - `pick.eq_1` (reserved names);
     - leanr's missing `ensureAtomicBinderName` (`Binders.lean:188-191`): `fun (x.a : Nat) => …` is accepted by leanr and rejected by the oracle, a pre-existing binder-slice gap;
     - mutations U and R′, expected to survive;
     - every term dropped under § Decisions, with its leanr error and the confirming command;
     - any mutation that could not be made to discriminate, with the reason.
   - Leave the PR number as `#<n>` until the PR exists. The finishing step fills it in before merge; it must not merge as a placeholder.

- [ ] **Step 5: Full CI, blocking**

Run: `mise run ci; echo CI_EXIT=$?`
Run it in the foreground and wait for `CI_EXIT`. Expected: `CI_EXIT=0`. fmt and clippy failures count: fix them and re-run.

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_elab docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md
git commit -m "M4b-4a P4: reconcile seams, record the slice"
```
