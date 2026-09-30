# M4b-4a P3 — generalized field notation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Dot notation resolves a field name that is not a structure field to a namespace constant, as the pinned oracle does. `(Nat.zero).succ` is `Nat.succ Nat.zero`. `fun (s : S3) => (s).get` is `S1.get (S2.toS1 (S3.toS2 s))`. `(Nat.succ).twice Nat.zero` is `Function.twice Nat.succ Nat.zero`. `fun (s : S3Alias) => (s).a` elaborates, where today it hits a seam.

**Architecture:**
- `leanr_meta` gains `get_structure_resolution_order` (relaxed C3, memoized, cycle-guarded) and a non-reducing `forall_meta_telescope` whose mvars carry the binder names.
- `leanr_elab`'s `app/lval.rs` gains:
  - `LValResolution::Const`;
  - `find_method`;
  - the `Const` arms of `resolve_lval_aux` (structure namespace and `Function`);
  - `type_matches_base_name`;
  - `add_lval_arg`, which walks the telescope under a checkpoint/rollback and follows the `whnf` and `coerceToFunction?` continuations;
  - the `Const` arm of `elab_app_lvals` (final and non-final).
- The two `M4b-4a P3` seams in `lval.rs` become real code.

**Tech Stack:** Rust (`leanr_meta` additive, `leanr_elab`), Lean 4 `v4.33.0-rc1` as the differential oracle, `mise` tasks.

**Spec:** `docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md`. Read § P3, § Errors, § Seams after P4, § Testing and all of § Landed (P1 and P2) before starting any task.

## Decisions taken while planning

- **The `numScopeArgs` gap is routed around, not fixed** (user decision, 2026-09-30). P2 recorded that `leanr_meta` lacks `processConstApprox`'s `numScopeArgs` arm. If a record below fails in leanr for a reason that is not P3's:
  1. Check out `main`, rebuild, and confirm that the same failure shows without P3's code, using the nearest P1/P2-reachable form of the term.
  2. Drop the record from `p3Queries`.
  3. Write the term, leanr's error and the confirming command into the task report and into spec § Landed › P3's follow-ups (Task 5).
  Never patch `leanr_meta`'s defeq for it in this slice. Every record below was run on the pinned oracle while planning. None of them has a hole-typed binder, the shape that exposed the gap in P2.

## Spec deviations (found while planning, all measured)

Task 5 records each of these in the spec as a P3 amendment.

1. **`AmbiguousField` is not added.** `findMethod?` throws it only when `resolveGlobalName` returns two or more candidates (`App.lean:1464-1467`). leanr resolves exact names only, so there is never more than one candidate. The variant would be dead code with no test. It belongs to the owner of the existing seam "`findMethod?` candidate resolution uses exact names only" (the `open`/alias slice), which adds it together with the resolution that can reach it.
2. **An extra `leanr_meta` accessor: `forall_meta_telescope`** (non-reducing, `Meta/Basic.lean:1752-1753`). It sits outside the spec's structure-accessor table.
   - `addLValArg` needs it (`App.lean:1751`), and it reads each mvar's `userName` (`:1754-1755`).
   - leanr's only telescope, `forall_meta_telescope_reducing`, mints anonymous `Natural` mvars. It would both reduce (wrong: `:1782` does the `whnf` itself) and lose the names.
   - Minting goes through a generalized `mk_aux_mvar_at` that also takes a `user_name`. This is additive, under the M4b elab→meta accessor precedent.
3. **A new error variant, `MaxRecDepth`**, for `addLValArg.go`'s `withIncRecDepth` (`App.lean:1749`; `Exception.lean:226` throws a plain `.error`). Measured: `CoeFun Loop (fun _ => {u : Nat} → Loop)` makes the oracle report "maximum recursion depth has been reached".
4. **`findMethod?` on a private structure name is a seam.** The oracle applies `privateToUserName` (`App.lean:1458`). leanr models no private names (P1's `isInaccessiblePrivateName` seam, same owner). The fixture has no private structure.
5. **The C3 merge carries a cycle guard.** `computeStructureResolutionOrder` recurses over `parentInfo` with no guard (`Structure.lean:462-470`). `structureExt` rows are untrusted, so a doctored parent cycle returns `None` rather than overflowing the stack. This matches P1's `find_field` and `get_path_to_base_structure`.

## Global Constraints

- Oracle is `leanprover/lean4:v4.33.0-rc1` (`lean-toolchain`). Never bump it.
- Every oracle `file:line` citation written into code or tests is opened against `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/Lean/...` first. Every citation in this plan was opened while writing it. Citations in this repo drift by 1-2 lines, so re-open any you copy anyway.
- `leanr_meta` changes are additive and TCB-neutral:
  - `get_structure_resolution_order`, `forall_meta_telescope`, and `mk_aux_mvar_at`'s new `user_name` parameter;
  - no behaviour change for any existing caller.
  - `leanr_kernel` is untouched.
- No new dependencies.
- Named-seam discipline:
  - A construct owned by a later slice raises `ElabError::UnsupportedSyntax` naming the owner.
  - A genuine oracle error gets a typed variant.
  - `resolve_lval_loop` retries on `is_oracle_error()` only (`ElabError::is_oracle_error`, `error.rs:194`). Every new error variant is an oracle error.
- Every committed `elab-queries.jsonl` record stays byte-identical except those this plan adds. Check with `git diff tests/fixtures/elab/elab-queries.jsonl | grep '^-[^-]'`, which must print nothing.
- **Every new test is shown to discriminate.** The implementer applies the mutation named in the task, watches the test go red, reverts, and records the command and its output in the task report.
  - This repo's plans have named mutations their tests do not kill, repeatedly (four of five tasks in one recent slice). Treat every "Mutation:" line below as a hypothesis until you have run it.
  - If a mutation survives, strengthen the test. Never delete the mutation.
- Before every push: `mise run ci`, blocking, to completion (fmt, clippy, full suite). A subagent must not background it: run it in the foreground and wait for the exit status.
- Build only under `/workspace`, never `/tmp` (a 20Gi EmptyDir; a second cargo target there got the pod evicted).
- Fixture regeneration (never `mise run fixtures:regen`, which also touches Mathlib):
  ```
  cd tests/fixtures/elab && lean Elab0.lean -o Elab0.olean && cd ../../.. && mise run fixtures:regen-elab
  ```
  `fixtures:regen-elab` rewrites both `elab-queries.jsonl` and `structures.jsonl`.
- Oracle checks use a prelude-mode scratch file (in the scratchpad, never committed):
  ```
  prelude
  import Elab0
  set_option pp.explicit true
  set_option pp.fieldNotation false
  #check <term>
  ```
  run as `cd tests/fixtures/elab && LEAN_PATH=$PWD lean /path/to/Chk.lean`. Quote the oracle's message beside every rejection assertion.

## Review Focus

These are the five failure modes most likely to bite a user that no happy-path record exercises. Each has a test, added in the owning task.

1. **A doctored `structureExt` parent cycle must not overflow the stack** in the C3 merge. The oracle has no guard, but well-formed data is acyclic.
   - `get_structure_resolution_order` returns `None` on a cycle, and `find_method` maps that to `ElabError::Internal`.
   - Tests: Task 2 (meta, `resolution_order_of_a_parent_cycle_is_none`) and Task 3 (elab, `parent_cycle_in_structure_ext_is_an_error_not_a_stack_overflow`).
2. **A `CoeFun` instance that reproduces its own carrier must terminate.** `Loop` coerces to `{u : Nat} → Loop` forever, and the oracle stops at `maxRecDepth`. Without a depth cap, leanr loops until the step budget runs out, or forever. Test in Task 4 (`self_reproducing_coe_fun_hits_max_rec_depth`).
3. **A user-written named argument that takes the lval parameter's name consumes that parameter** (`remainingNamedArgs`, `App.lean:1756-1758`). `(s).addTo (s := s)` is `NoLValParameter`: it must not insert `s` twice or overwrite the user's argument. Test in Task 3.
4. **The unfold retry now applies to field NAMES on aliases.** `fun (s : S3Alias) => (s).zzz` reports the missing `S3.zzz` (the unfolded type), not `S3Alias.zzz`. A retry that returns the first error instead of the last would name `S3Alias`. Test in Task 3.
5. **`typeMatchesBaseName` runs at `withReducibleAndInstances`** (`App.lean:1713`). A parameter typed by an `abbrev` alias of `S1` matches, and one typed by a plain `def` alias does not: `(s).ab` elaborates, `(s).df` is `NoLValParameter`. Running at the ambient default transparency would accept both. Record `p3/reducible-param` and the rejection, both in Task 3.

---

## Measured oracle behaviour (the corpus and rejections below)

Every row was run with the scratch-file recipe above, against the Task 1 fixture additions:

| Term | Oracle (`pp.explicit`) |
|---|---|
| `(Nat.zero).succ` | `Nat.succ Nat.zero` |
| `(Nat.zero).succ.succ` | `Nat.succ (Nat.succ Nat.zero)` |
| `fun (s : S3Alias) => (s).a` | `fun s => S1.a (S2.toS1 (S3.toS2 s))` |
| `fun (s : S3) => (s).get` | `fun s => S1.get (S2.toS1 (S3.toS2 s))` |
| `fun (d : D3) => (d).zz` | `fun d => D2.zz (D3.toD2 d)` |
| `fun (q : OQ) => (q).m` | `fun q => OA.m (OQ.toOA q)` |
| `fun (q : OQ) => (q).n` | `fun q => OB.n (OQ.toOB q)` |
| `fun (q : OQ) => (q).k` | `fun q => OC.k (OQ.toOC q)`: C3 order `[OQ,OA,OB,OC,OE]` puts `OC` before `OE`; a DFS over `extends` would pick `OE.k` |
| `fun (q : OQ) => (q).e` | `fun q => OE.e (OC.toOE (OQ.toOC q))` |
| `fun (x : PD Nat) => (x).get` | `fun x => @PB.get Nat (@PC.toPB Nat Nat (@PD.toPC Nat x))` |
| `fun (x : PD Nat) => (x).get.{0}` | same term, level `0` explicit |
| `(Nat.succ).twice Nat.zero` | `Function.twice Nat.succ Nat.zero` |
| `fun (f : Nat → Nat) => (f).twice` | `fun f => Function.twice f` |
| `fun (s : S1) => (s).addTo Nat.zero` | `fun s => S1.addTo Nat.zero s` (positional, index 1) |
| `fun (s : S1) => (s).addTo` | `fun s n => S1.addTo n s` (named `(s := s)`, then eta) |
| `fun (s : S1) => (s).addTo (n := Nat.zero)` | `fun s => S1.addTo Nat.zero s` |
| `fun (s : S1) => (s).imp Nat.zero` | `fun s => @S1.imp s Nat.zero` (implicit, so named) |
| `fun (s : S1) => @(s).imp Nat.zero` | `fun s => @S1.imp s Nat.zero` (explicit mode, so positional) |
| `fun (s : S1) => (s).ab` | `fun s => S1.ab s` |
| `fun (p : Prod Nat Nat) => (p).1.succ` | `fun p => Nat.succ (@Prod.fst Nat Nat p)` |
| `fun (s : S1) => (s).get.succ` | `fun s => Nat.succ (S1.get s)` |
| `fun (s : S2) => (s).toS1.get` | `fun s => S1.get (S2.toS1 s)` |
| `fun (s : S1) => (s).viaDef` | `fun s => S1.viaDef s` (`whnf` continuation) |
| `fun (s : S1) => (s).viaFn` | `fun s => FnS.f S1.viaFn s` (`coerceToFunction?` continuation) |
| `fun (s : S1) => (s).viaDef3` | `fun s n => S1.viaDef3 n s` (`whnf` continuation with `argIdx > args.size`, then named) |

Rejections:

| Term | Oracle message |
|---|---|
| `(Nat.zero).foo` | "Invalid field `foo`: The environment does not contain `Nat.foo`, so it is not possible to project the field `foo` from an expression Nat.zero of type `Nat`" |
| `fun (s : S3Alias) => (s).zzz` | "Invalid field `zzz`: The environment does not contain `S3.zzz` … of type `S3`" |
| `fun (s : S2) => (s).zzz` | "Invalid field `zzz`: The environment does not contain `S2.zzz` … of type `S2`" |
| `fun (s : S1) => (s).get.twice` | "Invalid field `twice`: The environment does not contain `Nat.twice` … of type `Nat`" |
| `fun (s : S1) => (s).bad` | "Invalid field notation: `S1.bad` has a parameter with expected type S1 but it cannot be used. Note: The parameter `s` cannot be referred to by name because that function has a preceding parameter of the same name" |
| `fun (s : S1) => (s).none` | "Invalid field notation: Function `S1.none` does not have a usable parameter of type `S1` for which to substitute `s`" |
| `fun (s : S1) => (s).addTo (s := s)` | "… Function `S1.addTo` does not have a usable parameter of type `S1` …" |
| `fun (s : S1) => (s).df` | "… Function `S1.df` does not have a usable parameter of type `S1` …" |
| `(Nat.zero).succ.{0}` | "too many explicit universe levels for `Nat.succ`" |
| `fun (s : S1) => (s).imp.succ` | "Invalid field `succ`: The environment does not contain `Function.succ` … from an expression @S1.imp s of type `Nat → Nat`" (the non-final step's `explicit := false` makes `s` a named argument) |
| `fun (s : S1) => (s).viaFnI` | "Invalid field notation: `FnI.f` (coerced from `S1.viaFnI`) has a parameter with expected type S1 but it cannot be used. Note: Field notation cannot refer to parameter `s` by name because that constant was coerced to a function" |
| `fun (s : S1) => (s).loop` | "maximum recursion depth has been reached" |

---

## File Structure

| File | Responsibility | Task |
|---|---|---|
| `tests/fixtures/elab/Elab0.lean`, `Elab0.olean`, `structures.jsonl` | P3 declarations | 1 |
| `crates/leanr_meta/src/structure.rs` | `get_structure_resolution_order` (C3), memo field | 2 |
| `crates/leanr_meta/src/assign.rs` | `mk_aux_mvar_at` takes `user_name` | 2 |
| `crates/leanr_meta/src/synth.rs` | `forall_meta_telescope` beside `forall_meta_telescope_reducing` | 2 |
| `crates/leanr_meta/tests/structures.rs` | `order` compared against the dump; cycle test | 2 |
| `crates/leanr_elab/src/error.rs` | `UnusableLValParameter`, `NoLValParameter`, `MaxRecDepth` | 3, 4 |
| `crates/leanr_elab/src/app/lval.rs` | `Const`, `find_method`, `type_matches_base_name`, `add_lval_arg`, `elab_app_lvals` `Const` arm | 3, 4 |
| `crates/leanr_elab/src/builtin/binder/fun.rs` | `cleanup_annotations` → `pub(crate)` | 3 |
| `crates/leanr_elab/tests/lval_smoke.rs` | flipped seams, P3 rejections | 3, 4 |
| `crates/leanr_elab/tests/oracle_elab.rs` | corpus floor | 3, 4 |
| `tests/fixtures/elab/dump_elab.lean`, `elab-queries.jsonl` | `p3Queries` | 3, 4 |
| `crates/leanr_elab/src/dispatch.rs`, `src/app/mod.rs`, `tests/seam_audit.rs` | deferral tables, `M4b-4a P3` needle | 5 |
| spec § Landed › P3, P3 amendments | record | 5 |

---

### Task 1: Fixture declarations

**Files:**
- Modify: `tests/fixtures/elab/Elab0.lean` (append after `structure FI`, the file's last declaration)
- Regenerate: `tests/fixtures/elab/Elab0.olean`, `tests/fixtures/elab/structures.jsonl`, `tests/fixtures/elab/elab-queries.jsonl` (must not change)

**Interfaces:**
- Produces fixture constants: `S1.get S1.addTo S1.imp S1.bad S1.none S1Ab S1Df S1.ab S1.df S1Fn S1.viaDef S1Fn3 S1.viaDef3 D2.zz OA.m OB.n OC.k OE.k OE.e PB.get Function.twice FnS instCoeFunFnS S1.viaFn FnI instCoeFunFnI S1.viaFnI Loop instCoeFunLoop S1.loop`.
- New structures (so new `structures.jsonl` lines): `FnS`, `FnI`, `Loop`.

- [ ] **Step 1: Append the declarations**

Append to `tests/fixtures/elab/Elab0.lean`:

```lean
-- === M4b-4a P3: generalized field notation ===
-- Namespace methods reached by `findMethod?` (App.lean:1453-1477), each
-- in a namespace of the fixture's P1 structures. Bodies are irrelevant;
-- the linter is off because most parameters exist only to be the lval
-- target.
section P3
set_option linter.unusedVariables false
-- `S3`'s resolution order is `[S3, S2, S1]`: `(s).get` on an `S3` finds
-- `S1.get` last and needs `mkBaseProjections` (App.lean:1874).
def S1.get (s : S1) : Nat := s.a
-- The `S1` parameter is SECOND: positional insertion at index 1 when an
-- argument is given, the named `(s := e)` fallback when none is
-- (App.lean:1764-1776).
def S1.addTo (n : Nat) (s : S1) : Nat := n
-- An implicit `S1` parameter: named insertion unless `@` is used.
def S1.imp {s : S1} (n : Nat) : Nat := n
-- A preceding parameter already called `s`: the `S1` one is unusable
-- (App.lean:1771-1772, `throwUnusableParameter`).
def S1.bad (s : Nat) {s : S1} : Nat := Nat.zero
-- No `S1` parameter at all (App.lean:1792).
def S1.none (n : Nat) : Nat := n
-- `typeMatchesBaseName` runs `withReducibleAndInstances`
-- (App.lean:1712-1726): the `abbrev` alias matches, the `def` does not.
abbrev S1Ab : Type := S1
def S1Df : Type := S1
def S1.ab (s : S1Ab) : Nat := Nat.zero
def S1.df (s : S1Df) : Nat := Nat.zero
-- A method whose TYPE is a `def` alias of a pi: `forallMetaTelescope`
-- finds no binder, the `whnf` continuation (App.lean:1782-1783) does.
def S1Fn : Type := S1 → Nat
def S1.viaDef : S1Fn := S1.a
-- An explicit `Nat` first, THEN the alias: after the first telescope
-- `argIdx = 1 > args.size = 0`, and only `allowNamed ||` (App.lean:1781)
-- keeps the walk going into the `whnf` continuation.
def S1Fn3 : Type := (s : S1) → Nat
def S1.viaDef3 (n : Nat) : S1Fn3 := fun _ => n
-- `D2` is a NON-subobject parent of `D3`: `(d).zz` goes through the
-- `D3.toD2` parent projection.
def D2.zz (d : D2) : Nat := d.z
-- `OQ`'s C3 resolution order is `[OQ, OA, OB, OC, OE]` (structures.jsonl).
-- `OC.k` vs `OE.k` separates C3 from a DFS over `extends` (which visits
-- `OE` through `OB` before `OC`).
def OA.m (x : OA) : Nat := Nat.zero
def OB.n (x : OB) : Nat := Nat.zero
def OC.k (x : OC) : Nat := Nat.zero
def OE.k (x : OE) : Nat := Nat.zero
def OE.e (x : OE) : Nat := Nat.zero
-- Parametric base: `(x).get` on `PD Nat` walks `PD.toPC`, `PC.toPB`.
def PB.get {α : Type u} (x : PB α) : α := x.b
-- `Function` namespace for pi-typed terms (App.lean:1580-1583).
def Function.twice (f : Nat → Nat) (x : Nat) : Nat := f (f x)
-- `coerceToFunction?` continuation (App.lean:1784-1785): `S1.viaFn : FnS`
-- is not a function until `CoeFun` makes it `S1 → Nat`.
structure FnS where
  f : S1 → Nat
instance instCoeFunFnS : CoeFun FnS (fun _ => S1 → Nat) := ⟨FnS.f⟩
def S1.viaFn : FnS := FnS.mk S1.a
-- Same, but the coerced parameter is implicit, and after a coercion
-- named insertion is disabled (`allowNamed := false`).
structure FnI where
  f : {s : S1} → Nat
instance instCoeFunFnI : CoeFun FnI (fun _ => {s : S1} → Nat) := ⟨FnI.f⟩
def S1.viaFnI : FnI := FnI.mk (fun {s} => s.a)
-- A carrier that coerces to a function returning itself: `addLValArg.go`
-- recurses until `withIncRecDepth` stops it (App.lean:1749).
structure Loop where
  f : {u : Nat} → Loop
instance instCoeFunLoop : CoeFun Loop (fun _ => {u : Nat} → Loop) := ⟨Loop.f⟩
axiom S1.loop : Loop
end P3
```

- [ ] **Step 2: Rebuild the olean and regenerate**

Run:
```bash
cd tests/fixtures/elab && lean Elab0.lean -o Elab0.olean && cd ../../.. \
  && mise run fixtures:regen-elab \
  && git diff --stat tests/fixtures/elab/elab-queries.jsonl \
  && git diff tests/fixtures/elab/structures.jsonl | grep '^[-+]{' | cut -c1-60
```
Expected:
- `Elab0.olean` builds with no errors (the unused-variable warnings are silenced).
- `elab-queries.jsonl` shows no diff.
- `structures.jsonl` gains exactly three `+` lines (`FnS`, `FnI`, `Loop`) and loses none.

- [ ] **Step 3: Run the existing suites against the new fixture**

Run: `cargo test -p leanr_elab -p leanr_meta -p leanr_olean 2>&1 | tail -30`
Expected: PASS, apart from these known failures:
- `lval_smoke.rs`'s `projection_seams_…`, whose `(Nat.zero).succ` and `S3Alias` assertions still expect the seam. It still passes, because P3's code is not written yet; nothing flips until Task 3.
- `structures.rs`, which must still pass: it compares every structure, including the three new ones.

Any other failure means a new instance or declaration changed an existing elaboration. The three `CoeFun` instances are the likely cause. Stop and report it; do not adjust existing tests.

- [ ] **Step 4: Commit**

```bash
git add tests/fixtures/elab/Elab0.lean tests/fixtures/elab/Elab0.olean tests/fixtures/elab/structures.jsonl
git commit -m "M4b-4a P3: fixture declarations for generalized field notation"
```

---

### Task 2: `leanr_meta` — C3 resolution order and `forall_meta_telescope`

**Files:**
- Modify: `crates/leanr_meta/src/structure.rs` (`StructureTable` gains a memo; new method)
- Modify: `crates/leanr_meta/src/assign.rs:709-731` (`mk_aux_mvar_at` gains `user_name`), and every caller of `mk_aux_mvar_at` (find them with `grep -rn "mk_aux_mvar_at(" crates/leanr_meta/src`)
- Modify: `crates/leanr_meta/src/synth.rs` (add `forall_meta_telescope` after `forall_meta_telescope_reducing`, `:2612`)
- Test: `crates/leanr_meta/tests/structures.rs`; unit tests in `synth.rs`'s test module

**Interfaces:**
- Produces: `pub fn get_structure_resolution_order(&mut self, s: NameId) -> Option<Vec<NameId>>` on `MetaCtx`. It returns `None` only on a parent cycle. A non-structure gives `Some(vec![s])`, as the oracle's empty `parentInfo` does.
- Produces: `pub fn forall_meta_telescope(&mut self, ty: ExprId) -> Result<(Vec<ExprId>, Vec<BinderInfo>, ExprId), MetaError>`. Each mvar's `MVarDecl.user_name` is the binder name. Inst-implicit binders mint `MVarKind::Synthetic` mvars, all others `Natural`. It does not `whnf`.
- Changes: `pub(crate) fn mk_aux_mvar_at(&mut self, lctx, ty, kind, user_name: Option<NameId>)`. Existing callers pass `None`.

- [ ] **Step 1: Write the failing resolution-order test**

In `crates/leanr_meta/tests/structures.rs`, `structure_accessors_match_the_oracle_dump`:
- make the context mutable (`let mut ctx = MetaCtx::new(…)`);
- change `render` to a function taking the store, so the closure does not hold `ctx` borrowed across the `&mut` call: `let render = |ctx: &MetaCtx, n| name_to_string(ctx.store(), base, Some(n));`;
- update the existing `render(…)` calls to `render(&ctx, …)`;
- add, inside the per-structure loop:

```rust
        // `getStructureResolutionOrder` (Structure.lean:512-514), relaxed C3.
        let want_order: Vec<String> = rec["order"]
            .as_array()
            .unwrap()
            .iter()
            .map(|x| x.as_str().unwrap().to_string())
            .collect();
        let got_order: Vec<String> = ctx
            .get_structure_resolution_order(sid)
            .expect("well-formed fixture: no parent cycle")
            .into_iter()
            .map(|n| render(&ctx, n))
            .collect();
        assert_eq!(got_order, want_order, "{s}: resolution order");
```

And after the loop, beside the other non-structure checks:

```rust
    // A non-structure's order is itself (`getStructureParentInfo` is empty).
    assert_eq!(ctx.get_structure_resolution_order(nat), Some(vec![nat]));
```

- [ ] **Step 2: Write the failing cycle test**

`Replayed.structures` is an owned `Vec<StructureInfo>` (`tests/support/mod.rs:56`), so the test doctors it before `MetaCtx::new`. The doctoring is shape-only and needs no names: every `extends` edge gets a reverse edge, so each parent–child pair becomes a 2-cycle (S3 → S2 → S3, …). Add to `crates/leanr_meta/tests/structures.rs`:

```rust
/// Review Focus 1: `computeStructureResolutionOrder` recurses over
/// `parentInfo` with no guard (Structure.lean:462-470); well-formed
/// data is acyclic, `.olean` rows are untrusted. With every `extends`
/// edge doubled back (`S2`'s parents gain `S3`, …) the order of `S3`
/// must be `None`, not a stack overflow. A structure with neither
/// parents nor children (`Add`) is unaffected.
#[test]
fn resolution_order_of_a_parent_cycle_is_none() {
    let mut r = replay_fixture_in("elab", "Elab0.olean");
    let edges: Vec<(NameId, NameId, NameId)> = r
        .structures
        .iter()
        .flat_map(|s| {
            s.parent_info
                .iter()
                .map(move |p| (p.struct_name, s.struct_name, p.proj_fn))
        })
        .collect();
    for (parent, child, proj_fn) in edges {
        if let Some(p) = r.structures.iter_mut().find(|s| s.struct_name == parent) {
            p.parent_info.push(leanr_olean::StructureParentInfo {
                struct_name: child,
                subobject: false,
                proj_fn,
            });
        }
    }
    let view = r.env.view();
    let mut scratch = Store::scratch();
    let base = Some(view.store);
    let s3 = decode_name(&mut scratch, base, "S3");
    let add = decode_name(&mut scratch, base, "Add");
    let mut ctx = MetaCtx::new(
        view,
        &mut scratch,
        Config::default(),
        EnvExtensions {
            structures: &r.structures,
            ..Default::default()
        },
    );
    assert_eq!(ctx.get_structure_resolution_order(s3), None);
    assert_eq!(ctx.get_structure_resolution_order(add), Some(vec![add]));
}
```

Import `NameId` (`leanr_kernel::bank::NameId`) if the file does not already. `StructureParentInfo`'s fields are `struct_name`, `subobject`, `proj_fn` (`leanr_olean/src/module_data.rs`, used as such by `structure.rs`'s `path_go`).

Run: `cargo test -p leanr_meta --test structures 2>&1 | tail -20`
Expected: FAIL to compile, "no method named `get_structure_resolution_order`".

- [ ] **Step 3: Implement the C3 merge**

In `crates/leanr_meta/src/structure.rs`, give `StructureTable` a memo:

```rust
#[derive(Default)]
pub(crate) struct StructureTable {
    by_name: HashMap<NameId, StructureInfo>,
    /// oracle: `structureResolutionExt` (Structure.lean:421-422), "a mere
    /// cache". Sound because `structureExt` rows never change while a
    /// `MetaCtx` lives.
    resolution_orders: HashMap<NameId, Vec<NameId>>,
}
```

(`build` initializes it with `HashMap::new()`.) Add to the `impl MetaCtx` block:

```rust
    /// oracle: `getStructureResolutionOrder` (`Structure.lean:512-514`) —
    /// `computeStructureResolutionOrder structName (relaxed := true)`
    /// (`:462-470`), the C3 merge (`mergeStructureResolutionOrders`,
    /// `:472-503`) memoized as the oracle memoizes it. `None` only for a
    /// parent cycle, which well-formed data never has and the oracle
    /// would recurse on forever; see `find_field`'s doc.
    pub fn get_structure_resolution_order(&mut self, s: NameId) -> Option<Vec<NameId>> {
        self.resolution_order_go(s, &mut HashSet::new())
    }

    fn resolution_order_go(
        &mut self,
        s: NameId,
        in_progress: &mut HashSet<NameId>,
    ) -> Option<Vec<NameId>> {
        if let Some(o) = self.structures.resolution_orders.get(&s) {
            return Some(o.clone());
        }
        if !in_progress.insert(s) {
            return None;
        }
        // `getStructureParentInfo env structName |>.map (·.structName)`:
        // empty for a non-structure.
        let parent_names: Vec<NameId> = self
            .get_structure_info(s)
            .map_or_else(Vec::new, |i| i.parent_info.iter().map(|p| p.struct_name).collect());
        let mut res_orders: Vec<Vec<NameId>> = Vec::with_capacity(parent_names.len() + 1);
        // `parentResOrders.insertIdx 0 parentNames |>.filter (!·.isEmpty)`.
        res_orders.push(parent_names.clone());
        for &p in &parent_names {
            res_orders.push(self.resolution_order_go(p, in_progress)?);
        }
        res_orders.retain(|o| !o.is_empty());
        let mut order = vec![s];
        while !res_orders.is_empty() {
            let name = select_parent(&res_orders);
            order.push(name);
            for o in res_orders.iter_mut() {
                o.retain(|&n| n != name);
            }
            res_orders.retain(|o| !o.is_empty());
        }
        in_progress.remove(&s);
        self.structures.resolution_orders.insert(s, order.clone());
        Some(order)
    }
```

and, as a free function in the same file:

```rust
/// oracle: `mergeStructureResolutionOrders.selectParent`
/// (`Structure.lean:492-503`), relaxed: for `n' = 0, 1, …`, ignore the
/// last `n'` orders and take the first head that appears in no other
/// considered order's TAIL. Every order is nonempty (caller invariant).
/// The `good` flag only feeds the strict mode's conflict report, which
/// `getStructureResolutionOrder` never asks for.
fn select_parent(res_orders: &[Vec<NameId>]) -> NameId {
    for n_skip in 0..res_orders.len() {
        let hi = res_orders.len() - n_skip;
        for i in 0..hi {
            let parent = res_orders[i][0];
            let consistent = |o: &Vec<NameId>| o[1..].iter().all(|&n| n != parent);
            if res_orders[..i].iter().all(consistent) && res_orders[i + 1..hi].iter().all(consistent) {
                return parent;
            }
        }
    }
    res_orders[0][0]
}
```

Open `Structure.lean:472-503` and check the loop bounds against it: `*...resOrders.size` is `0..size`, `*...hi` is `0..hi`, `[*...<i]` is `[..i]`, and `[i<...hi]` is `[i+1..hi]`.

- [ ] **Step 4: Run the structure tests**

Run: `cargo test -p leanr_meta --test structures 2>&1 | tail -20`
Expected: PASS (both tests).

- [ ] **Step 5: Show the tests discriminate**

Apply each mutation, run the command from Step 4, confirm red, then revert:
- **Mutation A:** in `resolution_order_go`, drop the `res_orders.push(parent_names.clone())` line. The parent list is then no longer a constraint.
- **Mutation B:** in `select_parent`, replace the whole body with `res_orders[0][0]`. That is "first head", not C3. The order-sensitive `OQ` row must go red.
- **Mutation C:** delete the `if !in_progress.insert(s) { return None; }` guard. The cycle test must abort with a stack overflow; a SIGABRT counts as red.

Record all three outputs.

- [ ] **Step 6: Write the failing telescope test**

In `crates/leanr_meta/src/synth.rs`'s test module, after `forall_meta_telescope_reducing_returns_one_mvar_and_info_per_binder` (`:3464`), add:

```rust
    /// oracle: `forallMetaTelescope` (`Lean/Meta/Basic.lean:1752-1753`,
    /// worker `:1717-1741`): one mvar per syntactic binder, named after
    /// the binder (`mkFreshExprMVar d k n`, `:1729`), `.synthetic` for an
    /// inst-implicit binder (`:1727`). `addLValArg` reads both
    /// (`App.lean:1754-1755`).
    #[test]
    fn forall_meta_telescope_names_its_mvars_and_kinds_inst_implicit_synthetic() {
        with_instances_ctx(|ctx| {
            let ty = three_binder_test_type(ctx);
            let (mvars, bis, _) = ctx.forall_meta_telescope(ty).expect("telescope runs");
            assert_eq!(
                bis,
                vec![BinderInfo::Implicit, BinderInfo::InstImplicit, BinderInfo::Default]
            );
            let kinds: Vec<MVarKind> = mvars
                .iter()
                .map(|&m| match ctx.node(m) {
                    Node::MVar { id: Some(n) } => ctx.mctx().decl(MVarId(n)).unwrap().kind,
                    o => panic!("expected an mvar, got {o:?}"),
                })
                .collect();
            assert_eq!(
                kinds,
                vec![MVarKind::Natural, MVarKind::Synthetic, MVarKind::Natural]
            );
            // A NAMED binder: `(x : Prop) → Prop`.
            let base = Some(ctx.view.store);
            let xs = ctx.scratch.intern_str(base, "x").unwrap();
            let x = ctx.scratch.name_str(base, None, xs).unwrap();
            let zero = ctx.scratch.level_zero(base).unwrap();
            let prop = ctx.scratch.expr_sort(base, zero).unwrap();
            let named = ctx
                .scratch
                .expr_forall(base, Some(x), prop, prop, BinderInfo::Default)
                .unwrap();
            let (mvars, _, body) = ctx.forall_meta_telescope(named).expect("telescope runs");
            let Node::MVar { id: Some(n) } = ctx.node(mvars[0]) else {
                panic!("expected an mvar")
            };
            assert_eq!(ctx.mctx().decl(MVarId(n)).unwrap().user_name, Some(x));
            assert_eq!(body, prop);
        });
    }
```

Import `MVarId`/`MVarKind` in the test module if it does not already. Check `level_zero`'s signature: `resolve.rs`'s tests call `store.level_zero(None)`, so pass `base` or `None` to match. Non-reduction (`reducing := false`) is left out of the test on purpose: the body contains no `whnf` call, and no P3 term observes the difference, since `addLValArg` runs its own `whnf` at `:1782` and would reach the same binder either way.

Run: `cargo test -p leanr_meta forall_meta_telescope 2>&1 | tail -20`
Expected: FAIL to compile.

- [ ] **Step 7: Implement**

In `assign.rs`, give `mk_aux_mvar_at` a trailing `user_name: Option<NameId>` parameter and store it in `MVarDecl.user_name`. Update each caller to pass `None`, including `mk_aux_mvar` at `:691-694`. Extend the doc with one sentence: "`user_name` is `forall_meta_telescope`'s binder name (`mkFreshExprMVar d k n`, `Meta/Basic.lean:1729`); every other caller passes `None`."

In `synth.rs`, after `forall_meta_telescope_reducing`:

```rust
    /// oracle: `forallMetaTelescope` (`Lean/Meta/Basic.lean:1752-1753`) —
    /// `forallMetaTelescopeReducingAux` with `reducing := false`: peel the
    /// SYNTACTIC `forallE` binders only, minting each mvar with the
    /// binder's name as its `userName` and `.synthetic` kind for an
    /// inst-implicit binder (`:1727-1729`). `addLValArg` reads both
    /// (`App.lean:1751-1755`) and does its own `whnf` (`:1782`).
    #[allow(clippy::type_complexity)]
    pub fn forall_meta_telescope(
        &mut self,
        ty: ExprId,
    ) -> Result<(Vec<ExprId>, Vec<BinderInfo>, ExprId), MetaError> {
        let base = Some(self.view.store);
        let mut cur = ty;
        let mut mvars = Vec::new();
        let mut bis = Vec::new();
        while let Node::Forall { binder_name, binder_type, body, binder_info } = self.node(cur) {
            self.step()?;
            let d = instantiate_rev(self.scratch, base, binder_type, &mvars, &mut self.guard)?;
            let kind = if binder_info == BinderInfo::InstImplicit {
                MVarKind::Synthetic
            } else {
                MVarKind::Natural
            };
            let lctx = self.current_lctx();
            let (m, _) = self.mk_aux_mvar_at(lctx, d, kind, binder_name)?;
            mvars.push(m);
            bis.push(binder_info);
            cur = body;
        }
        let body = instantiate_rev(self.scratch, base, cur, &mvars, &mut self.guard)?;
        Ok((mvars, bis, body))
    }
```

Check that `instantiate_rev`'s argument order matches its use in `forall_meta_telescope_reducing` directly above. That function keeps a separate `subst` because it resets at every `whnf`; here `mvars` is the substitution.

- [ ] **Step 8: Run, then show the test discriminates**

Run: `cargo test -p leanr_meta 2>&1 | tail -20`
Expected: PASS.
- **Mutation D:** pass `None` instead of `binder_name`. The `user_name` asserts must go red.
- **Mutation E:** always use `MVarKind::Natural`. The kind assert must go red.
Record both.

- [ ] **Step 9: Commit**

```bash
git add crates/leanr_meta
git commit -m "M4b-4a P3: C3 structure resolution order and forall_meta_telescope"
```

---

### Task 3: `find_method`, the `Const` resolution and `add_lval_arg`'s telescope walk

**Files:**
- Modify: `crates/leanr_elab/src/error.rs` (two variants, after `InvalidField`)
- Modify: `crates/leanr_elab/src/app/lval.rs`
- Modify: `crates/leanr_elab/src/builtin/binder/fun.rs:41` (`cleanup_annotations` → `pub(crate)`)
- Modify: `crates/leanr_elab/tests/lval_smoke.rs`
- Modify: `tests/fixtures/elab/dump_elab.lean` (`p3Queries`, and add it to `main`'s list), `tests/fixtures/elab/elab-queries.jsonl` (regenerated)
- Modify: `crates/leanr_elab/tests/oracle_elab.rs` (floor)

**Interfaces:**
- Consumes (Task 2): `MetaCtx::get_structure_resolution_order`, `MetaCtx::forall_meta_telescope`.
- Produces:
  - `ElabError::UnusableLValParameter { f: ExprId, param: String, allow_named: bool }`;
  - `ElabError::NoLValParameter { f: ExprId, base: String }`;
  - private `lval.rs` functions `find_method`, `type_matches_base_name`, `add_lval_arg`, with the signatures below.
- Task 4 extends `add_lval_arg`'s `go` with the two continuations; this task stops `go` after the telescope loop.

- [ ] **Step 1: Write the failing corpus records**

In `tests/fixtures/elab/dump_elab.lean`, after `p2Queries`:

```lean
-- M4b-4a P3: generalized field notation (`findMethod?`, `addLValArg`,
-- App.lean:1453-1477, :1735-1828). Every source was run on the pinned
-- oracle while planning (plan § Measured oracle behaviour).
def p3Queries : List (String × String) :=
  [ ("p3/nat-succ",            "(Nat.zero).succ")
  , ("p3/nat-succ-chain",      "(Nat.zero).succ.succ")
  , ("p3/alias-field",         "fun (s : S3Alias) => (s).a")
  , ("p3/inherited-method",    "fun (s : S3) => (s).get")
  , ("p3/diamond-method",      "fun (d : D3) => (d).zz")
  , ("p3/c3-first",            "fun (q : OQ) => (q).m")
  , ("p3/c3-nonsubobject",     "fun (q : OQ) => (q).n")
  , ("p3/c3-order",            "fun (q : OQ) => (q).k")
  , ("p3/c3-deep",             "fun (q : OQ) => (q).e")
  , ("p3/param-base",          "fun (x : PD Nat) => (x).get")
  , ("p3/param-base-univ",     "fun (x : PD Nat) => (x).get.{0}")
  , ("p3/function-arg",        "(Nat.succ).twice Nat.zero")
  , ("p3/function-partial",    "fun (f : Nat -> Nat) => (f).twice")
  , ("p3/positional",          "fun (s : S1) => (s).addTo Nat.zero")
  , ("p3/named-eta",           "fun (s : S1) => (s).addTo")
  , ("p3/named-with-named",    "fun (s : S1) => (s).addTo (n := Nat.zero)")
  , ("p3/implicit-named",      "fun (s : S1) => (s).imp Nat.zero")
  , ("p3/explicit-positional", "fun (s : S1) => @(s).imp Nat.zero")
  , ("p3/reducible-param",     "fun (s : S1) => (s).ab")
  , ("p3/proj-then-method",    "fun (p : Prod Nat Nat) => (p).1.succ")
  , ("p3/method-then-method",  "fun (s : S1) => (s).get.succ")
  , ("p3/field-then-method",   "fun (s : S2) => (s).toS1.get")
  ]
```

Append `++ p3Queries` to the query list in `main` (the `for (id, src) in … ++ p2Queries do` line). Regenerate:

```bash
mise run fixtures:regen-elab 2>&1 | tail -5 \
  && wc -l tests/fixtures/elab/elab-queries.jsonl \
  && git diff tests/fixtures/elab/elab-queries.jsonl | grep '^-[^-]'
```
Expected:
- no `dump_elab: … error` lines on stderr (the oracle elaborates all 22);
- `230` lines (208 + 22);
- the grep prints nothing.

In `crates/leanr_elab/tests/oracle_elab.rs`, raise the floor to 230, adding a comment line in the existing style: `// 208 -> 230 (M4b-4a P3 task 3): the 22 p3/* records.`

Run: `cargo test -p leanr_elab --test oracle_elab 2>&1 | tail -30`
Expected: FAIL. The `p3/*` records report `UnsupportedSyntax(… M4b-4a P3)`; `p3/proj-then-method` fails on its final `.succ`.

- [ ] **Step 2: Flip the P1 seam assertions to the oracle's answers**

In `crates/leanr_elab/tests/lval_smoke.rs`, replace the three P3 seam assertions (the `(Nat.zero).succ` line and the two `S3Alias` blocks, `:123-143`) with:

```rust
    // Review Focus 4: the unfold retry reaches field NAMES now. The
    // oracle's `findMethod?` on `S3Alias` finds nothing, `resolveLValLoop`
    // retries on the unfolded `S3` (App.lean:1688-1692), which also has
    // no `zzz`, and the LAST error is the one reported: "Invalid field
    // `zzz`: The environment does not contain `S3.zzz` … of type `S3`".
    assert_eq!(
        field_reason("fun (s : S3Alias) => (s).zzz"),
        InvalidFieldReason::NotFound { full_name: "S3.zzz".to_string() }
    );
```

Add the helper beside `proj_reason`:

```rust
fn field_reason(src: &str) -> InvalidFieldReason {
    match support::elab_and_synthesize(src) {
        Err(ElabError::InvalidField { reason, .. }) => reason,
        other => panic!("{src}: expected InvalidField, got {other:?}"),
    }
}
```

(`(Nat.zero).succ` and `(s).a` on `S3Alias` are now corpus records, `p3/nat-succ` and `p3/alias-field`.)

In `subobject_cycle_in_structure_ext_is_an_error_not_a_stack_overflow` (`:283-307`), the doctored run of `(s).zzz` on `S2` now gets past the field lookup to `findMethod?`, whose order over `S2`'s `parent_info` is well-formed (only `subobject` was doctored). Change the expected result to:

```rust
    match r {
        Err(ElabError::InvalidField { reason: InvalidFieldReason::NotFound { full_name }, .. }) => {
            assert_eq!(full_name, "S2.zzz")
        }
        other => panic!("expected InvalidField NotFound, got {other:?}"),
    }
```

and update the comment above the `match`: "With the cycle cut, `zzz` is not a field of `S2`, and `findMethod?` finds no `S2.zzz`: the oracle's error on well-formed data."

- [ ] **Step 3: Write the failing rejection tests**

Append to `crates/leanr_elab/tests/lval_smoke.rs`:

```rust
/// M4b-4a P3 rejections. Each message is the pinned oracle's (plan
/// § Measured oracle behaviour; `#check` on a prelude file importing
/// `Elab0`).
#[test]
fn generalized_field_notation_rejections_match_the_oracle() {
    // "Invalid field `foo`: The environment does not contain `Nat.foo`"
    assert_eq!(
        field_reason("(Nat.zero).foo"),
        InvalidFieldReason::NotFound { full_name: "Nat.foo".to_string() }
    );
    // "… does not contain `S2.zzz` … of type `S2`"
    assert_eq!(
        field_reason("fun (s : S2) => (s).zzz"),
        InvalidFieldReason::NotFound { full_name: "S2.zzz".to_string() }
    );
    // A non-final `Const` step feeds the next lval: `S1.get s : Nat`,
    // so `.twice` looks in `Nat`, not `Function`. "… does not contain
    // `Nat.twice` … of type `Nat`"
    assert_eq!(
        field_reason("fun (s : S1) => (s).get.twice"),
        InvalidFieldReason::NotFound { full_name: "Nat.twice".to_string() }
    );
    // "Invalid field notation: `S1.bad` has a parameter with expected
    // type S1 but it cannot be used. Note: The parameter `s` cannot be
    // referred to by name because that function has a preceding
    // parameter of the same name"
    match support::elab_and_synthesize("fun (s : S1) => (s).bad") {
        Err(ElabError::UnusableLValParameter { param, allow_named, .. }) => {
            assert_eq!(param, "s");
            assert!(allow_named);
        }
        other => panic!("expected UnusableLValParameter, got {other:?}"),
    }
    // "Invalid field notation: Function `S1.none` does not have a usable
    // parameter of type `S1` for which to substitute `s`"
    // Review Focus 3: `(s := s)` consumes the only `S1` parameter
    // (`remainingNamedArgs`, App.lean:1756-1758) — same message for `S1.addTo`.
    // Review Focus 5: `S1Df` is a `def`, invisible at
    // `withReducibleAndInstances` — same message for `S1.df`.
    for src in [
        "fun (s : S1) => (s).none",
        "fun (s : S1) => (s).addTo (s := s)",
        "fun (s : S1) => (s).df",
    ] {
        match support::elab_and_synthesize(src) {
            Err(ElabError::NoLValParameter { base, .. }) => assert_eq!(base, "S1", "{src}"),
            other => panic!("{src}: expected NoLValParameter, got {other:?}"),
        }
    }
    // The non-final `Const` step runs `addLValArg` with `explicit :=
    // false` (App.lean:1882): `s` fills `{s : S1}` by name, leaving
    // `@S1.imp s : Nat → Nat`, so `.succ` looks in `Function`. "… does
    // not contain `Function.succ` … of type `Nat → Nat`"
    assert_eq!(
        field_reason("fun (s : S1) => (s).imp.succ"),
        InvalidFieldReason::NotFound { full_name: "Function.succ".to_string() }
    );
    // "too many explicit universe levels for `Nat.succ`" — `mkConst
    // constName levels` (App.lean:1875).
    assert!(matches!(
        support::elab_and_synthesize("(Nat.zero).succ.{0}"),
        Err(ElabError::TooManyUniverseLevels(_))
    ));
}

/// Review Focus 1: `findMethod?` computes `S`'s resolution order when
/// `S.f` misses (App.lean:1472-1476). A doctored `parent_info` cycle
/// must surface as an error, not a stack overflow.
#[test]
fn parent_cycle_in_structure_ext_is_an_error_not_a_stack_overflow() {
    // Double every `extends` edge back (Task 2's meta test does the
    // same): `S3`'s order recurses S3 → S2 → S3. `find_field` walks
    // `field_info` subobjects, which are untouched, so `zzz` still
    // misses there and the lookup reaches `findMethod?`'s order.
    let r = support::elab_and_synthesize_doctored("fun (s : S3) => (s).zzz", |ss| {
        let edges: Vec<_> = ss
            .iter()
            .flat_map(|s| {
                s.parent_info
                    .iter()
                    .map(move |p| (p.struct_name, s.struct_name, p.proj_fn))
            })
            .collect();
        for (parent, child, proj_fn) in edges {
            if let Some(p) = ss.iter_mut().find(|s| s.struct_name == parent) {
                p.parent_info.push(leanr_olean::StructureParentInfo {
                    struct_name: child,
                    subobject: false,
                    proj_fn,
                });
            }
        }
    });
    match r {
        Err(ElabError::Internal(m)) => assert!(m.contains("cyclic parents"), "{m}"),
        other => panic!("expected Internal (cyclic parents), got {other:?}"),
    }
}
```

`leanr_olean` is already reachable from this test crate: `elab_and_synthesize_doctored`'s closure takes `&mut Vec<leanr_olean::StructureInfo>`.

Run: `cargo test -p leanr_elab --test lval_smoke 2>&1 | tail -30`
Expected: FAIL. The variants do not exist yet, so compilation fails.

- [ ] **Step 4: Add the error variants**

In `crates/leanr_elab/src/error.rs`, after `InvalidField`:

```rust
    /// oracle: `addLValArg.throwUnusableParameter` (`App.lean:1811-1828`,
    /// thrown at `:1772`): a parameter of the base type exists but can be
    /// passed neither positionally nor by name. `allow_named` is false
    /// once a `CoeFun` coercion has disabled named insertion (`:1785`).
    UnusableLValParameter {
        f: ExprId,
        param: String,
        allow_named: bool,
    },
    /// oracle: `addLValArg`'s final throw (`App.lean:1786-1796`): "Function
    /// … does not have a usable parameter of type `base` …".
    NoLValParameter { f: ExprId, base: String },
```

Both are oracle errors: `is_oracle_error` (`:194-202`) lists only the non-oracle variants, so nothing changes there. Update the `Display`/`Debug` impl if `error.rs` has a hand-written one; match whatever the neighbouring variants do.

- [ ] **Step 5: Implement `find_method` and the `Const` resolution**

In `crates/leanr_elab/src/app/lval.rs`, add the arm to `LValResolution` and update the enum's doc: "`const` since P3; `localRec` needs `auxDeclToFullName` …":

```rust
    /// `App.lean:1444-1446`.
    Const {
        base: NameId,
        struct_name: NameId,
        const_name: NameId,
        levels: Vec<LevelId>,
    },
```

Add:

```rust
/// oracle: `findMethod?` (`App.lean:1453-1477`): try `S.f`, then each
/// namespace after `S` in `S`'s resolution order (a non-structure's is
/// `[S]`). `resolveGlobalName` with `currNamespace := .anonymous` is
/// exact-name lookup in leanr (spec § Seams after P4: `open`/aliases are
/// the `open`/alias slice's), so a candidate list is empty or a
/// singleton and the ambiguity throw (`:1464-1467`) cannot arise; see
/// plan § Spec deviations 1.
fn find_method(
    elab: &mut TermElabM,
    struct_name: NameId,
    field: &str,
) -> Result<Option<(NameId, NameId)>, ElabError> {
    let find = |elab: &mut TermElabM, s: NameId| -> Result<Option<(NameId, NameId)>, ElabError> {
        let s_str = render(elab, s);
        // `privateToUserName structName'` (`:1458`): leanr models no
        // private names (plan § Spec deviations 4).
        if s_str.starts_with("_private.") {
            return Err(ElabError::UnsupportedSyntax(format!(
                "`.{field}` on the private structure `{s_str}` (`privateToUserName`, \
                 App.lean:1458) — the slice that models private names"
            )));
        }
        // `structName' ++ fieldName`: one string component under `s`'s
        // own `NameId`, no render/parse round trip. `base = Some(view
        // store)` so a declared name dedups to its persistent id
        // (`intern_components`' doc says why).
        let base = elab.view.store;
        let store = elab.mctx.store_mut();
        let f = store
            .intern_str(Some(base), field)
            .map_err(MetaError::from)?;
        let full = store
            .name_str(Some(base), Some(s), f)
            .map_err(MetaError::from)?;
        Ok(elab.view.get(full).is_some().then_some((s, full)))
    };
    if let Some(r) = find(elab, struct_name)? {
        return Ok(Some(r));
    }
    let order = if elab.mctx.is_structure(struct_name) {
        elab.mctx
            .get_structure_resolution_order(struct_name)
            .ok_or_else(|| {
                ElabError::Internal(format!(
                    "structure `{}` has cyclic parents in `structureExt` \
                     (getStructureResolutionOrder, Structure.lean:512)",
                    render(elab, struct_name)
                ))
            })?
    } else {
        vec![struct_name]
    };
    for &ns in order.iter().skip(1) {
        if let Some(r) = find(elab, ns)? {
            return Ok(Some(r));
        }
    }
    Ok(None)
}
```

In `resolve_lval_aux`, replace the seam at the end of the structure/`FieldName` arm (`:262-268`):

```rust
            if let Some((base, const_name)) = find_method(elab, s, name)? {
                return Ok(LValResolution::Const {
                    base,
                    struct_name: s,
                    const_name,
                    levels: levels.clone(),
                });
            }
            // `throwInvalidFieldAt ref fieldName fullName` (`:1578`); the
            // exporting-scope `declHint` retry (`:1571-1577`) is prose.
            let full_name = format!("{}.{name}", render(elab, s));
            Err(field_err(name, InvalidFieldReason::NotFound { full_name }))
```

Replace the `Function` seam in the `Forall`/`FieldName` arm (`:271-279`). Bind `levels` in that arm's pattern (`LVal::FieldName { name, levels, .. }`):

```rust
            if elab.view.get(full_id).is_some() {
                // `LValResolution.const `Function `Function fullName levels`
                // (`:1583`).
                let function = crate::app::head::intern_components(elab, &["Function"])?;
                return Ok(LValResolution::Const {
                    base: function,
                    struct_name: function,
                    const_name: full_id,
                    levels: levels.clone(),
                });
            }
```

- [ ] **Step 6: Implement `type_matches_base_name` and `add_lval_arg` (telescope walk only)**

Make `cleanup_annotations` in `builtin/binder/fun.rs:41` `pub(crate)`. It is the oracle's `Expr.cleanupAnnotations` (`Expr.lean:1754`), which `typeMatchesBaseName` also uses (`App.lean:1717`). Then, in `lval.rs`:

```rust
/// oracle: `typeMatchesBaseName` (`App.lean:1712-1726`), under
/// `withReducibleAndInstances` (`TransparencyMode::Instances`).
fn type_matches_base_name(
    elab: &mut TermElabM,
    ty: ExprId,
    base_name: NameId,
) -> Result<bool, ElabError> {
    let is_function = render(elab, base_name) == "Function";
    let cleaned = crate::builtin::binder::fun::cleanup_annotations(elab, ty);
    let store = elab.view.store;
    Ok(elab
        .mctx
        .with_transparency(TransparencyMode::Instances, |m| -> Result<bool, MetaError> {
            let head_is = |m: &MetaCtx, e: ExprId| {
                let mut e = e;
                while let Node::App { f, .. } = m.store().expr_node(Some(store), e) {
                    e = f;
                }
                matches!(m.store().expr_node(Some(store), e), Node::Const { name: Some(n), .. } if n == base_name)
            };
            if is_function {
                let w = m.whnf(ty)?;
                return Ok(matches!(m.store().expr_node(Some(store), w), Node::Forall { .. }));
            }
            if head_is(m, cleaned) {
                return Ok(true);
            }
            let mut cur = ty;
            loop {
                let t = m.whnf_core(cur)?;
                if head_is(m, t) {
                    return Ok(true);
                }
                match m.unfold_definition_pub(t)? {
                    Some(t2) => {
                        // The recursive call re-runs the WHOLE body on
                        // `type'`, including `cleanupAnnotations`
                        // (`:1717`); `whnfCore` below it strips mdata
                        // anyway, so looping on `whnf_core` is the same.
                        cur = t2;
                    }
                    None => return Ok(false),
                }
            }
        })?)
}
```

Check the path: `crate::builtin::binder::fun` may not be a public module path. Use whatever path `fun.rs` is reachable by; if it is private, widen only what is needed, as `pub(crate)`. Import `leanr_meta::{MetaCtx, TransparencyMode}` as the crate already does (`coe.rs` imports `TransparencyMode`).

Also check that `unfold_definition` honours the transparency setting. The rejection `(s).df` and record `p3/reducible-param` pin this. If `unfold_definition` ignores `cfg.transparency`, both would accept, and that is a finding for the task report, not something to paper over.

`add_lval_arg`, with the telescope loop and the final throw. Task 4 inserts the continuations where marked:

```rust
/// oracle: `addLValArg` (`App.lean:1735-1828`): find the first
/// parameter whose type is `base_name …` and insert `e` there —
/// positionally when the parameter is explicit (or `explicit`) and
/// `args` is long enough, else as `(x := e)` unless a parameter of the
/// same name came earlier. Runs under `withoutModifyingState` (`:1737`):
/// the telescope's mvars and any coercion's assignments are rolled back
/// (`MetaCtx::checkpoint`/`rollback`; declarations stay, as the
/// snapshot's doc says, and nothing refers to them).
fn add_lval_arg(
    elab: &mut TermElabM,
    base_name: NameId,
    e: ExprId,
    args: Vec<Arg>,
    named_args: Vec<NamedArg>,
    f: ExprId,
    explicit: bool,
) -> Result<(Vec<Arg>, Vec<NamedArg>), ElabError> {
    let snap = elab.mctx.checkpoint();
    let f_type = elab.mctx.infer_type(f);
    let r = f_type.map_err(ElabError::from).and_then(|f_type| {
        let unusable: Vec<String> = named_args.iter().map(|na| na.name.clone()).collect();
        let remaining: Vec<String> = unusable.clone();
        let st = AddLValArg { base_name, explicit, args: &args };
        add_lval_arg_go(elab, &st, None, f, f_type, 0, remaining, unusable, true, 0)
    });
    elab.mctx.rollback(snap);
    let insert = r?;
    let mut args = args;
    let mut named_args = named_args;
    match insert {
        LValInsert::Positional(idx) => args.insert(idx, Arg::Expr(e)),
        LValInsert::Named(name) => named_args.push(NamedArg {
            name,
            val: Arg::Expr(e),
            num_implicit_params: 0,
        }),
    }
    Ok((args, named_args))
}

/// Where `add_lval_arg_go` decided `e` goes. The oracle returns the
/// updated arrays from inside `go`; deciding inside the rollback scope
/// and editing outside it is the same (`e` and the args predate the
/// checkpoint).
enum LValInsert {
    Positional(usize),
    Named(String),
}

struct AddLValArg<'a> {
    base_name: NameId,
    explicit: bool,
    args: &'a [Arg],
}

/// oracle: `addLValArg.go` (`App.lean:1749-1796`).
#[allow(clippy::too_many_arguments)]
fn add_lval_arg_go(
    elab: &mut TermElabM,
    st: &AddLValArg<'_>,
    f_pre_coercion: Option<ExprId>,
    f: ExprId,
    f_type: ExprId,
    mut arg_idx: usize,
    mut remaining: Vec<String>,
    mut unusable: Vec<String>,
    allow_named: bool,
    depth: usize,
) -> Result<LValInsert, ElabError> {
    let (xs, bis, _f_type2) = elab.mctx.forall_meta_telescope(f_type)?;
    for (&x, &bi) in xs.iter().zip(bis.iter()) {
        let Node::MVar { id: Some(xid) } = node(elab, x) else {
            return Err(ElabError::Internal("forall_meta_telescope minted a non-mvar".into()));
        };
        let decl = elab.mctx.mctx().decl(MVarId(xid)).cloned().ok_or_else(|| {
            ElabError::Internal("forall_meta_telescope mvar is undeclared".into())
        })?;
        let user_name = decl.user_name.map(|n| render(elab, n)).unwrap_or_default();
        let is_explicit = st.explicit || bi == BinderInfo::Default;
        if let Some(i) = remaining.iter().position(|n| *n == user_name) {
            remaining.remove(i);
        } else {
            if type_matches_base_name(elab, decl.ty, st.base_name)? {
                if arg_idx <= st.args.len() && is_explicit {
                    return Ok(LValInsert::Positional(arg_idx));
                }
                if !allow_named || unusable.contains(&user_name) {
                    return Err(ElabError::UnusableLValParameter {
                        f: f_pre_coercion.unwrap_or(f),
                        param: user_name,
                        allow_named,
                    });
                }
                return Ok(LValInsert::Named(user_name));
            }
            if is_explicit {
                arg_idx += 1;
            }
            unusable.push(user_name);
        }
    }
    // Task 4: the `whnf` and `coerceToFunction?` continuations
    // (`:1781-1785`) go here, recursing with `depth + 1`.
    let _ = depth;
    Err(ElabError::NoLValParameter {
        f: f_pre_coercion.unwrap_or(f),
        base: render(elab, st.base_name),
    })
}
```

Before relying on that code, check three points against the oracle:
1. **`bInfo.isExplicit`** (`:1764`, `:1775`) is `BinderInfo::Default` only. Check `BinderInfo`'s variants in `leanr_kernel` and match the oracle's `isExplicit`.
2. **The `if let some idx := remainingNamedArgs.findFinIdx?` arm** (`:1756-1758`) skips both the `argIdx` advance and the `unusableNamedArgs.push`. The code above does the same.
3. **Anonymous binder names.** The oracle compares `Name`s; leanr compares rendered strings. A `None` user name renders as `""`, which no user-written named argument can equal. That preserves the oracle's behaviour: an anonymous binder's name is `.anonymous`, never user-writable.

Both error sites pass `f_pre_coercion.unwrap_or(f)`, which is the function the user named (`S1.viaFnI`, not `FnI.f S1.viaFnI`). The oracle's message mentions both (`funMsg`, `:1797-1809`), but leanr does not port the prose (spec § Errors), and the head the user wrote is the one worth carrying. Say so in both variants' docs.

- [ ] **Step 7: The `Const` arm of `elab_app_lvals`**

In `elab_app_lvals`'s `match res`, add:

```rust
            // `App.lean:1873-1884`.
            LValResolution::Const {
                base,
                struct_name,
                const_name,
                levels,
            } => {
                let e = if base != struct_name {
                    mk_base_projections(elab, base, struct_name, e)?
                } else {
                    e
                };
                let display = render(elab, const_name);
                // `mkConst constName levels` (`:1875`). `find_method` and the
                // `Function` arm only return declared constants.
                let proj_fn = crate::app::head::mk_const(elab, const_name, &levels, &display)?;
                if last {
                    let args = std::mem::take(&mut call.args);
                    let named = std::mem::take(&mut call.named_args);
                    let (args, named) =
                        add_lval_arg(elab, base, e, args, named, proj_fn, call.explicit)?;
                    call.args = args;
                    call.named_args = named;
                    return crate::app::elab_app_args(elab, proj_fn, call, kinds);
                }
                // Non-final (`:1881-1884`): no outer arguments, `explicit :=
                // false`, no expected type.
                let (args, named_args) =
                    add_lval_arg(elab, base, e, Vec::new(), Vec::new(), proj_fn, false)?;
                let step = AppCall {
                    named_args,
                    args,
                    expected: None,
                    explicit: false,
                    ellipsis: false,
                    stx: call.stx.clone(),
                };
                f = crate::app::elab_app_args(elab, proj_fn, step, kinds)?;
            }
```

Update `elab_app_lvals`'s doc to mention the `const` arm next to `projFn`.

- [ ] **Step 8: Run everything touched**

Run: `cargo test -p leanr_elab 2>&1 | tail -40`
Expected: PASS: `oracle_elab_gate` with all 230 records, and `lval_smoke`. If a `p3/*` record fails, apply § Decisions taken while planning. First show that the cause is not P3's own code: a P3 bug is fixed here, never dropped.

- [ ] **Step 9: Show the tests discriminate**

Apply each mutation, run `cargo test -p leanr_elab --test oracle_elab --test lval_smoke 2>&1 | tail -30`, confirm red, and revert:
- **F:** `find_method` skips the resolution-order loop (`return Ok(None)` after the first `find`). `p3/inherited-method`, `p3/c3-*`, `p3/param-base` go red.
- **G:** iterate `order` in reverse. `p3/c3-order` must pick `OE.k` and go red. `p3/c3-first` also changes.
- **H:** in the `Const` arm, drop `mk_base_projections` (always `e`). `p3/inherited-method` goes red.
- **I:** in `add_lval_arg_go`, always return `Positional(arg_idx)` when the type matches. `p3/named-eta` and `p3/implicit-named` go red.
- **J:** drop `st.explicit ||` from `is_explicit`. `p3/explicit-positional` goes red.
- **K:** remove the `remaining` check (never `remove`, always fall to the type test). `(s).addTo (s := s)` goes red.
- **L:** run `type_matches_base_name` without `with_transparency` (at the ambient default). The `(s).df` rejection goes red.
- **M:** in `resolve_lval_loop`, return the ORIGINAL error rather than retrying. The `S3Alias` `.zzz` assertion (`S3.zzz`) and `p3/alias-field` go red.
- **N:** in the non-final `Const` step, pass `true` instead of `false` as `add_lval_arg`'s `explicit`. The `(s).imp.succ` assertion goes red: `s` is inserted positionally, lands on `n : Nat`, and the error is no longer `NotFound Function.succ`.

Record every command and outcome.

- [ ] **Step 10: Commit**

```bash
git add crates/leanr_elab tests/fixtures/elab/dump_elab.lean tests/fixtures/elab/elab-queries.jsonl
git commit -m "M4b-4a P3: findMethod?, LValResolution.const and addLValArg"
```

---

### Task 4: `add_lval_arg`'s continuations — `whnf`, `coerceToFunction?`, recursion depth

**Files:**
- Modify: `crates/leanr_elab/src/error.rs` (`MaxRecDepth`)
- Modify: `crates/leanr_elab/src/app/lval.rs` (`add_lval_arg_go`)
- Modify: `crates/leanr_elab/tests/lval_smoke.rs`
- Modify: `tests/fixtures/elab/dump_elab.lean`, `elab-queries.jsonl`, `crates/leanr_elab/tests/oracle_elab.rs`

**Interfaces:**
- Consumes (Task 3): `add_lval_arg_go`'s signature, including `f_pre_coercion`, `allow_named` and `depth`.
- Consumes (`leanr_meta`): `MetaCtx::whnf`, `MetaCtx::coerce_to_function(e) -> Result<Option<ExprId>, MetaError>` (`coe.rs:129`), `MetaCtx::infer_type`.
- Produces: `ElabError::MaxRecDepth`.

- [ ] **Step 1: Write the failing records and tests**

Add to `p3Queries` in `dump_elab.lean`:

```lean
  , ("p3/whnf-continuation",   "fun (s : S1) => (s).viaDef")
  , ("p3/coe-fun",             "fun (s : S1) => (s).viaFn")
  , ("p3/whnf-then-named",     "fun (s : S1) => (s).viaDef3")
```

Regenerate. Expect 233 lines, with the `grep '^-[^-]'` check printing nothing. Raise `oracle_elab.rs`'s floor to 233 with the comment `// 230 -> 233 (M4b-4a P3 task 4): p3/whnf-continuation, p3/coe-fun, p3/whnf-then-named.`

Append to `lval_smoke.rs`:

```rust
/// `addLValArg` after a `CoeFun` coercion (App.lean:1784-1785):
/// `allowNamed := false`. "Invalid field notation: `FnI.f` (coerced
/// from `S1.viaFnI`) has a parameter with expected type S1 but it
/// cannot be used. Note: Field notation cannot refer to parameter `s`
/// by name because that constant was coerced to a function"
#[test]
fn coerced_implicit_lval_parameter_is_unusable() {
    match support::elab_and_synthesize("fun (s : S1) => (s).viaFnI") {
        Err(ElabError::UnusableLValParameter { param, allow_named, .. }) => {
            assert_eq!(param, "s");
            assert!(!allow_named);
        }
        other => panic!("expected UnusableLValParameter, got {other:?}"),
    }
}

/// Review Focus 2: `Loop` coerces to `{u : Nat} → Loop` forever;
/// `addLValArg.go`'s `withIncRecDepth` (App.lean:1749) stops it.
/// "maximum recursion depth has been reached"
#[test]
fn self_reproducing_coe_fun_hits_max_rec_depth() {
    assert!(matches!(
        support::elab_and_synthesize("fun (s : S1) => (s).loop"),
        Err(ElabError::MaxRecDepth)
    ));
}
```

Run: `cargo test -p leanr_elab --test oracle_elab --test lval_smoke 2>&1 | tail -30`
Expected:
- FAIL to compile (`MaxRecDepth` does not exist yet).
- After Step 2 adds the variant: the three new records fail with `NoLValParameter`, and so do `viaFnI` and `loop`.

- [ ] **Step 2: Add `MaxRecDepth`**

In `error.rs`:

```rust
    /// oracle: `throwMaxRecDepthAt` (`Exception.lean:226`), reached from
    /// `withIncRecDepth` (`:245`) — an ordinary `.error`. leanr counts
    /// only the recursion that can run away on its own
    /// (`addLValArg.go`, `App.lean:1749`) against the oracle's
    /// `defaultMaxRecDepth` (512, `Init/Prelude.lean:4836`); the oracle
    /// counts from the ambient depth, so the exact cut-off differs,
    /// never whether one exists.
    MaxRecDepth,
```

- [ ] **Step 3: Implement the continuations**

Replace the Task 3 placeholder in `add_lval_arg_go` (the `// Task 4` comment and the `let _ = …` line) with:

```rust
    // `withIncRecDepth` (`:1749`).
    const MAX_REC_DEPTH: usize = 512;
    // `if allowNamed || argIdx ≤ args.size then` (`:1781`).
    if allow_named || arg_idx <= st.args.len() {
        let f_app = xs.iter().try_fold(f, |acc, &x| mk_app(elab, acc, x))?;
        let w = elab.mctx.whnf(_f_type2)?;
        if matches!(node(elab, w), Node::Forall { .. }) {
            if depth + 1 >= MAX_REC_DEPTH {
                return Err(ElabError::MaxRecDepth);
            }
            // `:1782-1783`.
            return add_lval_arg_go(
                elab, st, f_pre_coercion, f_app, w, arg_idx, remaining, unusable, allow_named,
                depth + 1,
            );
        }
        if let Some(f2) = elab.mctx.coerce_to_function(f_app)? {
            if depth + 1 >= MAX_REC_DEPTH {
                return Err(ElabError::MaxRecDepth);
            }
            // `:1784-1785`: `fPreCoercion?.getD f`, named insertion off.
            let f2_type = elab.mctx.infer_type(f2)?;
            return add_lval_arg_go(
                elab,
                st,
                Some(f_pre_coercion.unwrap_or(f)),
                f2,
                f2_type,
                arg_idx,
                remaining,
                unusable,
                false,
                depth + 1,
            );
        }
    }
```

Rename `_f_type2` to `f_type2` now that it is used, and delete Task 3's `let _ = depth;` line.

One check against the oracle:
- **The `whnf` of `f_type2`.** It runs at the ambient transparency (the elaborator's default), as `:1782` does: `addLValArg` is in `MetaM` with no transparency wrapper. Do not reuse `type_matches_base_name`'s `Instances` setting here.

- [ ] **Step 4: Run**

Run: `cargo test -p leanr_elab 2>&1 | tail -40`
Expected: PASS, with 233 records.

If `p3/coe-fun` fails in `elab_app_args` rather than in `add_lval_arg` (for example `FunctionExpected` on `S1.viaFn s`), the head coercion is `synthesizePendingAndNormalizeFunType`'s (`App.lean:378-380`), which leanr already has (the `Fn` fixture). Find the divergence before dropping anything; it is not the `numScopeArgs` gap.

- [ ] **Step 5: Show the tests discriminate**

Apply, run the Step 4 command, confirm red, and revert:
- **O:** delete the `whnf` branch. `p3/whnf-continuation` goes red.
- **P:** delete the `coerce_to_function` branch. `p3/coe-fun` and `coerced_implicit_lval_parameter_is_unusable` go red.
- **Q:** pass `allow_named` instead of `false` in the coercion recursion. The `viaFnI` test goes red: the value would be inserted by name, so either the term elaborates or `allow_named` is true.
- **R:** remove both `MAX_REC_DEPTH` checks. `self_reproducing_coe_fun_hits_max_rec_depth` must go red. That can mean `StepBudgetExhausted` or `DepthBudgetExhausted` from `leanr_meta`, or a hang, so run with `timeout 300`. Record which. If a meta budget error fires, the test stays as written: the oracle's answer is `MaxRecDepth`, and an exhausted budget is "never answered", not a rejection.
- **S:** change the guard to `allow_named && arg_idx <= st.args.len()`. `p3/whnf-then-named` goes red: after `S1.viaDef3`'s explicit `n`, `arg_idx = 1 > 0`, so `&&` stops before the `whnf` continuation and reports `NoLValParameter`.

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_elab tests/fixtures/elab
git commit -m "M4b-4a P3: addLValArg's whnf and CoeFun continuations, recursion depth"
```

---

### Task 5: Reconcile seams and docs, record the slice

**Files:**
- Modify: `crates/leanr_elab/src/dispatch.rs:166-170` (deferral table)
- Modify: `crates/leanr_elab/src/app/mod.rs:65-69` (seam index)
- Modify: `crates/leanr_elab/src/app/lval.rs` (module doc, `LValResolution` doc)
- Modify: `crates/leanr_elab/tests/seam_audit.rs:760-780` (needle)
- Modify: `docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md` (§ P3 amendments, § Landed › P3)

- [ ] **Step 1: Find every remaining reference**

Run: `grep -rn "M4b-4a P3" crates/ docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md`
Expected: only the documentation rows below, and no live (non-comment) source line. If a live line remains, it is a seam this plan missed. Stop and report it.

- [ ] **Step 2: Update the tables**

- `dispatch.rs`: change the `generalized field notation (.const, Function.f) … M4b-4a P3` row to `… P3 SHIPPED (M4b-4a) — lval.rs`, in the style of the neighbouring shipped rows.
- `app/mod.rs:67`: `generalized field notation (.const, Function.f) .. P3 SHIPPED (M4b-4a) — lval.rs`.
- In `lval.rs`'s `LValResolution` doc, name `localRec` as the only unported arm.

- [ ] **Step 3: Add the needle and show it is not vacuous**

In `seam_audit.rs`'s `no_seam_message_names_a_completed_slice`, append `"M4b-4a P3"` to `needles` and update the assertion message to "… and M4b-4a P1, P2, P3 are complete …". Extend the doc comment in the existing style: "**`M4b-4a P3` was added by M4b-4a P3 task 5, and measured non-vacuous.** …".

Measure it:
1. Add a live line `let _ = "M4b-4a P3";` to `lval.rs`.
2. Run `cargo test -p leanr_elab --test seam_audit no_seam_message_names_a_completed_slice`. It must fail, naming that line.
3. Remove the line and run it again. It must pass.
Record both runs.

- [ ] **Step 4: Record the slice in the spec**

In `docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md`:

1. Under § Next, after the P2 amendments, add **"P3 amendments (found while planning, measured)"** with this plan's five § Spec deviations, one bullet each, with their citations.
2. Under § Landed, add `### P3 — generalized field notation (PR #<n>)`:
   - what landed: C3 order, `forall_meta_telescope`, `find_method`, the `Const` arms, `type_matches_base_name`, and `add_lval_arg` with both continuations and the depth cap;
   - the corpus: 25 `p3/*` records;
   - where the rejections live: `lval_smoke.rs`;
   - that the P1 debt is closed: `fun (s : S3Alias) => (s).a` is `p3/alias-field`, and the `S3Alias` `.zzz` rejection now names `S3.zzz`;
   - open follow-ups: every term dropped under § Decisions taken while planning, with its leanr error and the confirming command, and any mutation that could not be made to discriminate, with the reason.
   - Leave the PR number as `#<n>` until the PR exists. The finishing step fills it in before merge, and it must not merge as a placeholder.

- [ ] **Step 5: Full CI, blocking**

Run: `mise run ci; echo CI_EXIT=$?`
Run it in the foreground and wait for `CI_EXIT`. Expected: `CI_EXIT=0`. fmt and clippy failures count; fix them and re-run.

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_elab docs/superpowers/specs/2026-09-29-m4b4-dot-notation-design.md
git commit -m "M4b-4a P3: reconcile seams, record the slice"
```
