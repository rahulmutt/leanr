# M4b-4c P2 — `ElabElim` — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Elaborate eliminator-headed applications exactly as the
pinned oracle does. This covers:

- the `elabAsElim?` gate
- the `elabAppArgs` diversion
- `ElabElim.main` / `finalize` / `revertArgs` / `mkMotive`

It also removes the M4b-4c recursor seams and lifts the corpus ban on
eliminator queries. When this lands, M4b-4 is complete.

**Architecture:** Two new `leanr_meta` capabilities are added, both
additive:

- `check` / `is_type_correct`, a port of `Meta/Check.lean`. The
  existing `is_type_correct` is only an `infer_type` proxy.
- `with_full_approx_def_eq` and `transform_used_let_only`.

`leanr_elab` gains `app/elim.rs`, which holds the gate (`elab_as_elim_info`)
and a separate `ElimElab` machine. `elab_app_args` diverts to that
machine at the oracle's point. Three behavior-neutral extractions
let `ElimElab` reuse `AppElab`'s helpers without sharing its state.

New elab-corpus records pin every success shape and every error
message. Error records are a new record kind, `{"id","src","err"}`.

**Tech Stack:** Rust (`leanr_meta`, `leanr_elab`), Lean 4 oracle
dumpers at `leanprover/lean4:v4.33.0-rc1`, `mise` tasks.

**Spec:** `docs/superpowers/specs/2026-10-01-m4b4c-elab-as-elim-design.md`.
Before starting, read:

- § Evidence and § Decisions
- every `### P2 —` section, plus § Errors, § Fixture and § Testing › P2
- § Landed › P1

The previous plan, `docs/superpowers/plans/2026-10-01-m4b4c-p1-elim-substrate.md`,
shows the house style for oracle dumpers and gates.

## Global Constraints

- Oracle pin: `leanprover/lean4:v4.33.0-rc1`. Never bump it.
- Correctness is differential against the oracle. Every expected value
  in an oracle gate is **dumped by the oracle, never hand-computed**.
  Unit tests may assert values this plan quotes from an oracle run.
- The kernel is untouched. Nothing in this plan edits
  `crates/leanr_kernel`.
- `leanr_meta` changes must be additive and behavior-neutral (the
  accessor precedent). No existing caller's behavior may change. Every
  `oracle_fast` / `oracle_synth` record must stay green.
- `leanr_elab` refactors in Task 3 are behavior-neutral. The full elab
  corpus must stay green, and `git diff tests/fixtures` must be empty.
- Build under `/workspace`, never `/tmp`. `/tmp` is a 20Gi EmptyDir.
- Run `lean` from a directory under `/workspace`. elan resolves the
  toolchain from `lean-toolchain`, and outside the repo it fails with
  "no default toolchain".
- Do **not** run `mise run fixtures:regen`, because it also runs the
  Mathlib steps. Run only the individual commands this plan names.
- Before every commit, run `cargo fmt --all` and
  `cargo clippy --workspace --all-targets -- -D warnings`. CI's
  `mise run ci` gates on both.
- Comments that cite oracle lines (`App.lean:NNNN`) must be checked
  against the v4.33.0-rc1 source at
  `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/` before
  they are committed. Earlier citations have been off by 1-2 lines.
  The ranges this plan uses were opened while writing it:
  - `ElabElim`: `App.lean:1140-1319`
  - `mkMotive`: `:1167-1173`
  - `revertArgs`: `:1179-1190`
  - `finalize`: `:1196-1240`
  - `getNextArg?`: `:1247-1260`
  - `elabArg`: `:1267-1272`
  - `mkImplicitArg`: `:1280-1284`
  - `main`: `:1286-1317`
  - `shouldElabAsElim`: `:1322-1328`
  - diversion: `:1373-1383`
  - `elabAsElim?`: `:1397-1431`
  - `Check.lean` `checkAux`: `:288-329`
  - `check`: `:331-338`
  - `isTypeCorrect`: `:365-370`
  - `fullApproxDefEq`: `Basic.lean:2094-2105`

## Review Focus

Each of these is a corpus record added in Task 6 Step 1, and each was
measured on the oracle while this plan was written:

1. **An eliminator reached through generalized field notation**,
   `fun (h : False) => (h.rec : Nat)`. The motive is explicit, and
   `addLValArg` passes `h` as the **named** argument `t`, because the
   positional slot is past `args.size`. The gate must therefore not
   depend on `lvals.is_empty()`. Record `elim/hRec`, plus `elim/hRecArg`
   in argument position.
2. **An over-applied eliminator whose extra argument postpones**
   (`… n (sameAs Nat.zero Nat.zero)`). `revertArgs` elaborates it with
   no expected type, right to left, and then `kabstract`s the value.
   Record `elim/overPostponed`.
3. **An eliminator head with explicit universes** (`Nat.rec.{1} …`).
   It is still a `.const`, so the gate applies. Record `elim/univ`.
4. **An eliminator in argument position**, whose expected type comes
   from the outer application's binder (`Nat.succ (Nat.rec …)`).
   Record `elim/argPos`.
5. **A discriminant whose type carries an unused `let`.** The motive
   binder drops it (`usedLetOnly := true`); a *used* `let` is kept.
   Records `elim/letDiscr`, `elim/letDiscrUsed` and `elim/letOver`.

## Spec corrections found while planning

Record these under the spec's § Landed › P2 (Task 7):

- **`elab_app_fn_id`'s `heed` is deleted, not kept.** The oracle's
  `heedElabAsElim` is a `TermElabM` reader field. Only the `induction`
  tactic clears it (`Tactic/Induction.lean:806`), so in term
  elaboration it is always `true`. The leanr `heed` also tested
  `lvals.is_empty() && n_fields == 0`, which existed only to place the
  seam. Keeping it would send `h.rec` (an LVal) down the ordinary path.
  The gate now lives entirely in `elab_app_args`, on the final head.
- **No `registerMVarArgName` table.** Its only reader is the oracle's
  error prose, which leanr defers. `args.rs`'s `mk_inst_mvar` already
  established the precedent of dropping the name. `save_arg_info` is
  documented and left out.
- **`mkFreshBinderName` need not match the oracle byte for byte.** The
  canonical encoder erases binder names (`dump_elab.lean`'s module doc),
  so `Elab::mk_fresh_binder_name` is used as is.
- **`isTypeCorrect` needed a real `Meta.check`.** leanr's
  `is_type_correct` (`assign.rs:664`) is an `infer_type` proxy, and
  `infer_type` does not check argument types. Both
  `isTypeCorrect`-driven errors (`elimErr/motiveIncorrect` and
  `elimErr/overAppIncorrect`) are well-typed under `infer_type` and
  rejected by `check`. Task 2 ports `check`. The old proxy keeps its
  behavior under a new name, `infer_type_succeeds`, and is recorded as
  a follow-up: route `assign.rs`'s `quasiPatternApprox` caller through
  the real `check`.
- **The elab corpus had no error records.** `dump_elab.lean` drops a
  throwing query. Task 6 adds an `err` record kind for an
  `elimErrQueries` list only, so every existing list keeps its drop
  behavior. The oracle logs elaboration errors through `errToSorry` and
  then aborts with `internal exception #3`, so the record carries the
  first line of the **first logged message**.
- **New fixture declaration `preElim`.** "insufficient number of
  arguments" (no motive yet) needs an explicit binder **before** the
  motive, and no existing fixture eliminator has one. It is an axiom:
  `@[elab_as_elim] axiom preElim (k : Nat) {motive : Nat → Prop}
  (z : motive Nat.zero) (n : Nat) : motive n`. `@[elab_as_elim]` was
  measured to accept an axiom.
- **`kabstract` fvar/mvar oracle records stay deferred.** The P1
  follow-up asked for them. The elab corpus now pins the fvar fast
  path end to end (every `elim/*` query with a bound major). No P2
  caller passes an mvar pattern in the common case (discriminants are
  `instantiateMVars`'d and assigned by `finalize`), but two paths do:
  `revert_args` passes a postponed synthetic mvar to `kabstract`
  (exercised trivially by `elim/overPostponed`), and `mk_motive` would
  for a `_` major. Task 1 adds the `mdata` fast-path
  unit test. The mvar record stays a follow-up.

## File map

| File | Change | Responsibility |
|---|---|---|
| `crates/leanr_meta/src/metactx.rs` | modify | `with_full_approx_def_eq` |
| `crates/leanr_meta/src/transform.rs` | modify | `transform_used_let_only` |
| `crates/leanr_meta/src/kabstract.rs` | modify | `mdata` fast-path unit test |
| `crates/leanr_meta/tests/aux_recursor_oracle.rs` | modify | Num-aware name decode |
| `crates/leanr_meta/src/check.rs` | create | `check`, `is_type_correct` |
| `crates/leanr_meta/src/assign.rs` | modify | rename the proxy to `infer_type_succeeds` |
| `crates/leanr_meta/src/lib.rs` | modify | `mod check;` |
| `crates/leanr_elab/src/app/state.rs` | modify | `TelescopeBinder::bi`, free `whnf_forall`, `open_forall_telescope`, `TermElabM::synthesize_app_inst_mvars_of` |
| `crates/leanr_elab/src/elab.rs` | modify | `mk_const_with_fresh_mvar_levels_of` becomes `pub` |
| `crates/leanr_elab/src/error.rs` | modify | new `EliminatorErrorReason` arms, `oracle_first_line` |
| `crates/leanr_elab/src/app/elim.rs` | create | `should_elab_as_elim`, `elab_as_elim_info`, `ElimElab` |
| `crates/leanr_elab/src/app/mod.rs` | modify | `pub mod elim;`, the diversion, doc table |
| `crates/leanr_elab/src/app/head.rs` | modify | delete both seams and `recursor_head_seam` |
| `crates/leanr_elab/src/dispatch.rs`, `src/lib.rs` | modify | doc rows |
| `crates/leanr_elab/tests/elim_smoke.rs` | create | gate unit tests, postpone tests |
| `crates/leanr_elab/tests/oracle_elab.rs` | modify | the `err` record branch, corpus floor |
| `crates/leanr_elab/tests/seam_audit.rs` | modify | rows flip, query ban lifted, `M4b-4c` needle |
| `crates/leanr_elab/tests/postpone_smoke.rs` | modify | repoint the seam-propagation test |
| `crates/leanr_olean/src/module_data.rs` | modify | `elab_as_elim` golden gains `preElim` |
| `tests/fixtures/elab/Elab0.lean` (+ `.olean`) | modify | `preElim` |
| `tests/fixtures/elab/dump_elab.lean` | modify | `elimQueries`, `elimErrQueries`, `emitErr` |
| `tests/fixtures/elab/elab-queries.jsonl`, `elim.jsonl` | regen | |

---

### Task 1: leanr_meta: approximation scope, `usedLetOnly`, and P1 follow-ups

**Files:**
- Modify: `crates/leanr_meta/src/metactx.rs`, next to `with_transparency`
  (`:494-505`)
- Modify: `crates/leanr_meta/src/transform.rs`
- Modify: `crates/leanr_meta/src/kabstract.rs` (tests module)
- Modify: `crates/leanr_meta/tests/aux_recursor_oracle.rs:28`

**Interfaces:**
- Produces: `pub fn MetaCtx::with_full_approx_def_eq<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R`
- Produces: `pub fn MetaCtx::transform_used_let_only(&mut self, input: ExprId) -> Result<ExprId, MetaError>`.
  This is `Meta.transform (usedLetOnly := true)` with the default
  `pre`/`post`.

- [ ] **Step 1: Write the failing tests.**

  In `metactx.rs`'s test module, add a test built on the oracle's
  `constApprox` row of `dump_defeq.lean`:
  `?m N.zero =?= N.succ (N.succ N.zero)`, with `?m : N → N`. It is
  `false` by default and `true` under full approximation, because
  `processConstApprox` assigns `?m := fun _ => N.succ (N.succ N.zero)`.

```rust
    #[test]
    fn full_approx_enables_const_approx_and_restores() {
        use crate::test_support::{app, c, fresh_mvar, with_meta0_ctx};
        with_meta0_ctx(|ctx| {
            let n = c(ctx, "N");
            let base = Some(ctx.view.store);
            let n_to_n = ctx
                .scratch
                .expr_forall(base, None, n, n, leanr_kernel::BinderInfo::Default)
                .unwrap();
            let zero = c(ctx, "N.zero");
            let succ = c(ctx, "N.succ");
            let one = app(ctx, succ, zero);
            let two = app(ctx, succ, one);

            let (m1, _) = fresh_mvar(ctx, n_to_n);
            let lhs1 = app(ctx, m1, zero);
            assert!(!ctx.is_def_eq(lhs1, two).unwrap(), "default config: no constApprox");

            let (m2, _) = fresh_mvar(ctx, n_to_n);
            let lhs2 = app(ctx, m2, zero);
            let before = ctx.cfg();
            assert!(ctx.with_full_approx_def_eq(|ctx| ctx.is_def_eq(lhs2, two)).unwrap());
            assert_eq!(ctx.cfg(), before, "the scope restores the config");
        });
    }
```

  If `Config` does not derive `PartialEq`, compare the four flags
  individually instead.

  In `transform.rs`'s test module:

```rust
    /// oracle: `transform (usedLetOnly := true)` rebuilds lets with
    /// `mkLetFVars (usedLetOnly := true)`, which drops a let whose
    /// variable the body does not mention (measured end to end:
    /// `elim/letDiscr` vs `elim/letDiscrUsed`).
    #[test]
    fn used_let_only_drops_unused_lets_and_keeps_used_ones() {
        use crate::test_support::{bvar, c, with_meta0_ctx};
        with_meta0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let n = c(ctx, "N");
            let zero = c(ctx, "N.zero");
            let succ = c(ctx, "N.succ");
            // let y : N := N.zero; N
            let unused = ctx.scratch.expr_let(base, None, n, zero, n, false).unwrap();
            assert_eq!(ctx.transform_used_let_only(unused).unwrap(), n);
            let mut noop = |_: &mut MetaCtx, _| Ok(TransformStep::Continue(None));
            assert_eq!(ctx.transform(unused, &mut noop).unwrap(), unused, "flag off: kept");
            // let y : N := N.zero; N.succ y
            let b0 = bvar(ctx, 0);
            let body = ctx.scratch.expr_app(base, succ, b0).unwrap();
            let used = ctx.scratch.expr_let(base, None, n, zero, body, false).unwrap();
            assert_eq!(ctx.transform_used_let_only(used).unwrap(), used);
        });
    }
```

  In `kabstract.rs`'s test module, add the P1 follow-up. The fvar fast
  path is plain `abstract`, which keeps an `mdata` wrapper. P1 measured
  that the general path would instead abstract the whole `mdata x`.

```rust
    /// P1 follow-up: the fvar fast path is `abstract`, which keeps an
    /// `mdata` wrapper, so `N.succ (mdata x)` gives `N.succ (mdata #0)`.
    /// The general path would have abstracted the whole `mdata x` to `#0`.
    #[test]
    fn kabstract_fvar_fast_path_keeps_mdata() {
        with_meta0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let n = c(ctx, "N");
            let x = fresh_fvar(ctx, n, "x");
            let kv = ctx
                .scratch
                .intern_kvmap(base, &leanr_kernel::KVMap::default())
                .unwrap();
            let md_x = ctx.scratch.expr_mdata(base, kv, x).unwrap();
            let succ = c(ctx, "N.succ");
            let e = app(ctx, succ, md_x);
            let r = ctx.kabstract(e, x).unwrap();
            let b0 = bvar(ctx, 0);
            let md_b0 = ctx.scratch.expr_mdata(base, kv, b0).unwrap();
            assert_eq!(r, app(ctx, succ, md_b0));
        });
    }
```

  If `KVMap` is not re-exported at `leanr_kernel::KVMap`, use the path
  that `grep -rn "pub struct KVMap" crates/leanr_kernel/src` gives.

- [ ] **Step 2: Run them and watch them fail.**

  Run: `cargo test -p leanr_meta full_approx_enables used_let_only_drops kabstract_fvar_fast_path_keeps_mdata`

  Expected:
  - the first two fail to compile (no such method);
  - the `mdata` test **passes** at once, because it pins current
    behavior. Check that it can fail by temporarily removing the fvar
    fast path. It must go red; then revert.

- [ ] **Step 3: Implement `with_full_approx_def_eq`.**

```rust
    /// oracle: `fullApproxDefEq` (`Basic.lean:2094-2105`): `withConfig`
    /// setting `foApprox`, `ctxApprox`, `quasiPatternApprox` and
    /// `constApprox`. Additive. The defeq cache key is derived from the
    /// whole `Config` (`config.rs` module doc), so results computed
    /// under the scope never leak into the default-config cache. The
    /// whole config is restored, as `withConfig` (a `withReader`) does.
    pub fn with_full_approx_def_eq<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        let saved = self.cfg;
        self.cfg.fo_approx = true;
        self.cfg.ctx_approx = true;
        self.cfg.quasi_pattern_approx = true;
        self.cfg.const_approx = true;
        let r = f(self);
        self.cfg = saved;
        r
    }
```

  (If `Config` is `Clone` but not `Copy`, use `self.cfg.clone()`.)

- [ ] **Step 4: Implement `transform_used_let_only`.** Thread a flag
  through the traversal. Replace the `cache: &mut Cache` parameter of
  `transform_visit` and its helpers with `st: &mut TransformSt`, where:

```rust
struct TransformSt {
    cache: Cache,
    /// oracle: `transform`'s `usedLetOnly` argument (`Transform.lean:183`),
    /// forwarded to every `mkLetFVars` / `mkLambdaFVars` / `mkForallFVars`
    /// of the rebuild. Only the `letE` rebuild can observe it: a lambda or
    /// forall telescope binds no let-decls.
    used_let_only: bool,
}
```

  `transform` builds `TransformSt { cache: HashMap::new(), used_let_only: false }`.
  The new method does the same with `true` and a `pre` that always
  returns `TransformStep::Continue(None)`. In `transform_let`'s rebuild
  loop:

```rust
                    for (x, non_dep) in lets.iter().rev() {
                        let rebuilt = self.mk_let_expr(*x, b, *non_dep)?;
                        // oracle: `mkLetFVars (usedLetOnly := true)` keeps a let
                        // only if the abstracted body mentions it (`hasLooseBVar 0`).
                        if st.used_let_only {
                            if let Node::LetE { body, .. } = self.node(rebuilt) {
                                if !self.has_loose_bvar(body, 0)? {
                                    continue;
                                }
                            }
                        }
                        b = rebuilt;
                    }
```

  With `used_let_only == false` the code path is unchanged, so this is
  behavior-neutral for `coe.rs::expand_coe`. Update the module doc's
  "every flag at its default" sentence to name the new entry point.

- [ ] **Step 5: Num-aware names in `aux_recursor_oracle.rs`.** P1
  follow-up: `decode_name` has no numeric components, so the
  `_private.Elab0.0.*` records resolve to a different `NameId`. Add a
  local helper with the same logic as `leanr_elab`'s
  `tests/support/mod.rs::name_id` (`:826-845`). For each `.`-separated
  part:
  - a part that parses as `u64` → `intern_nat` + `name_num`;
  - otherwise → `intern_str` + `name_str`.

  Use it on line 28 in place of `decode_name`.

- [ ] **Step 6: Run the tests and watch them pass.**

  Run: `cargo test -p leanr_meta`

  Expected: all green, including `oracle_fast`, `oracle_synth` and
  `aux_recursor_oracle`.

- [ ] **Step 7: Commit.**

```bash
cargo fmt --all && cargo clippy --workspace --all-targets -- -D warnings
git add crates/leanr_meta
git commit -m "M4b-4c P2: full-approx defeq scope, transform usedLetOnly, P1 meta follow-ups"
```

---

### Task 2: leanr_meta: `check` and `is_type_correct`

**Files:**
- Create: `crates/leanr_meta/src/check.rs`
- Modify: `crates/leanr_meta/src/lib.rs` (`mod check;`)
- Modify: `crates/leanr_meta/src/assign.rs:415`, `:650-666`. Rename the
  proxy to `infer_type_succeeds`; its body and doc stay, plus a
  follow-up note.

**Interfaces:**
- Produces: `pub fn MetaCtx::check(&mut self, e: ExprId) -> Result<(), MetaError>`
- Produces: `pub fn MetaCtx::is_type_correct(&mut self, e: ExprId) -> Result<bool, MetaError>`
- Produces: `MetaError::Check(String)`, the variant for `check`'s own
  throws. Add it to `crates/leanr_meta/src/error.rs` with a doc line.

**What the oracle does** (`Check.lean:288-338`, `:365-370`): under
`withTransparency .all`, it does a cached structural walk.

- `forallE`: open the telescope (non-reducing). For each binder,
  `ensureType` its type (`getLevel`: the type's type whnfs to a
  `Sort`) and `check` it. Then `ensureType` and `check` the body.
- `lam` / `letE`: `lambdaLetTelescope`. Per binder:
  - a cdecl gets `ensureType` + `check` on its type;
  - an ldecl also gets: `inferType v` defeq to `t`, else throw; then
    `check v`.

  Then `check` the body.
- `const c us`: the level count must equal the declaration's
  `levelParams` length.
- `app f a`: `check f`, `check a`, then `checkApp`. That is: the
  `whnf` of `inferType f` must be a `forallE` whose domain is `isDefEq`
  to `inferType a`. Otherwise throw.
- `mdata`: check the inner term.
- `proj s i e`: `check e`. Then if the struct type is a `Prop` and the
  projection's type is not, throw.
- everything else: OK.

`isTypeCorrect` is `try check e; true catch _ => false`. It has **no
rollback**: mvar assignments made by `isDefEq` inside `check` persist,
exactly as in the oracle.

- [ ] **Step 1: Write the failing tests** in `check.rs`'s test module,
  on Meta0. Each one is chosen so that the old proxy and `check`
  disagree, or so that it pins a side effect.

```rust
#[cfg(test)]
mod tests {
    use crate::test_support::{app, c, fresh_mvar, with_meta0_ctx};

    /// `N.succ N` — `infer_type` answers `N` (it never checks the
    /// argument), `check` rejects it: `N : Type`, not `N`.
    #[test]
    fn ill_typed_application_is_rejected_where_infer_type_succeeds() {
        with_meta0_ctx(|ctx| {
            let succ = c(ctx, "N.succ");
            let n = c(ctx, "N");
            let bad = app(ctx, succ, n);
            assert!(ctx.infer_type(bad).is_ok(), "the proxy would say type-correct");
            assert!(!ctx.is_type_correct(bad).unwrap());
        });
    }

    #[test]
    fn well_typed_application_is_accepted() {
        with_meta0_ctx(|ctx| {
            let succ = c(ctx, "N.succ");
            let zero = c(ctx, "N.zero");
            let ok = app(ctx, succ, zero);
            assert!(ctx.is_type_correct(ok).unwrap());
        });
    }

    /// `isTypeCorrect` does not roll back: `N.succ ?m` with `?m : ?T`
    /// assigns `?T := N` through `checkApp`'s `isDefEq`.
    #[test]
    fn check_keeps_defeq_assignments() {
        with_meta0_ctx(|ctx| {
            let n = c(ctx, "N");
            let ty = ctx.infer_type(n).unwrap(); // Type
            let (t, t_id) = fresh_mvar(ctx, ty);
            let (m, _) = fresh_mvar(ctx, t);
            let succ = c(ctx, "N.succ");
            let e = app(ctx, succ, m);
            assert!(ctx.is_type_correct(e).unwrap());
            assert!(ctx.mctx().is_assigned(t_id), "?T was assigned by checkApp");
        });
    }

    /// `let y : N := N; y` — the value's type is `Type`, not `N`.
    #[test]
    fn let_value_type_mismatch_is_rejected() {
        with_meta0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let n = c(ctx, "N");
            let b0 = ctx.scratch.expr_bvar(base, &leanr_kernel::Nat::from(0u64)).unwrap();
            let e = ctx.scratch.expr_let(base, None, n, n, b0, false).unwrap();
            assert!(!ctx.is_type_correct(e).unwrap());
        });
    }

    /// `N.{0}` — `N` has no universe parameters.
    #[test]
    fn wrong_universe_count_is_rejected() {
        with_meta0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let s = ctx.scratch.intern_str(base, "N").unwrap();
            let name = ctx.scratch.name_str(base, None, s).unwrap();
            let z = ctx.scratch.level_zero(base).unwrap();
            let levels = ctx.scratch.intern_level_list(base, &[z]).unwrap();
            let e = ctx.scratch.expr_const(base, Some(name), levels).unwrap();
            assert!(!ctx.is_type_correct(e).unwrap());
        });
    }
}
```

  `MetavarContext::is_assigned` (`mvar_ctx.rs:109`),
  `Store::expr_let(base, decl_name, ty, value, body, non_dep)` and
  `Store::expr_const(base, name, levels)` are the real signatures,
  checked while this plan was written.

- [ ] **Step 2: Run them and watch them fail.**

  Run: `cargo test -p leanr_meta check::tests`

  Expected: compile error, because there is no `check` module.
  `is_type_correct` is private in `assign.rs`.

- [ ] **Step 3: Rename the proxy.** In `assign.rs`, rename the
  private `fn is_type_correct` to `fn infer_type_succeeds`, and change
  the call at `:415` to match. Append to its doc:

```text
/// Renamed from `is_type_correct` in M4b-4c P2, when the real port landed
/// (`check.rs`). Behaviour unchanged. Follow-up: route this
/// `quasiPatternApprox` caller through `MetaCtx::is_type_correct`; that
/// is a behaviour change and needs its own oracle check.
```

- [ ] **Step 4: Implement `check.rs`.**

```rust
//! oracle: `Lean/Meta/Check.lean` (v4.33.0-rc1): `check` (`:331-338`)
//! over `checkAux` (`:288-329`), and `isTypeCorrect` (`:365-370`).
//! The error-message machinery (`throwAppTypeMismatch`,
//! `addPPExplicitToExposeDiff`) is not ported. The only caller,
//! `isTypeCorrect`, discards the message.

use std::collections::HashSet;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;

use crate::transparency::TransparencyMode;
use crate::{MetaCtx, MetaError};

impl<'e> MetaCtx<'e> {
    /// oracle: `check e (transparency := .all)`.
    pub fn check(&mut self, e: ExprId) -> Result<(), MetaError> {
        let mut seen = HashSet::new();
        self.with_transparency(TransparencyMode::All, |ctx| ctx.check_aux(e, &mut seen))
    }

    /// oracle: `isTypeCorrect`, `try check e; true catch _ => false`.
    /// Only oracle-shaped failures are folded into `false`:
    /// `MetaError::Check` (check's own throws) and `MetaError::Infer`
    /// (inference failures inside it). Budget exhaustion, named seams
    /// (`Unsupported`) and invariant violations PROPAGATE. Folding them
    /// would turn "leanr cannot answer" into a confident "ill-typed".
    pub fn is_type_correct(&mut self, e: ExprId) -> Result<bool, MetaError> {
        match self.check(e) {
            Ok(()) => Ok(true),
            Err(MetaError::Check(_)) | Err(MetaError::Infer(_)) => Ok(false),
            Err(other) => Err(other),
        }
    }

    /// oracle: `checkAux.check`. `checkCache` on `ExprStructEq` is a
    /// visited set: hash-consing makes `ExprId` equality structural.
    fn check_aux(&mut self, e: ExprId, seen: &mut HashSet<ExprId>) -> Result<(), MetaError> {
        if !seen.insert(e) {
            return Ok(());
        }
        self.step()?;
        match self.node(e) {
            Node::Forall { .. } => self.check_forall(e, seen),
            Node::Lam { .. } | Node::LetE { .. } => self.check_lambda_let(e, seen),
            Node::Const { name, levels } => self.check_constant(name, levels),
            Node::App { f, arg } => {
                self.check_aux(f, seen)?;
                self.check_aux(arg, seen)?;
                self.check_app(f, arg)
            }
            Node::MData { expr, .. } => self.check_aux(expr, seen),
            Node::Proj { .. } | Node::ProjBig { .. } => self.check_proj(e, seen),
            _ => Ok(()),
        }
    }
}
```

  Write the five helpers in the same file, one oracle clause each:

  - `check_forall`: open the forall telescope with `push_local_decl`,
    instantiating each body with `instantiate_beta_rev_range` exactly as
    `transform.rs`'s forall arm does. For each binder type, `ensure_type`
    then `check_aux`. Do the same for the body. Bracket the telescope
    with `lctx_checkpoint` / `lctx_restore` on every exit path.
  - `check_lambda_let`: the same, over `Lam` and `LetE`. For `LetE`:
    `ensure_type(t)`, `check_aux(t)`, then
    `if !is_def_eq(t, infer_type(v))` →
    `Err(MetaError::Check("let type mismatch".into()))`, then
    `check_aux(v)`. Push the let with `push_let_decl`.
  - `ensure_type(t)`: `self.get_level(t).map(|_| ())`. `get_level`
    already throws `Infer("type expected")`.
  - `check_constant(name, levels)`: `self.view.get(name)`'s level-param
    count must equal the `LevelsId` length, else
    `Err(Check("incorrect number of universe levels"))`. A missing
    constant gives `Err(Infer("unknown constant"))`, the oracle's
    `getConstVal` throw.
  - `check_app(f, a)`: `whnf(infer_type(f))` must be
    `Forall { binder_type: d, .. }`. If it is not, return
    `Err(Check("function expected"))`. If
    `!is_def_eq(d, infer_type(a))`, return
    `Err(Check("application type mismatch"))`.
  - `check_proj`: `check_aux` on the structure, then the oracle's
    `isProp structType && !isProp projType` test via the public
    `is_prop` (`lazy_delta.rs:171`), else
    `Err(Check("invalid projection"))`.

- [ ] **Step 5: Run the tests and watch them pass.**

  Run: `cargo test -p leanr_meta`

  Expected: all green. `assign.rs`'s behavior is unchanged (the
  rename only), so `oracle_fast` and `oracle_synth` stay green.

- [ ] **Step 6: Mutation check.** Make `check_app` return `Ok(())`
  unconditionally. The first and third tests must go red. Revert.

- [ ] **Step 7: Commit.**

```bash
cargo fmt --all && cargo clippy --workspace --all-targets -- -D warnings
git add crates/leanr_meta
git commit -m "M4b-4c P2: port Meta.check and isTypeCorrect"
```

---

### Task 3: leanr_elab: behavior-neutral extractions for `ElimElab`

**Files:**
- Modify: `crates/leanr_elab/src/app/state.rs`
- Modify: `crates/leanr_elab/src/elab.rs:154`

**Interfaces:**
- Produces: `TelescopeBinder { name, fvar, ty, bi: BinderInfo }`. The
  new `bi` field is `xDecl.binderInfo`.
- Produces: `pub(crate) fn whnf_forall(elab: &mut TermElabM<'_>, e: ExprId) -> Result<ExprId, ElabError>`.
  `AppElab::whnf_forall` delegates to it, and
  `open_forall_telescope_reducing`'s inline copy calls it.
- Produces: `pub(crate) fn open_forall_telescope(elab: &mut TermElabM<'_>, ty: ExprId) -> Result<(Vec<TelescopeBinder>, ExprId), ElabError>`.
  This is the oracle's non-reducing `forallTelescope`. It shares the
  loop with the reducing walk through a private
  `open_forall_telescope_core(elab, ty, reducing: bool)`.
- Produces:
  `pub(crate) fn TermElabM::synthesize_app_inst_mvars_of(&mut self, inst_mvars: Vec<MVarId>, app: ExprId, stx: &SynElem) -> Result<(), ElabError>`.
  It is `Term.synthesizeAppInstMVars` (`App.lean:75-79`).
  `AppElab::synthesize_app_inst_mvars` becomes
  `let m = take(&mut self.st.inst_mvars); self.elab.synthesize_app_inst_mvars_of(m, self.st.f, stx)`.
- Produces: `pub fn TermElabM::mk_const_with_fresh_mvar_levels_of`.
  Only its visibility changes, from `pub(crate)` to `pub`, so that the
  Task 5 tests can build a head.

- [ ] **Step 1: Baseline.**

  Run: `cargo test -p leanr_elab`

  It must be green. Note the passing test count.

- [ ] **Step 2: Make the five extractions.** Each one moves code
  without changing it. `open_forall_telescope_core` with
  `reducing == false` skips the `whnf` branch entirely. The oracle's
  `forallTelescope` walks syntactic `forallE`s only.

- [ ] **Step 3: Run the tests and watch them pass.**

  Run: `cargo test -p leanr_elab && git status --short tests/fixtures`

  Expected: the same test count, all green, and no fixture change.

- [ ] **Step 4: Commit.**

```bash
cargo fmt --all && cargo clippy --workspace --all-targets -- -D warnings
git add crates/leanr_elab
git commit -m "M4b-4c P2: extract telescope/whnfForall/inst-mvar helpers for ElimElab"
```

---

### Task 4: Eliminator errors and the `preElim` fixture

**Files:**
- Modify: `crates/leanr_elab/src/error.rs:340-369`
- Modify: `tests/fixtures/elab/Elab0.lean`, after `natElim` (`:872-876`)
- Regen: `tests/fixtures/elab/Elab0.olean`, `tests/fixtures/elab/elim.jsonl`
- Modify: `crates/leanr_olean/src/module_data.rs:1043`
- Modify: `crates/leanr_elab/tests/seam_audit.rs`, the `@[elab_as_elim]`
  assertion message (it names the tagged declarations)

**Interfaces:**
- Produces: `EliminatorErrorReason`. It drops `Copy` (keeps `Debug,
  Clone, PartialEq, Eq`) and gains these variants:

| Variant | `oracle_first_line()` |
|---|---|
| `NoExpectedType` | `failed to elaborate eliminator, expected type is not available` |
| `InsufficientArgs` | `failed to elaborate eliminator, insufficient number of arguments` |
| `InsufficientArgsExpectedType` | `failed to elaborate eliminator, insufficient number of arguments, expected type:` |
| `UnusedNamedArgs(Vec<String>)` | `failed to elaborate eliminator, unused named arguments: [a, b]` |
| `OverAppTypeIncorrect` | `failed to elaborate eliminator, after generalizing over-applied arguments, expected type is type incorrect:` |
| `MotiveNotTypeCorrect` | `failed to elaborate eliminator, motive is not type correct:` |
| `InvalidMotive` | `failed to elaborate eliminator, invalid motive` |
| `MotiveNotHead` | `Internal error, eliminator target type isn't an application of the motive` |

  The strings are the oracle's first lines, as printed by the planning
  probe and quoted in § Evidence below.
- Produces: `pub fn EliminatorErrorReason::oracle_first_line(&self) -> String`.
  The signature changes from `(self) -> &'static str`.
- Produces: `pub fn ElabError::oracle_first_line(&self) -> Option<String>`.
  It is `Some` for `Eliminator { reason }` and `None` for every other
  variant. Task 6's corpus gate compares it.

**Evidence (oracle, planning probe):** the first line of the first
logged message for each error query of Task 6 is exactly the string in
the table. `elimErr/unusedNamed` prints `[foo]`.

- [ ] **Step 1: Write the failing test** in `error.rs`'s test module.
  Add one if there is none: `#[cfg(test)] mod tests`.

```rust
#[test]
fn eliminator_first_lines_are_the_oracles() {
    use EliminatorErrorReason as R;
    assert_eq!(
        R::UnusedNamedArgs(vec!["foo".into(), "bar".into()]).oracle_first_line(),
        "failed to elaborate eliminator, unused named arguments: [foo, bar]"
    );
    assert_eq!(
        ElabError::Eliminator { reason: R::InvalidMotive }.oracle_first_line().as_deref(),
        Some("failed to elaborate eliminator, invalid motive")
    );
    assert_eq!(ElabError::Postpone.oracle_first_line(), None);
}
```

- [ ] **Step 2: Run it and watch it fail.**

  Run: `cargo test -p leanr_elab eliminator_first_lines`

  Expected: compile error.

- [ ] **Step 3: Implement.** Add the variants, change
  `oracle_first_line` to return `String` (the existing four arms use
  `.to_string()`), and add `ElabError::oracle_first_line`. Then fix
  the callers broken by the loss of `Copy` and the new return type:
  `cargo build -p leanr_elab --tests` lists them. Expect
  `elim_info.rs`'s test helper `reason` and
  `tests/elim_info_oracle.rs:42-60`. Comparing a `String` with a
  `&str` with `==` compiles unchanged.

- [ ] **Step 4: Add `preElim` to `Elab0.lean`** after `natElim`:

```lean
-- An explicit binder BEFORE the motive. It is the only shape that
-- reaches `finalize` with no motive yet ("insufficient number of
-- arguments", App.lean:1199-1200): `(preElim : Nat)` runs out of
-- positionals at `k`. An axiom, because a tagged `theorem`/`def` needs
-- a body, and `@[elab_as_elim]` accepts an axiom (measured).
@[elab_as_elim] axiom preElim (k : Nat) {motive : Nat → Prop}
    (z : motive Nat.zero) (n : Nat) : motive n
```

- [ ] **Step 5: Rebuild the fixture and the eliminator dump.**

```bash
cd /workspace/tests/fixtures/elab && lean Elab0.lean -o Elab0.olean
LEAN_PATH=$PWD lean --run dump_elim.lean > elim.jsonl
LEAN_PATH=$PWD lean --run dump_structs.lean > structures.jsonl
LEAN_PATH=$PWD lean --run dump_elab.lean > elab-queries.jsonl
cd /workspace && git diff --stat tests/fixtures/elab
```

  Expected:
  - `elim.jsonl` gains exactly one line (`"n":"preElim"`, `"tag":true`,
    `info` with `motive` 1);
  - `structures.jsonl` and `elab-queries.jsonl` are unchanged.

  Any other diff means the new axiom moved something. Stop and
  investigate.

- [ ] **Step 6: Update the decode golden** at
  `module_data.rs:1043`. Its value is the oracle's `Name.quickLt`
  order, which is hash-based, so it is not alphabetical. Run the test,
  take the three names in the order the decode reports them, and
  confirm the set is exactly `{Eq.subst', natElim, preElim}` before
  committing. Raise any hard-coded `elim.jsonl` record count in
  `tests/elim_info_oracle.rs` by one.

- [ ] **Step 7: Run the tests and watch them pass.**

  Run: `cargo test -p leanr_olean -p leanr_meta -p leanr_elab`

  Expected: all green.

- [ ] **Step 8: Commit.**

```bash
cargo fmt --all && cargo clippy --workspace --all-targets -- -D warnings
git add crates tests/fixtures/elab
git commit -m "M4b-4c P2: ElabElim error reasons and the preElim fixture eliminator"
```

---

### Task 5: The gate, `elab_as_elim_info`

**Files:**
- Create: `crates/leanr_elab/src/app/elim.rs` (gate half)
- Modify: `crates/leanr_elab/src/app/mod.rs` (`pub mod elim;`)
- Create: `crates/leanr_elab/tests/elim_smoke.rs`

**Interfaces:**
- Consumes: `get_elab_elim_info` (P1), `TelescopeBinder::bi` (Task 3),
  and the `MetaCtx` predicates (P1).
- Produces: `pub fn should_elab_as_elim(elab: &TermElabM<'_>, name: NameId) -> bool`
- Produces:

```rust
pub fn elab_as_elim_info(
    elab: &mut TermElabM<'_>,
    f: ExprId,
    named_args: &[NamedArg],
    args: &[Arg],
    explicit: bool,
    ellipsis: bool,
    kinds: &KindInterner,
) -> Result<Option<ElabElimInfo>, ElabError>
```

- [ ] **Step 1: Write the failing tests.** In `elim_smoke.rs`, each
  case parses an application, expands it with
  `leanr_elab::app::expand::expand_app`, and builds the head constant
  with `elab.mk_const_with_fresh_mvar_levels_of(name_id(elab, head))`.
  It then asks the gate and does **not** elaborate the arguments. The
  local names in the sources (`h`, `n`, `z`, `s`) never need to
  resolve.

```rust
mod support;
use support::{name_id, with_elab};

use leanr_elab::app::elim::elab_as_elim_info;
use leanr_elab::app::expand::expand_app;

/// `(head constant, source)` → does the gate divert?
fn gate(head: &str, src: &str) -> bool {
    with_elab(src, |elab, term, kinds| {
        let node = term.as_node().expect("an application node");
        let (_head, named, args, ellipsis) = expand_app(node, kinds).expect("expand");
        let c = name_id(elab, head);
        let f = elab.mk_const_with_fresh_mvar_levels_of(c).expect("declared");
        elab_as_elim_info(elab, f, &named, &args, false, ellipsis, kinds)
            .expect("gate")
            .is_some()
    })
}

#[test]
fn every_should_elab_as_elim_disjunct_diverts() {
    assert!(gate("Nat.rec", "Nat.rec z s n"), "isRec");
    assert!(gate("Nat.casesOn", "Nat.casesOn n z s"), "isCasesOnRecursor");
    assert!(gate("Nat.brecOn", "Nat.brecOn n s"), "isBRecOnRecursor");
    assert!(gate("Nat.recOn", "Nat.recOn n z s"), "isRecOnRecursor");
    assert!(gate("natElim", "natElim z s"), "elabAsElim tag");
    assert!(!gate("Nat.succ", "Nat.succ n"), "not an eliminator");
}

#[test]
fn a_supplied_motive_takes_the_standard_path() {
    assert!(!gate("Nat.rec", "Nat.rec (motive := m) z s n"), "named motive");
    // `False.rec`'s motive is EXPLICIT: a positional `_` counts as missing,
    // any other positional is the motive (App.lean:1422-1430).
    assert!(gate("False.rec", "False.rec _ h"), "positional hole");
    assert!(!gate("False.rec", "False.rec (fun _ => Nat) h"), "positional motive");
    assert!(!gate("False.rec", "False.rec h"), "positional non-hole");
    assert!(gate("False.rec", "False.rec"), "no positional at all");
    // `Nat.rec`'s motive is implicit, so the `_` is the zero minor.
    assert!(gate("Nat.rec", "Nat.rec _ s n"), "implicit motive ignores `_`");
}

#[test]
fn binders_before_the_motive_consume_their_arguments() {
    // `preElim (k : Nat) {motive}`: `k` eats one positional, motive implicit.
    assert!(gate("preElim", "preElim k z n"));
    // A named argument for a pre-motive binder is erased, not counted.
    assert!(gate("Eq.subst'", "Eq.subst' (α := Nat) h p"));
}

#[test]
fn explicit_and_ellipsis_opt_out() {
    with_elab("Nat.rec z s n", |elab, term, kinds| {
        let node = term.as_node().unwrap();
        let (_h, named, args, _e) = expand_app(node, kinds).unwrap();
        let c = name_id(elab, "Nat.rec");
        let f = elab.mk_const_with_fresh_mvar_levels_of(c).unwrap();
        assert!(elab_as_elim_info(elab, f, &named, &args, true, false, kinds).unwrap().is_none());
        assert!(elab_as_elim_info(elab, f, &named, &args, false, true, kinds).unwrap().is_none());
    });
}

/// A non-`.const` head (here an fvar) is never an eliminator head.
#[test]
fn a_local_head_is_not_gated() {
    with_elab("Nat.rec z s n", |elab, term, kinds| {
        let node = term.as_node().unwrap();
        let (_h, named, args, e) = expand_app(node, kinds).unwrap();
        let c = name_id(elab, "Nat.rec");
        let rec = elab.mk_const_with_fresh_mvar_levels_of(c).unwrap();
        let ty = elab.mctx.infer_type(rec).unwrap();
        let x = elab.mctx.push_local_decl(None, ty, leanr_kernel::BinderInfo::Default).unwrap();
        assert!(elab_as_elim_info(elab, x, &named, &args, false, e, kinds).unwrap().is_none());
    });
}
```

  If `support::with_elab` hands back the term already wrapped, or
  `expand_app` needs the `app` node specifically, adapt only the
  plumbing above. The assertions are the contract.

- [ ] **Step 2: Run them and watch them fail.**

  Run: `cargo test -p leanr_elab --test elim_smoke`

  Expected: compile error, because there is no `app::elim`.

- [ ] **Step 3: Implement the gate half of `app/elim.rs`.**

```rust
//! M4b-4c P2: eliminator elaboration. Oracle: `Lean/Elab/App.lean`,
//! `shouldElabAsElim` (`:1322-1328`), `elabAppArgs.elabAsElim?`
//! (`:1397-1431`) and the `ElabElim` namespace (`:1140-1319`).

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::BinderInfo;
use leanr_syntax::kind::KindInterner;

use crate::app::elim_info::{get_elab_elim_info, ElabElimInfo};
use crate::app::expand::{Arg, NamedArg};
use crate::app::lval;
use crate::app::state::open_forall_telescope_reducing;
use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `shouldElabAsElim` (`App.lean:1322-1328`). `isRec` is the
/// constant-kind test (`ConstantInfo::Rec`); the other four read P1's
/// decoded `auxRecExt` / `elabAsElim` sets.
pub fn should_elab_as_elim(elab: &TermElabM<'_>, name: NameId) -> bool {
    matches!(elab.view.get(name), Some(leanr_kernel::ConstantInfo::Rec(_)))
        || elab.mctx.is_cases_on_recursor(name)
        || elab.mctx.is_brec_on_recursor(name)
        || elab.mctx.is_rec_on_recursor(name)
        || elab.mctx.has_elab_as_elim_tag(name)
}

/// oracle: `elabAppArgs.elabAsElim?` (`App.lean:1397-1431`). `Some` means
/// divert to `ElabElim`. `heedElabAsElim` is not modelled: only the
/// `induction` tactic clears it (`Tactic/Induction.lean:806`), so in
/// term elaboration it is always `true`.
pub fn elab_as_elim_info(
    elab: &mut TermElabM<'_>,
    f: ExprId,
    named_args: &[NamedArg],
    args: &[Arg],
    explicit: bool,
    ellipsis: bool,
    kinds: &KindInterner,
) -> Result<Option<ElabElimInfo>, ElabError> {
    if explicit || ellipsis {
        return Ok(None);
    }
    let Node::Const { name: Some(name), .. } = lval::node(elab, f) else {
        return Ok(None);
    };
    if !should_elab_as_elim(elab, name) {
        return Ok(None);
    }
    let info = get_elab_elim_info(elab, name)?;
    let f_type = elab.mctx.infer_type(f)?;
    let cp = elab.mctx.lctx_checkpoint();
    let r = motive_supplied(elab, f_type, &info, named_args, args, kinds);
    elab.mctx.lctx_restore(cp);
    Ok(if r? { None } else { Some(info) })
}

/// The `forallTelescopeReducing` body of `elabAsElim?`
/// (`App.lean:1403-1431`): simulate argument consumption up to the
/// motive, then decide whether the caller already supplied it.
fn motive_supplied(
    elab: &mut TermElabM<'_>,
    f_type: ExprId,
    info: &ElabElimInfo,
    named_args: &[NamedArg],
    args: &[Arg],
    kinds: &KindInterner,
) -> Result<bool, ElabError> {
    let (xs, _) = open_forall_telescope_reducing(elab, f_type)?;
    let mut named: Vec<&str> = named_args.iter().map(|n| n.name.as_str()).collect();
    let mut args = args;
    let Some(pre) = xs.get(..info.motive_pos) else {
        // oracle: `unreachable!` (`:1420-1421`); `.olean` input is untrusted.
        return Err(ElabError::Internal("elabAsElim?: motivePos past the telescope".into()));
    };
    for x in pre {
        let user = binder_user_name(elab, x.name);
        if named.contains(&user.as_str()) {
            named.retain(|n| *n != user);
        } else if x.bi == BinderInfo::Default {
            args = args.get(1..).unwrap_or(&[]);
        }
    }
    let x = &xs[info.motive_pos];
    let user = binder_user_name(elab, x.name);
    if named.contains(&user.as_str()) {
        return Ok(true);
    }
    Ok(match (x.bi == BinderInfo::Default, args.first()) {
        (true, Some(Arg::Expr(_))) => true,
        (true, Some(Arg::Stx(stx))) => kinds.name(stx.kind()) != "Lean.Parser.Term.hole",
        (true, Some(Arg::AnonCtorTail { .. })) => true,
        _ => false,
    })
}

/// A binder's user name rendered the way `NamedArg::name` is stored
/// (source text). `.anonymous` renders as `[anonymous]`, which no
/// named argument can spell.
pub(crate) fn binder_user_name(elab: &TermElabM<'_>, n: Option<NameId>) -> String {
    let base = elab.view.store;
    elab.mctx.store().to_name(Some(base), n).to_string()
}
```

  Add `pub mod elim;` to `app/mod.rs`'s module list.

- [ ] **Step 4: Run the tests and watch them pass.**

  Run: `cargo test -p leanr_elab --test elim_smoke`

  Expected: PASS.

- [ ] **Step 5: Mutation check.** Apply each mutation, run the test
  above, confirm it goes red, and revert:
  - delete each of the five disjuncts;
  - invert the `!= "Lean.Parser.Term.hole"` test;
  - drop the `x.bi == BinderInfo::Default` arm of the pre-motive loop;
  - drop `explicit || ellipsis`.

  Record any survivor for Task 7.

- [ ] **Step 6: Commit.**

```bash
cargo fmt --all && cargo clippy --workspace --all-targets -- -D warnings
git add crates/leanr_elab
git commit -m "M4b-4c P2: elabAsElim? gate and shouldElabAsElim"
```

---

### Task 6: `ElimElab`, the diversion, seam removal, and the corpus

**Files:**
- Modify: `crates/leanr_elab/src/app/elim.rs` (the machine half)
- Modify: `crates/leanr_elab/src/app/mod.rs:510-548`. The comment
  block is replaced by the diversion.
- Modify: `crates/leanr_elab/src/app/head.rs`:
  - delete the dotIdent `heed` block (`:146-160`);
  - delete `elab_app_fn_id`'s `heed` and the long comment
    (`:434-486`);
  - delete `recursor_head_seam` (`:323-331`).
- Modify: `tests/fixtures/elab/dump_elab.lean`
- Regen: `tests/fixtures/elab/elab-queries.jsonl`
- Modify: `crates/leanr_elab/tests/oracle_elab.rs`: the `err` branch
  and `CORPUS_FLOOR`
- Modify: `crates/leanr_elab/tests/seam_audit.rs` (`:156-205`,
  `:383-433`, `:792-820`)
- Modify: `crates/leanr_elab/tests/postpone_smoke.rs:211-227`
- Modify: `crates/leanr_elab/tests/elim_smoke.rs` (postpone tests)

**Interfaces:**
- Consumes: everything from Tasks 1-5.
- Produces: `pub(crate) struct ElimElab`, `ElimElab::main`, and the
  `elab_app_args` diversion.

- [ ] **Step 1: Add the corpus queries to `dump_elab.lean`.** Add them
  after `anonTailQueries` (`:1114-1120`). Every query below was run on
  the oracle while this plan was written. The success rows elaborated,
  and each error row logged exactly the first line shown in Task 4's
  table.

```lean
-- M4b-4c P2: eliminator-headed applications (`ElabElim`). Each row was
-- run on the pinned oracle at plan time. Spec § Evidence lists the
-- terms these exercise.
def elimQueries : List (String × String) :=
  [ ("elim/rec",           "fun (n : Nat) => (Nat.rec Nat.zero (fun _ ih => Nat.succ ih) n : Nat)")
  , ("elim/casesOn",       "fun (n : Nat) => (Nat.casesOn n Nat.zero (fun m => m) : Nat)")
  , ("elim/recOn",         "fun (n : Nat) => (Nat.recOn n Nat.zero (fun _ ih => ih) : Nat)")
  , ("elim/brecOn",        "fun (n : Nat) => (Nat.brecOn n (fun _ _ => Nat.zero) : Nat)")
  , ("elim/namedMotive",   "fun (n : Nat) => Nat.rec (motive := fun _ => Nat) Nat.zero (fun _ ih => ih) n")
  , ("elim/explicitAt",    "fun (n : Nat) => @Nat.rec (fun _ => Nat) Nat.zero (fun _ ih => ih) n")
  , ("elim/ellipsis",      "Nat.rec ..")
  , ("elim/hRec",          "fun (h : False) => (h.rec : Nat)")
  , ("elim/hRecArg",       "fun (h : False) => Nat.succ h.rec")
  , ("elim/falseRecHole",  "fun (h : False) => (False.rec _ h : Nat)")
  , ("elim/falseRecMotive","fun (h : False) => (False.rec (fun _ => Nat) h : Nat)")
  , ("elim/subst",         "fun (a b : Nat) (h : Eq a b) (p : Eq a a) => (Eq.subst' h p : Eq a b)")
  , ("elim/natElimUnder",  "(natElim Nat.zero (fun _ ih => ih) : Nat → Nat)")
  , ("elim/natElimNamedMajor", "fun (m : Nat) => (natElim (n := m) Nat.zero (fun _ ih => ih) : Nat)")
  , ("elim/preElim",       "fun (n : Nat) (z : Eq Nat.zero Nat.zero) => (preElim Nat.zero z n : Eq n n)")
  , ("elim/dotRec",        "fun (n : Nat) => (.rec Nat.zero (fun _ ih => ih) n : Nat)")
  , ("elim/overApp",       "fun (n : Nat) => (Nat.rec (fun m => m) (fun _ ih m => ih m) n Nat.zero : Nat)")
  , ("elim/overAppDep",    "fun (n : Nat) => (Nat.rec (fun m => Eq.refl m) (fun _ ih m => ih m) n Nat.zero : Eq Nat.zero Nat.zero)")
  , ("elim/overPostponed", "fun (n : Nat) => (Nat.rec (fun m => m) (fun _ ih m => ih m) n (sameAs Nat.zero Nat.zero) : Nat)")
  , ("elim/postponed",     "fun (n : Nat) => sameAs (Nat.rec Nat.zero (fun _ ih => ih) n) n")
  , ("elim/argPos",        "fun (n : Nat) => Nat.succ (Nat.rec Nat.zero (fun _ ih => ih) n)")
  , ("elim/univ",          "fun (n : Nat) => (Nat.rec.{1} Nat.zero (fun _ ih => ih) n : Nat)")
  , ("elim/listRec",       "fun (l : List Nat) => (List.rec Nat.zero (fun _ _ ih => ih) l : Nat)")
  , ("elim/ndrec",         "fun (a b : Nat) (h : Eq a b) (p : Eq a a) => (Eq.ndrec p h : Eq a b)")
  , ("elim/letDiscr",      "fun (n : (let x := Nat.zero; Nat)) => (Nat.rec Nat.zero (fun _ ih => ih) n : Nat)")
  , ("elim/letDiscrUsed",  "fun (n : (let x := Nat; x)) => (Nat.rec Nat.zero (fun _ ih => ih) n : Nat)")
  , ("elim/letOver",       "fun (n : Nat) (m : (let x := Nat.zero; Nat)) => (Nat.rec (fun k => k) (fun _ ih k => ih k) n m : Nat)")
  ]

-- M4b-4c P2: queries the oracle REJECTS. Emitted as `{"id","src","err"}`,
-- where `err` is the first line of the first logged message. The oracle
-- logs through `errToSorry` and then aborts with an internal exception,
-- so the thrown exception's own text is only the fallback.
def elimErrQueries : List (String × String) :=
  [ ("elimErr/noExpected",          "fun (n : Nat) => Nat.rec Nat.zero (fun _ ih => ih) n")
  , ("elimErr/mvarExpected",        "fun (n : Nat) => (Nat.rec Nat.zero (fun _ ih => ih) n : _)")
  , ("elimErr/insufficient",        "(preElim : Nat)")
  , ("elimErr/insufficientExpected","fun (h : False) => (False.rec : Nat)")
  , ("elimErr/insufficientDomain",  "(natElim Nat.zero (fun _ ih => ih) : Bool → Nat)")
  , ("elimErr/unusedNamed",         "fun (n : Nat) => (Nat.rec (foo := Nat.zero) Nat.zero (fun _ ih => ih) n : Nat)")
  , ("elimErr/overAppIncorrect",    "fun (n : Nat) (p : Eq Nat.zero Nat.zero) => (Nat.rec (fun _ => p) (fun _ ih _ => ih Nat.zero) n Nat.zero : Eq p p)")
  , ("elimErr/motiveIncorrect",     "fun (n : Nat) (p : Eq n n) => (Nat.rec p (fun _ ih => ih) n : Eq p p)")
  , ("elimErr/invalidMotive",       "fun (a b : Nat) (h : Eq a b) (p : Eq a a) => (Eq.subst' h p : Nat)")
  ]

def emitErr (id src err : String) : IO Unit :=
  IO.println <| Json.compress <| Json.mkObj [("id", id), ("src", src), ("err", err)]
```

  Append `++ elimQueries` to `main`'s query list (`:1135`). Then add a
  second loop inside `go`, after the first:

```lean
    for (id, src) in elimErrQueries do
      match Lean.Parser.runParserCategory env `term src with
      | .error msg => IO.eprintln s!"dump_elab: parse error for {id}: {msg}"
      | .ok stx =>
        Core.resetMessageLog
        let thrown ← try
            discard <| (do
              let e ← Lean.Elab.Term.elabTerm stx none
              Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
              instantiateMVars e).run'
            pure none
          catch ex => pure (some (← ex.toMessageData.toString))
        let logged ← (← Core.getMessageLog).toList.mapM (·.data.toString)
        let first := fun (m : String) => (m.splitOn "\n").headD ""
        match logged.head?, thrown with
        | some m, _    => emitErr id src (first m)
        | none, some m => emitErr id src (first m)
        | none, none   => IO.eprintln s!"dump_elab: {id} was expected to fail but elaborated"
        Core.resetMessageLog
```

  Update the module doc's "Record shape" paragraph to describe the
  `err` record.

- [ ] **Step 2: Regenerate, and check that only additions appear.**

```bash
cd /workspace/tests/fixtures/elab && LEAN_PATH=$PWD lean --run dump_elab.lean > elab-queries.jsonl
cd /workspace && git diff --numstat tests/fixtures/elab/elab-queries.jsonl
grep -c '"err"' tests/fixtures/elab/elab-queries.jsonl
```

  Expected:
  - `36	0`: 27 `elim/*` records and 9 `elimErr/*` records added, none
    removed;
  - `9` `err` records, each first line one of Task 4's table strings,
    and `elimErr/unusedNamed`'s ending in `[foo]`.

  A missing record shows up on the dumper's stderr. Stop and
  investigate it; do not drop it.

- [ ] **Step 3: Write the failing gate branch.** In `oracle_elab.rs`,
  immediately before `match got {`:

```rust
        // M4b-4c P2: an `err` record is a query the ORACLE rejects. leanr
        // must reject it too, with the same first line. Only errors with
        // an `oracle_first_line` can match, which today is
        // `ElabError::Eliminator`.
        if let Some(want) = q.get("err").and_then(|v| v.as_str()) {
            match got {
                Err(e) => {
                    let line = e.oracle_first_line();
                    if line.as_deref() != Some(want) {
                        failures.push(format!("{id}: leanr error {e:?} (first line {line:?}); oracle {want:?}"));
                    }
                }
                Ok(_) => failures.push(format!("{id}: leanr elaborated; oracle errors with {want:?}")),
            }
            continue;
        }
```

  Set `CORPUS_FLOOR` to the new `wc -l tests/fixtures/elab/elab-queries.jsonl`
  value (expected 329), with a history line:
  `// 276 -> 329 (M4b-4c P2): M4b-4b's 17 anon/* records, never folded in, plus the 36 elim/* and elimErr/* records.`

- [ ] **Step 4: Run the gate and watch it fail.**

  Run: `cargo test -p leanr_elab --test oracle_elab`

  Expected: FAIL. `elim/rec` and friends hit the M4b-4c seam, the aux
  recursors and tagged heads diverge, and every `elimErr/*` errors with
  the wrong variant or elaborates.

- [ ] **Step 5: Implement `ElimElab`** in `app/elim.rs`. Add these
  imports to the module: `MVarId`, `MVarKind`, `SynElem`, `TermTarget`,
  `NodeOrToken`, and `EliminatorErrorReason as R`. Also bring in Task
  3's `whnf_forall`, `open_forall_telescope` and
  `TermElabM::synthesize_app_inst_mvars_of`.

```rust
/// oracle: `ElabElim.Context` + `ElabElim.State` (`App.lean:1142-1162`),
/// one struct, the same way `AppElab` folds `ElabAppArgs.M`
/// (`state.rs`'s module doc). Deliberately not an `AppElab`: the oracle's
/// `ElabElim.M` has its own state, and its `fType` is kept INSTANTIATED
/// after every argument (`addArgAndContinue`), unlike `AppElab`'s lazy
/// `fArgs` scheme.
pub(crate) struct ElimElab<'a, 'e> {
    pub(crate) elab: &'a mut TermElabM<'e>,
    // Context
    pub(crate) info: ElabElimInfo,
    pub(crate) expected: ExprId,
    /// The application's syntax: the oracle's ambient `getRef`
    /// (`state::Context::stx`'s doc). Used for `.expr` arguments'
    /// `ensureArgType` and for `synthesizeAppInstMVars`.
    pub(crate) stx: SynElem,
    // State
    pub(crate) f: ExprId,
    pub(crate) f_type: ExprId,
    pub(crate) named_args: Vec<NamedArg>,
    pub(crate) args: Vec<Arg>,
    pub(crate) inst_mvars: Vec<MVarId>,
    pub(crate) idx: usize,
    pub(crate) motive: Option<ExprId>,
}

/// oracle: `LOption Arg`, as returned by `getNextArg?`.
enum NextArg {
    Some(Arg),
    None,
    Undef,
}

impl ElimElab<'_, '_> {
    /// oracle: `ElabElim.main` (`App.lean:1286-1317`). The oracle
    /// recurses through `addArgAndContinue`; this loops.
    pub(crate) fn main(mut self, kinds: &KindInterner) -> Result<ExprId, ElabError> {
        loop {
            let ft = whnf_forall(self.elab, self.f_type)?;
            let Node::Forall { binder_name, binder_type, body, binder_info } = lval::node(self.elab, ft)
            else {
                return self.finalize(kinds);
            };
            let arg = if self.idx == self.info.motive_pos {
                let m = match self.get_next_arg(binder_name, binder_info) {
                    // `elabAsElim?` guarantees this is a positional `_`.
                    NextArg::Some(a) => self.elab_arg(a, binder_type, kinds)?,
                    // `.undef`: the explicit motive is missing; treated as
                    // implicit so `h.rec` works (`App.lean:1301-1305`).
                    NextArg::None | NextArg::Undef => self.mk_implicit_arg(binder_type, binder_info)?,
                };
                self.motive = Some(m);
                m
            } else if self.info.majors_pos.contains(&self.idx) {
                match self.get_next_arg(binder_name, binder_info) {
                    NextArg::Some(a) => self.elab_arg(a, binder_type, kinds)?,
                    NextArg::Undef => return self.finalize(kinds),
                    NextArg::None => self.mk_implicit_arg(binder_type, binder_info)?,
                }
            } else {
                match self.get_next_arg(binder_name, binder_info) {
                    NextArg::Some(Arg::Stx(stx)) => self.elab.postpone_elab_term(&stx, Some(binder_type))?,
                    NextArg::Some(Arg::AnonCtorTail { node, from }) => self
                        .elab
                        .postpone_elab_target(&TermTarget::AnonCtorTail { node, from }, Some(binder_type))?,
                    NextArg::Some(Arg::Expr(v)) => {
                        let stx = self.stx.clone();
                        self.elab.ensure_has_type(&stx, Some(binder_type), v)?
                    }
                    NextArg::Undef => return self.finalize(kinds),
                    NextArg::None => self.mk_implicit_arg(binder_type, binder_info)?,
                }
            };
            // oracle: `addArgAndContinue`. `saveArgInfo`'s
            // `registerMVarArgName` is error-prose bookkeeping only and is
            // not ported (`args.rs`'s `mk_inst_mvar` precedent).
            self.idx += 1;
            let base = self.elab.view.store;
            self.f = self
                .elab
                .mctx
                .store_mut()
                .expr_app(Some(base), self.f, arg)
                .map_err(leanr_meta::MetaError::from)?;
            self.f_type = self.elab.mctx.instantiate_beta_rev_range(body, &[arg])?;
        }
    }

    /// oracle: `getNextArg?` (`App.lean:1247-1260`).
    fn get_next_arg(&mut self, binder_name: Option<NameId>, bi: BinderInfo) -> NextArg {
        let user = binder_user_name(self.elab, binder_name);
        if let Some(na) = self.named_args.iter().find(|n| n.name == user).cloned() {
            self.named_args.retain(|n| n.name != user);
            return NextArg::Some(na.val);
        }
        if bi == BinderInfo::Default {
            if self.args.is_empty() {
                NextArg::Undef
            } else {
                NextArg::Some(self.args.remove(0))
            }
        } else {
            NextArg::None
        }
    }

    /// oracle: `elabArg` (`App.lean:1267-1272`): the RAW binder type, no
    /// `consumeTypeAnnotations` (unlike `AppElab::get_arg_expected_type`).
    fn elab_arg(&mut self, arg: Arg, expected: ExprId, kinds: &KindInterner) -> Result<ExprId, ElabError> {
        match arg {
            Arg::Expr(v) => {
                let stx = self.stx.clone();
                self.elab.ensure_has_type(&stx, Some(expected), v)
            }
            Arg::Stx(stx) => {
                let v = self.elab.elab_term(&stx, kinds, Some(expected))?;
                self.elab.ensure_has_type(&stx, Some(expected), v)
            }
            Arg::AnonCtorTail { node, from } => {
                let r = NodeOrToken::Node(node.clone());
                let v = self.elab.elab_target(&TermTarget::AnonCtorTail { node, from }, kinds, Some(expected))?;
                self.elab.ensure_has_type(&r, Some(expected), v)
            }
        }
    }

    /// oracle: `mkImplicitArg` (`App.lean:1280-1284`).
    fn mk_implicit_arg(&mut self, ty: ExprId, bi: BinderInfo) -> Result<ExprId, ElabError> {
        let inst = bi == BinderInfo::InstImplicit;
        let kind = if inst { MVarKind::Synthetic } else { MVarKind::Natural };
        let (e, id) = self.elab.mk_fresh_expr_mvar_of_kind(ty, kind)?;
        if inst {
            self.inst_mvars.push(id);
        }
        Ok(e)
    }
}
```

  Then `finalize`, `revert_args` and `mk_motive`, one oracle clause per
  line:

```rust
impl ElimElab<'_, '_> {
    /// oracle: `finalize` (`App.lean:1196-1240`).
    fn finalize(mut self, kinds: &KindInterner) -> Result<ExprId, ElabError> {
        if !self.named_args.is_empty() {
            let names = self.named_args.iter().map(|n| n.name.clone()).collect();
            return Err(ElabError::Eliminator { reason: R::UnusedNamedArgs(names) });
        }
        let Some(motive) = self.motive else {
            return Err(ElabError::Eliminator { reason: R::InsufficientArgs });
        };
        // oracle: `forallTelescope`. The fvars are scoped to it.
        let cp = self.elab.mctx.lctx_checkpoint();
        let r = self.finalize_in_telescope(motive, kinds);
        self.elab.mctx.lctx_restore(cp);
        r
    }

    fn finalize_in_telescope(&mut self, motive: ExprId, kinds: &KindInterner) -> Result<ExprId, ElabError> {
        let (binders, f_type) = open_forall_telescope(self.elab, self.f_type)?;
        let xs: Vec<ExprId> = binders.iter().map(|b| b.fvar).collect();
        let insufficient = || ElabError::Eliminator { reason: R::InsufficientArgsExpectedType };
        let mut expected = self.expected;
        let mut f = self.f;
        if !xs.is_empty() {
            // Under-application: specialize the expected type by `xs`.
            for &x in &xs {
                let w = self.elab.mctx.whnf(expected)?;
                let Node::Forall { binder_type: t, body: b, .. } = lval::node(self.elab, w) else {
                    return Err(insufficient());
                };
                let x_ty = self.elab.mctx.infer_type(x)?;
                if !self.elab.mctx.with_full_approx_def_eq(|m| m.is_def_eq(t, x_ty))? {
                    return Err(insufficient());
                }
                expected = self.elab.mctx.instantiate1(b, x)?;
            }
        } else {
            // Over-application (or exact): "revert" the remaining arguments.
            (f, expected) = self.revert_args(f, expected, kinds)?;
            if !self.elab.mctx.is_type_correct(expected)? {
                return Err(ElabError::Eliminator { reason: R::OverAppTypeIncorrect });
            }
        }
        let result = mk_app_n(self.elab, f, &xs)?;
        if lval::app_fn(self.elab, f_type) != motive {
            return Err(ElabError::Eliminator { reason: R::MotiveNotHead });
        }
        let discrs = lval::app_args(self.elab, f_type);
        let motive_val = self.mk_motive(&discrs, expected)?;
        if !self.elab.mctx.is_type_correct(motive_val)? {
            return Err(ElabError::Eliminator { reason: R::MotiveNotTypeCorrect });
        }
        if !self.elab.mctx.is_def_eq(motive, motive_val)? {
            return Err(ElabError::Eliminator { reason: R::InvalidMotive });
        }
        let inst = std::mem::take(&mut self.inst_mvars);
        let stx = self.stx.clone();
        self.elab.synthesize_app_inst_mvars_of(inst, result, &stx)?;
        let result = self.elab.mctx.instantiate_mvars(result)?;
        Ok(self.elab.mctx.mk_lambda(&xs, result)?)
    }

    /// oracle: `revertArgs` (`App.lean:1179-1190`). `foldrM`: the
    /// arguments are ELABORATED right to left.
    fn revert_args(&mut self, f: ExprId, expected: ExprId, kinds: &KindInterner) -> Result<(ExprId, ExprId), ElabError> {
        let args = std::mem::take(&mut self.args);
        let mut vals = Vec::with_capacity(args.len());
        let mut expected = expected;
        for arg in args.into_iter().rev() {
            let val = match arg {
                Arg::Expr(v) => v,
                Arg::Stx(stx) => self.elab.elab_term(&stx, kinds, None)?,
                Arg::AnonCtorTail { node, from } => {
                    self.elab.elab_target(&TermTarget::AnonCtorTail { node, from }, kinds, None)?
                }
            };
            let val = self.elab.mctx.instantiate_mvars(val)?;
            let body = self.elab.mctx.kabstract(expected, val)?;
            let ty = self.elab.mctx.infer_type(val)?;
            let ty = self.elab.mctx.instantiate_mvars(ty)?;
            let ty = self.elab.mctx.transform_used_let_only(ty)?;
            let name = self.elab.mk_fresh_binder_name()?;
            let base = self.elab.view.store;
            expected = self
                .elab
                .mctx
                .store_mut()
                .expr_forall(Some(base), Some(name), ty, body, BinderInfo::Default)
                .map_err(leanr_meta::MetaError::from)?;
            vals.push(val);
        }
        vals.reverse();
        Ok((mk_app_n(self.elab, f, &vals)?, expected))
    }

    /// oracle: `mkMotive` (`App.lean:1167-1173`), `foldrM` from the right.
    fn mk_motive(&mut self, discrs: &[ExprId], expected: ExprId) -> Result<ExprId, ElabError> {
        let mut motive = expected;
        for &discr in discrs.iter().rev() {
            let discr = self.elab.mctx.instantiate_mvars(discr)?;
            let body = self.elab.mctx.kabstract(motive, discr)?;
            let ty = self.elab.mctx.infer_type(discr)?;
            let ty = self.elab.mctx.instantiate_mvars(ty)?;
            let ty = self.elab.mctx.transform_used_let_only(ty)?;
            let name = self.elab.mk_fresh_binder_name()?;
            let base = self.elab.view.store;
            motive = self
                .elab
                .mctx
                .store_mut()
                .expr_lam(Some(base), Some(name), ty, body, BinderInfo::Default)
                .map_err(leanr_meta::MetaError::from)?;
        }
        Ok(motive)
    }
}

/// `mkAppN f args`.
fn mk_app_n(elab: &mut TermElabM<'_>, f: ExprId, args: &[ExprId]) -> Result<ExprId, ElabError> {
    let base = elab.view.store;
    let mut r = f;
    for &a in args {
        r = elab.mctx.store_mut().expr_app(Some(base), r, a).map_err(leanr_meta::MetaError::from)?;
    }
    Ok(r)
}
```

  `lval::app_fn` / `lval::app_args` (`lval.rs:79-95`) are
  `pub(crate)`, so they are usable here. Check the signatures of
  `elab_target`, `postpone_elab_target` and `ensure_has_type` before
  compiling. Their visibility may need `pub(crate)`, which is a
  behavior-neutral widening.

- [ ] **Step 6: The diversion.** In `app/mod.rs::elab_app_args`,
  replace the comment block `:510-548` with:

```rust
    // oracle: `App.lean:1373-1383`. When `elabAsElim?` answers, the WHOLE
    // application goes to `ElabElim.main`, and `AppElab` is never built.
    if let Some(info) =
        elim::elab_as_elim_info(elab, f, &named_args, &args, explicit, ellipsis, kinds)?
    {
        elab.try_postpone_if_none_or_mvar(expected)?;
        let no_expected = || ElabError::Eliminator {
            reason: crate::error::EliminatorErrorReason::NoExpectedType,
        };
        let expected = expected.ok_or_else(no_expected)?;
        let expected = elab.mctx.instantiate_mvars(expected)?;
        let head = lval::app_fn(elab, expected);
        if matches!(lval::node(elab, head), leanr_kernel::bank::terms::Node::MVar { .. }) {
            return Err(no_expected());
        }
        return elim::ElimElab {
            elab,
            info,
            expected,
            stx,
            f,
            f_type,
            named_args,
            args,
            inst_mvars: Vec::new(),
            idx: 0,
            motive: None,
        }
        .main(kinds);
    }
```

  (Import `lval` and `elim` as the file requires.)

- [ ] **Step 7: Remove the seams.** In `head.rs`:
  - delete the dotIdent arm's `heed` block (`:146-160`), leaving
    `Ok(vec![crate::app::lval::elab_app_lvals(elab, f, lvals, call, kinds)?])`;
  - in `elab_app_fn_id`, delete `heed`, the `info` lookup used only
    by the guard, the long comment, and the `if heed && …` return
    (`:434-486`);
  - delete `recursor_head_seam`.

  Reword `elab_app_fn`'s doc paragraph about "the recursor guard" to
  say that the `elabAsElim?` gate now lives in `app/elim.rs`, on the
  final head in `elab_app_args`.

- [ ] **Step 8: Update the seam tests.**
  - `seam_audit.rs::deferred_constructs_are_named_seams`: delete the
    three `M4b-4c` rows and their comment. The `@(…)` row stays.
  - `seam_audit.rs::fixture_declares_no_undecoded_elab_attributes`:
    - delete the whole `elab-queries.jsonl` loop and its comment;
    - keep the `elab_without_expected_type` ban and the
      `@[elab_as_elim]` presence assertion;
    - reword the doc to say that `ElabElim` routes every
      `shouldElabAsElim` head (M4b-4c P2), so only the undecoded
      attribute is still gated.
  - `seam_audit.rs::no_seam_message_names_a_completed_slice`: add
    `"M4b-4c"` to `needles` and to the assertion message.
  - `postpone_smoke.rs::a_seam_in_a_resumed_term_propagates_under_postpone_on_error`:
    `Nat.rec` is no longer a seam. Use an unregistered kind instead,
    which is still a named `UnsupportedSyntax`
    (`seam_audit.rs::unregistered_kinds_are_named_by_kind`). Change the
    source to `"match Nat.zero with | x => x"` and the assertion to
    `Err(ElabError::UnsupportedSyntax(m)) => assert!(m.contains("Lean.Parser.Term.match"), "{m}")`.
    Update the doc's last sentence to match.
  - Add to `elim_smoke.rs` the oracle behavior that replaces the old
    seam. `Nat.rec`, postponed and resumed, is an oracle error
    (`NoExpectedType`):
    - under `postponeOnError` it is swallowed as "not ready";
    - without it, it propagates.

```rust
use leanr_elab::error::EliminatorErrorReason;
use leanr_elab::ElabError;

#[test]
fn a_resumed_eliminator_without_expected_type_is_an_oracle_error() {
    with_elab("Nat.rec", |elab, term, kinds| {
        elab.postpone_elab_term(term, None).unwrap();
        let id = elab.pending_mvars[0];
        let soft = elab.without_postponing(|e| e.synthesize_synthetic_mvar(id, true, false, kinds));
        assert!(matches!(soft, Ok(false)), "postponeOnError swallows an oracle error: {soft:?}");
        let hard = elab.without_postponing(|e| e.synthesize_synthetic_mvar(id, false, false, kinds));
        assert!(
            matches!(hard, Err(ElabError::Eliminator { reason: EliminatorErrorReason::NoExpectedType })),
            "{hard:?}"
        );
    });
}
```

- [ ] **Step 9: Run everything and watch it pass.**

  Run: `cargo test -p leanr_elab`

  Expected: all green. That covers:
  - `oracle_elab_gate` with all 329 records;
  - `elim_smoke`, `seam_audit`, `postpone_smoke` and `elim_info_oracle`;
  - `elab_as_elim_guard_honours_the_explicit_and_ellipsis_early_out`,
    which is unchanged: `@Nat.rec` and `Nat.rec ..` still take the
    ordinary path.

  For any `oracle_elab` divergence, read the record's oracle `exp`
  against leanr's output. The likely culprits, in order:
  1. argument order in `revert_args`/`mk_motive` (both are right
     folds);
  2. `kabstract` on an un-instantiated term;
  3. `binder_type` taken from the pre-`whnf_forall` type.

- [ ] **Step 10: Mutation check.** Apply each mutation, run
  `cargo test -p leanr_elab --test oracle_elab`, confirm it goes red,
  and revert. Note which records kill each one:
  - `mk_motive` folds left (`discrs.iter()` without `.rev()`);
  - `Undef` at the motive calls `finalize` instead of
    `mk_implicit_arg` (expect `elim/hRec`);
  - `is_type_correct` replaced by `infer_type(..).is_ok()` (expect
    `elimErr/motiveIncorrect` and `elimErr/overAppIncorrect`);
  - `transform_used_let_only` replaced by identity (expect
    `elim/letDiscr` and `elim/letOver`);
  - `with_full_approx_def_eq` removed (plain `is_def_eq`). If no
    record kills it, record a survivor;
  - `revert_args` elaborates left to right (if this survives, record
    it. No committed query has two over-applied syntax arguments that
    interact);
  - drop the mvar-headed-expected check in the diversion (expect
    `elimErr/mvarExpected`).

- [ ] **Step 11: Commit.**

```bash
cargo fmt --all && cargo clippy --workspace --all-targets -- -D warnings
git add crates tests/fixtures/elab
git commit -m "M4b-4c P2: ElabElim, the elabAppArgs diversion, seam removal, eliminator corpus"
```

---

### Task 7: Documentation, full CI, and the spec's § Landed

**Files:**
- Modify: `crates/leanr_elab/src/app/mod.rs`, the module doc. In the
  table at `:63-77` and the PARTIAL-seam paragraph at `:79-85`, make
  the `elabAsElim` row `SHIPPED (M4b-4c) — app/elim.rs` and delete the
  paragraph.
- Modify: `crates/leanr_elab/src/dispatch.rs:178-179`. The row becomes
  `elabAsElim .................................. M4b-4c SHIPPED — app/elim.rs`.
- Modify: `crates/leanr_elab/src/lib.rs:120-129`, the `elabAsElim`
  deferral bullet. Reword it as shipped.
- Modify: `docs/superpowers/specs/2026-10-01-m4b4c-elab-as-elim-design.md`,
  appending `### P2 (PR #NN): ElabElim` under § Landed.

- [ ] **Step 1: Update the docs** above. Then check:

```bash
grep -rn "M4b-4c" crates/leanr_elab/src | grep -v "^\S*:\s*//"
```

  Expected: no output. Every remaining mention is in a comment, and
  `no_seam_message_names_a_completed_slice` enforces this.

- [ ] **Step 2: Re-verify the oracle citations.** For every
  `App.lean:` / `Check.lean:` / `Basic.lean:` citation added on this
  branch, open the cited lines in the v4.33.0-rc1 source and fix any
  that are off:

```bash
git diff main --name-only | xargs grep -n "App.lean:\|Check.lean:\|Basic.lean:"
```

- [ ] **Step 3: Run full CI, blocking.**

```bash
mise run ci; echo "CI_EXIT=$?"
```

  Expected: `CI_EXIT=0`. Do not background this.

- [ ] **Step 4: Write § Landed › P2.** Include:
  - the spec corrections from this plan's "Spec corrections" section;
  - the mutation results from Tasks 2, 5 and 6, with killers and
    survivors;
  - the remaining open seams:
    - `@[elab_without_expected_type]`, still banned;
    - `kabstract` mvar-pattern oracle records;
    - the `infer_type_succeeds` proxy in `assign.rs`'s
      `quasiPatternApprox` branch;
    - `trace[Elab.app.elab_as_elim]`;
    - the `numScopeArgs` gap, if any query hit it;
  - the line "M4b-4 is complete."

- [ ] **Step 5: Commit.**

```bash
git add crates docs
git commit -m "M4b-4c P2: docs, seam bookkeeping, spec Landed"
```
