# Synth pi-goals Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Typeclass synthesis in leanr_meta must answer goals of the form `∀ xs, C ..`, at the root and in nested subgoals, the way the pinned oracle does. Today those goals raise `MetaError::Unsupported`.

**Architecture:** Add one private telescope helper, `MetaCtx::with_forall_telescope`, in `synth.rs`. It is built on `push_local_decl` + `lctx_checkpoint`/`lctx_restore`. Port the oracle's five telescope sites onto it one-to-one: `preprocess`, `preprocess_out_param`, `get_instances`, `get_subgoals` and `try_resolve`. Subgoal mvars are minted at the outer lctx with type `∀ xs, d` and applied to `xs`. `try_resolve` closes over `xs` with `mk_lambda_eta`.

**Tech Stack:** Rust (leanr_meta and the leanr_elab tests), Lean 4 oracle fixtures (`lean --run` dumpers), mise tasks.

**Spec:** `docs/superpowers/specs/2026-10-02-synth-pi-goals-design.md` (branch `synth-pi-goals`, 4595e44). Read it before starting any task.

## Global Constraints

- Pinned oracle: `leanprover/lean4:v4.33.0-rc1`. Do not bump it. Oracle sources are at `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/`.
- **Open every oracle citation you write against that tree.** Do not copy cites from this plan, the spec or old doc comments without opening the line; they drift by 1–2 lines.
- Every existing binder-free goal must take the same instructions as before (`xs = []`). The existing synth corpus (`oracle_synth`, 30 compared records) and every elab corpus must stay green, with no re-blessing.
- `removeUnusedArguments?` is NOT ported. It stays a NAMED SEAM with a new rationale (spec § Seams).
- No new dependencies. leanr_kernel is untouched.
- Before every commit, run `cargo fmt --all` and `cargo clippy -p leanr_meta -p leanr_elab --all-targets -- -D warnings`. CI's `mise run ci` gates on both.
- Build under `/workspace` (the default `target/`), never under `/tmp`.
- Run blocking cargo/CI commands in the foreground. Never background `mise run ci` and end your turn.
- Every mutation listed in a task is actually applied, run, observed failing, and reverted. Record the observed failing test or record in the commit message.

## Review Focus

1. **A pi goal answered by an ambient local instance.** With `h : Add N` in scope, `N → Add N` should answer `fun _ => h`. This proves the outer lctx snapshot carries local instances into `get_subgoals`/`get_instances`. Test: Task 2, `pi_goal_uses_an_ambient_local_instance`.
2. **An error raised inside a telescope.** A `MetaError` from `k` must still restore `lctx` and `local_instances`, or later queries would see phantom locals. Test: Task 1, `with_forall_telescope_restores_on_err`.
3. **A goal's own instance binder** (`∀ [h : Add N], Add N`). `get_instances` must not offer `h`, because the oracle reads local instances before its telescope. Test: Task 1, `get_instances_ignores_the_goals_own_instance_binder`. Oracle row: Task 3, `piInstBinder`.
4. **A pi goal whose body still has an expr mvar** (`N → Add ?a`). This takes the `is_def_eq(mvar, instVal)` recheck path with a pi-typed mvar. It must return `Ok(_)`, never `Err` or a panic. Test: Task 2, `pi_goal_with_mvar_body_does_not_error`.
5. **Synthesis called from inside an elaborator binder** (an outer fvar context plus a telescope). Covered by the re-recorded `op/beq-prop-bool` (`fun (b : Bool) => True == b`) in Task 4.

---

### Task 1: The telescope helper; `preprocess`, `preprocess_out_param`, `get_instances`

**Files:**
- Modify: `crates/leanr_meta/src/synth.rs`. Add the helper next to `preprocess` (~:1855). Port `preprocess` (~:1856-1934) and `preprocess_out_param` (~:1936-2050). Update the tests module: replace `preprocess_seams_a_pi_shaped_goal` (~:3638-3658) and add new tests.
- Modify: `crates/leanr_meta/src/instances.rs`. Change `get_instances` (~:484-648) and the module-doc paragraph at ~:103 that says the goal is "ALREADY-telescoped".

**Interfaces:**
- Produces (Task 2 relies on it):
  ```rust
  pub(crate) fn with_forall_telescope<R>(
      &mut self,
      ty: ExprId,
      reducing: bool,
      k: impl FnOnce(&mut MetaCtx<'e>, &[ExprId], ExprId) -> Result<R, MetaError>,
  ) -> Result<R, MetaError>
  ```
  `k(ctx, xs, body)` receives the fvars in binder order and the instantiated body. The ambient `lctx`/`local_names`/`local_instances` are restored on every exit.

- [ ] **Step 1: Write the failing tests** (in `synth.rs`'s `mod tests`)

Replace `preprocess_seams_a_pi_shaped_goal` with the tests below. `mk_arrow_for_test`, `const_named`, `parse_goal` and `with_instances_ctx` already exist in the module.

```rust
    /// oracle: `preprocess` (`SynthInstance.lean:737-773`) telescopes a
    /// pi-shaped goal, `whnf`s the body and rebuilds with `mkForallFVars`.
    #[test]
    fn preprocess_telescopes_a_pi_shaped_goal() {
        with_instances_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let add_n = parse_goal(ctx, "Add N");
            let pi = mk_arrow_for_test(ctx, n, add_n);
            let r = ctx.preprocess(pi).expect("pi goal preprocesses");
            assert!(matches!(r.kind, PreprocessKind::NoMVars));
            let Node::Forall { binder_type, body, .. } = ctx.node(r.ty) else {
                panic!("preprocess must return a forall, got {:?}", ctx.node(r.ty));
            };
            assert_eq!(binder_type, n);
            assert_eq!(body, add_n, "closed body re-abstracted unchanged");
        });
    }

    #[test]
    fn with_forall_telescope_opens_and_restores() {
        with_instances_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let add_n = parse_goal(ctx, "Add N");
            let pi = mk_arrow_for_test(ctx, n, add_n);
            let before = ctx.lctx_checkpoint();
            let (len, body) = ctx
                .with_forall_telescope(pi, true, |c, xs, body| {
                    assert_eq!(c.lctx_checkpoint(), before + 1, "one fvar pushed");
                    Ok((xs.len(), body))
                })
                .expect("telescope");
            assert_eq!((len, body), (1, add_n));
            assert_eq!(ctx.lctx_checkpoint(), before, "lctx restored on Ok");
        });
    }

    #[test]
    fn with_forall_telescope_restores_on_err() {
        with_instances_ctx(|ctx| {
            let add_n = parse_goal(ctx, "Add N");
            // `[h : Add N] → Add N`: the binder is installed as a local instance.
            let base = Some(ctx.view.store);
            let pi = ctx
                .scratch
                .expr_forall(base, None, add_n, add_n, BinderInfo::InstImplicit)
                .expect("pi");
            let before = ctx.lctx_checkpoint();
            let insts_before = ctx.local_instances.entries().len();
            let r: Result<(), MetaError> = ctx.with_forall_telescope(pi, true, |c, _, _| {
                assert_eq!(c.local_instances.entries().len(), insts_before + 1);
                Err(MetaError::Infer("boom".into()))
            });
            assert!(r.is_err());
            assert_eq!(ctx.lctx_checkpoint(), before, "lctx restored on Err");
            assert_eq!(ctx.local_instances.entries().len(), insts_before);
        });
    }

    /// Table keys of pi goals: closed `∀ xs, C ..` with loose bvars in
    /// the body must normalize structurally and deterministically.
    #[test]
    fn normalize_goal_key_handles_a_pi_goal() {
        with_instances_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let add_n = parse_goal(ctx, "Add N");
            let pi = mk_arrow_for_test(ctx, n, add_n);
            let k1 = ctx.normalize_goal_key(pi).expect("key");
            let k2 = ctx.normalize_goal_key(pi).expect("key");
            let k_body = ctx.normalize_goal_key(add_n).expect("key");
            assert_eq!(k1, k2);
            assert_ne!(k1, k_body);
        });
    }
```

Add to `instances.rs`'s test module. Copy the import/helper lines from the neighbouring `a_local_instances_synth_order_comes_from_its_instimplicit_binders` test (~:1492), which already builds a ctx with local instances.

```rust
    /// oracle: `getInstances` reads `localInstances` BEFORE its
    /// `forallTelescopeReducing` (SynthInstance.lean:203-205), so a goal's
    /// own instance binder is never a candidate.
    #[test]
    fn get_instances_ignores_the_goals_own_instance_binder() {
        with_instances_ctx(|ctx| {
            let add_n = parse_goal(ctx, "Add N");
            let base = Some(ctx.view.store);
            let pi = ctx
                .scratch
                .expr_forall(base, None, add_n, add_n, BinderInfo::InstImplicit)
                .expect("pi");
            let found = ctx.get_instances(pi).expect("get_instances");
            assert!(!found.is_empty(), "the global instAddN is still found");
            for i in &found {
                assert!(
                    !matches!(ctx.node(i.val), Node::FVar { .. }),
                    "the goal's own binder leaked in as a candidate"
                );
            }
        });
    }
```

If `Node::FVar`'s exact variant name differs, use the one `instances.rs` already matches on for local candidates (`grep -n "Node::FVar\|Node::Fvar" crates/leanr_meta/src/instances.rs`).

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test -p leanr_meta --lib -- preprocess_telescopes with_forall_telescope normalize_goal_key_handles get_instances_ignores`
Expected: compile error, because `with_forall_telescope` is not defined. After you add a stub `todo!()` body, `preprocess_telescopes_a_pi_shaped_goal` fails with `Unsupported`, and `get_instances_ignores_…` fails on the empty/garbled result for a pi goal.

- [ ] **Step 3: Implement `with_forall_telescope`** (in `synth.rs`, `impl<'e> MetaCtx<'e>`, above `preprocess`)

```rust
    /// oracle: `forallTelescope` / `forallTelescopeReducing`
    /// (`Lean/Meta/Basic.lean:1561`, `:1592`; worker
    /// `forallTelescopeReducingAuxAux`, `:1453`). Walk syntactic
    /// `forallE`s, pushing one local decl per binder; when the type stops
    /// being a forall and `reducing` is set, `whnf` once and continue if
    /// that exposed another forall. Then run `k(xs, body)`.
    ///
    /// `push_local_decl` installs an instance-implicit binder as a local
    /// instance, as the oracle's telescope does. The ambient
    /// `lctx`/`local_names`/`local_instances` are restored on EVERY exit
    /// path (`Ok` or `Err`), so no telescope fvar outlives `k`.
    pub(crate) fn with_forall_telescope<R>(
        &mut self,
        ty: ExprId,
        reducing: bool,
        k: impl FnOnce(&mut MetaCtx<'e>, &[ExprId], ExprId) -> Result<R, MetaError>,
    ) -> Result<R, MetaError> {
        let checkpoint = self.lctx_checkpoint();
        let result = (|| {
            let base = Some(self.view.store);
            let mut xs: Vec<ExprId> = Vec::new();
            // oracle `process`'s `j`: index into `xs` where the current
            // syntactic forall run started. Loose bvars in `cur` refer only
            // to `xs[j..]` (`instantiateRevRange j fvars.size fvars`).
            let mut j = 0usize;
            let mut cur = ty;
            loop {
                self.step()?;
                if let Node::Forall {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } = self.node(cur)
                {
                    let d = instantiate_rev(self.scratch, base, binder_type, &xs[j..], &mut self.guard)?;
                    let x = self.push_local_decl(binder_name, d, binder_info)?;
                    xs.push(x);
                    cur = body;
                    continue;
                }
                let t = instantiate_rev(self.scratch, base, cur, &xs[j..], &mut self.guard)?;
                if !reducing {
                    cur = t;
                    break;
                }
                let r = self.whnf(t)?;
                if matches!(self.node(r), Node::Forall { .. }) {
                    // Re-base: `r` is closed w.r.t. every fvar so far.
                    cur = r;
                    j = xs.len();
                    continue;
                }
                // oracle: `k fvars type` with the UN-whnf'd type (`process`'s `_` arm).
                cur = t;
                break;
            }
            k(self, &xs, cur)
        })();
        self.lctx_restore(checkpoint);
        result
    }
```

This mirrors `forall_meta_telescope_reducing` (~:2607-2645, `subst.clear()` = re-base) and leanr_elab's `open_forall_telescope_core` (`crates/leanr_elab/src/app/state.rs`). If `binder_name`'s type does not match `push_local_decl`'s `name: Option<NameId>`, adapt it at the call. Do not change `push_local_decl`.

- [ ] **Step 4: Port `preprocess`.** Replace the `Unsupported` arm and the classification prelude:

```rust
    fn preprocess(&mut self, ty: ExprId) -> Result<PreprocessResult, MetaError> {
        let ty = self.instantiate_mvars(ty)?;
        self.with_forall_telescope(ty, true, |ctx, xs, body| {
            let body = ctx.whnf(body)?;
            let ty = ctx.mk_forall(xs, body)?;
            ctx.preprocess_classify(ty, body)
        })
    }
```

Move the rest of today's function body (from the `!has_expr_mvar && !has_level_mvar` check down to the final `Ok`) into `fn preprocess_classify(&mut self, ty: ExprId, body: ExprId) -> Result<PreprocessResult, MetaError>`. Keep its comments, with one change: the `NoMVars` test reads `ty` (the oracle's `!type.hasMVar` on the rebuilt type, :743), and every head/arg inspection reads `body` (the oracle's `typeBody`). Every `return Ok(PreprocessResult { ty, .. })` returns the rebuilt `ty`. Rewrite the doc comment: drop the "telescope reduces to a whnf" and NAMED SEAM paragraphs, and cite `:737-773` after opening it. `mk_forall(&[], body)` must equal `body` for the `xs = []` case. Assert this in a `debug_assert!` the first time you run the tests. If it does not hold, special-case `xs.is_empty()`.

The oracle also rebuilds a normalized `cacheKeyType` (:752-772). leanr computes its key separately (`normalize_goal_key`), and `PreprocessResult` has no key field. Check with `grep -n "cache_key\|cacheKey" crates/leanr_meta/src/synth.rs`. If there is no such field, write nothing for it and say so in the doc comment.

- [ ] **Step 5: Port `preprocess_out_param`** (oracle `:775-818`, NON-reducing):

```rust
    fn preprocess_out_param(&mut self, ty: ExprId) -> Result<ExprId, MetaError> {
        self.with_forall_telescope(ty, false, |ctx, xs, body| {
            match ctx.preprocess_out_param_body(body)? {
                None => Ok(ty),
                Some(new_body) => ctx.mk_forall(xs, new_body),
            }
        })
    }
```

Rename today's body to `preprocess_out_param_body(&mut self, ty) -> Result<Option<ExprId>, MetaError>`. Each early `return Ok(ty)` (not a const head, `head == ty`, no out params) becomes `return Ok(None)`, and each rebuilt result becomes `Ok(Some(..))`. This is the oracle's "return the original `type`" on the early arms. Remove the doc sentence "leanr's goals are binder-free … no telescope to open".

- [ ] **Step 6: Port `get_instances`** (`instances.rs`). Snapshot the locals before the telescope, then run the existing body on the telescope's body:

```rust
    pub(crate) fn get_instances(&mut self, goal: ExprId) -> Result<Vec<Instance>, MetaError> {
        // oracle: `getInstances` (SynthInstance.lean:202-243) reads
        // `localInstances` BEFORE `forallTelescopeReducing` (:203-205),
        // so the goal's own instance binders are never candidates.
        let local_insts = self.local_instances.to_vec();
        self.with_forall_telescope(goal, true, |ctx, _xs, body| {
            ctx.get_instances_for_class_app(body, &local_insts)
        })
    }
```

Move today's body into `fn get_instances_for_class_app(&mut self, goal: ExprId, local_insts: &[LocalInstance]) -> Result<Vec<Instance>, MetaError>`, and replace `for li in self.local_instances.to_vec()` with `for li in local_insts.iter().cloned()`. Use the element type that `local_instances.to_vec()` returns. Keep the existing comments, and delete the sentence "this takes an ALREADY-telescoped class application, so there is no `forallTelescopeReducing` here — and hence no need for the oracle's own ... precaution". Update the module doc at ~:103 to match. The `local_instance_candidate` call stays inside the telescope; its own nested checkpoint/restore is fine.

- [ ] **Step 7: Run the tests to verify they pass**

Run: `cargo test -p leanr_meta --lib`
Expected: all pass, including the 5 new tests. Then run `cargo test -p leanr_meta --test oracle_synth --test oracle_fast`. Expected: PASS with 30 compared records. The binder-free behaviour is unchanged.

The `try_resolve` seam is still in place, so a pi goal reaching the generator still errors. That is Task 2.

- [ ] **Step 8: Run the mutations** (apply, run, observe FAIL, revert, one at a time):
  - (1a) In `with_forall_telescope`, drop the `lctx_restore` on the `Err` path (restore only on `Ok`). `with_forall_telescope_restores_on_err` must fail.
  - (1b) In `get_instances`, take the snapshot inside the closure. `get_instances_ignores_the_goals_own_instance_binder` must fail.
  - (1c) In `preprocess`, use `with_forall_telescope(ty, false, ..)`. Record that no unit test kills it; Task 3's `piReducible` row is the killer. Re-check it there.

- [ ] **Step 9: Commit**

```bash
cargo fmt --all && cargo clippy -p leanr_meta --all-targets -- -D warnings
git add crates/leanr_meta/src/synth.rs crates/leanr_meta/src/instances.rs
git commit -m "leanr_meta: forall telescope in synth preprocess/preprocessOutParam/getInstances"
```

---

### Task 2: `get_subgoals` over `xs`, `try_resolve` telescope, the `consume` seam doc

**Files:**
- Modify: `crates/leanr_meta/src/synth.rs`: `try_resolve` (~:2448-2531), `get_subgoals` (~:2533-2580), the `consume` doc (~:2741-2775), and new tests.

**Interfaces:**
- Consumes: `with_forall_telescope` (Task 1); `mk_aux_mvar_at(lctx: Arc<LocalCtxSnapshot>, ty, MVarKind::Natural, None) -> Result<(ExprId, MVarId), MetaError>` (`assign.rs:739`); `current_lctx() -> Arc<LocalCtxSnapshot>`; `mk_forall`; `mk_lambda_eta(fvars, body)` (`metactx.rs:1263`); `mk_app_spine(f, args)`.
- Produces: `fn get_subgoals(&mut self, outer: Arc<LocalCtxSnapshot>, xs: &[ExprId], inst: &Instance) -> Result<(Vec<ExprId>, ExprId, ExprId), MetaError>`. It has the same return triple as today: (binder mvars in order, instVal, instTypeBody).

- [ ] **Step 1: Write the failing tests**

```rust
    /// A root pi goal: `N → Add N` answers `fun _ => instAddN`
    /// (`mkLambdaFVars xs instVal (etaReduce := true)`, :374; the body
    /// does not mention `x`, so no eta step fires).
    #[test]
    fn synth_answers_a_pi_goal() {
        with_instances_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let add_n = parse_goal(ctx, "Add N");
            let pi = mk_arrow_for_test(ctx, n, add_n);
            let v = ctx.synth_instance(pi).expect("no error").expect("answered");
            let v = ctx.instantiate_mvars(v).expect("inst");
            let Node::Lam { binder_type, body, .. } = ctx.node(v) else {
                panic!("expected a lambda, got {}", render_expr(ctx, v));
            };
            assert_eq!(binder_type, n);
            assert_eq!(body, const_named(ctx, "instAddN"));
        });
    }

    /// Review Focus 1: the outer snapshot carries the ambient local
    /// instance into the telescope (oracle `getSubgoals`' `localInsts`,
    /// :317; `getInstances`' locals, :236-239).
    #[test]
    fn pi_goal_uses_an_ambient_local_instance() {
        with_instances_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let add_n = parse_goal(ctx, "Add N");
            let cp = ctx.lctx_checkpoint();
            let h = ctx
                .push_local_decl(None, add_n, BinderInfo::InstImplicit)
                .expect("h");
            let pi = mk_arrow_for_test(ctx, n, add_n);
            let v = ctx.synth_instance(pi).expect("no error").expect("answered");
            let v = ctx.instantiate_mvars(v).expect("inst");
            let Node::Lam { body, .. } = ctx.node(v) else {
                panic!("expected a lambda, got {}", render_expr(ctx, v));
            };
            assert_eq!(body, h, "local instance beats the global");
            ctx.lctx_restore(cp);
        });
    }

    /// Review Focus 4: a pi goal whose body has an expr mvar takes the
    /// `isDefEq mvar instVal` recheck path (:417) with a pi-typed mvar.
    #[test]
    fn pi_goal_with_mvar_body_does_not_error() {
        with_instances_ctx(|ctx| {
            let n = const_named(ctx, "N");
            let ty = type_sort(ctx);
            let a = fresh_mvar(ctx, ty);
            let add = const_named(ctx, "Add");
            let base = Some(ctx.view.store);
            let add_a = ctx.scratch.expr_app(base, add, a).expect("Add ?a");
            let pi = mk_arrow_for_test(ctx, n, add_a);
            ctx.synth_instance(pi).expect("Ok(_), not Err");
        });
    }
```

Check the `Node::Lam` field names in `crates/leanr_kernel/src/bank/terms.rs` (they mirror `Forall`: `binder_name, binder_type, body, binder_info`). Check `synth_instance`'s exact public name and return type with `grep -n "pub fn synth_instance" crates/leanr_meta/src/synth.rs`, and adapt the calls.

- [ ] **Step 2: Run the tests to verify they fail**

Run: `cargo test -p leanr_meta --lib -- synth_answers_a_pi_goal pi_goal_`
Expected: FAIL with `Unsupported("synth.rs::try_resolve: forall-shaped synthesis goal …")`.

- [ ] **Step 3: Rewrite `get_subgoals`** (oracle `:317-339`). It replaces the call to `forall_meta_telescope_reducing`, which stays as is for its leanr_elab caller:

```rust
    #[allow(clippy::type_complexity)]
    fn get_subgoals(
        &mut self,
        outer: Arc<LocalCtxSnapshot>,
        xs: &[ExprId],
        inst: &Instance,
    ) -> Result<(Vec<ExprId>, ExprId, ExprId), MetaError> {
        let base = Some(self.view.store);
        let mut inst_val = self.mk_const_with_fresh_mvar_levels(inst.val)?;
        let mut inst_type = self.infer_type(inst_val)?;
        let mut mvars: Vec<ExprId> = Vec::new();
        let mut subst: Vec<ExprId> = Vec::new();
        loop {
            self.step()?;
            if let Node::Forall { binder_type, body, .. } = self.node(inst_type) {
                let d = instantiate_rev(self.scratch, base, binder_type, &subst, &mut self.guard)?;
                // oracle :325 — `mkFreshExprMVarAt lctx localInsts (← mkForallFVars xs d)`.
                let m_ty = if xs.is_empty() { d } else { self.mk_forall(xs, d)? };
                let (m, _) = self.mk_aux_mvar_at(Arc::clone(&outer), m_ty, MVarKind::Natural, None)?;
                let arg = self.mk_app_spine(m, xs)?;
                subst.push(arg);
                inst_val = self.scratch.expr_app(base, inst_val, arg)?;
                inst_type = body;
                mvars.push(m);
            } else {
                let t = instantiate_rev(self.scratch, base, inst_type, &subst, &mut self.guard)?;
                inst_type = self.whnf(t)?;
                inst_val = instantiate_rev(self.scratch, base, inst_val, &subst, &mut self.guard)?;
                subst.clear();
                if !matches!(self.node(inst_type), Node::Forall { .. }) {
                    break;
                }
            }
        }
        let inst_val = instantiate_rev(self.scratch, base, inst_val, &subst, &mut self.guard)?;
        let body = instantiate_rev(self.scratch, base, inst_type, &subst, &mut self.guard)?;
        Ok((mvars, inst_val, body))
    }
```

`inst_val` holds no loose bvars (every `arg` is closed), so the `instantiate_rev` calls on it are no-ops kept for fidelity. Drop them if clippy or review prefers. The `xs = []` path: `mk_aux_mvar_at(current_lctx(), d, Natural, None)` is `mk_aux_mvar(d)`. Confirm that by reading `mk_aux_mvar` (`assign.rs`). If its kind or lctx differ, the binder-free path changes, so STOP and report. Keep the `get_subgoals` doc's level-refresh HARD REQUIREMENT paragraph. Replace the "specialized to the `xs = #[]` case" paragraph with the oracle's two invariants (`:308-309`, opened).

- [ ] **Step 4: Rewrite `try_resolve`** (oracle `:346-419`):

```rust
    fn try_resolve(
        &mut self,
        mvar: ExprId,
        inst: &Instance,
    ) -> Result<Option<(MetaSnapshot, Vec<ExprId>)>, MetaError> {
        let mvar_type = self.infer_type(mvar)?;
        let mvar_type = self.instantiate_mvars(mvar_type)?;
        // oracle :350-353 — capture `lctx`/`localInsts` BEFORE the telescope.
        let outer = self.current_lctx();
        self.with_forall_telescope(mvar_type, true, |ctx, xs, body| {
            let (mvars, inst_val, inst_type_body) = ctx.get_subgoals(outer, xs, inst)?;
            let mut subgoals = Vec::with_capacity(inst.synth_order.len());
            for &i in &inst.synth_order {
                match mvars.get(i) {
                    Some(&m) => subgoals.push(m),
                    None => return Ok(None),
                }
            }
            if !ctx.is_def_eq(body, inst_type_body)? {
                return Ok(None);
            }
            // oracle :374 — `mkLambdaFVars xs instVal (etaReduce := true)`.
            let inst_val = if xs.is_empty() { inst_val } else { ctx.mk_lambda_eta(xs, inst_val)? };
            let goal_body = ctx.instantiate_mvars(body)?;
            if !ctx.data(goal_body).has_expr_mvar() {
                let Node::MVar { id: Some(id) } = ctx.node(mvar) else {
                    return Err(MetaError::MVar(
                        "try_resolve: goal is not a metavariable reference".into(),
                    ));
                };
                ctx.mctx.assign(MVarId(id), inst_val)?;
            } else if !ctx.is_def_eq(mvar, inst_val)? {
                return Ok(None);
            }
            // oracle :418 — `getMCtx` inside the telescope; the subgoal
            // decls' lctx is `outer`, so nothing dangles after restore.
            Ok(Some((ctx.checkpoint(), subgoals)))
        })
    }
```

Keep the existing comments on `synth_order` and the direct-assign/recheck split, and move them into the closure. Rewrite the doc. The NAMED SEAM and BLAST RADIUS paragraphs go. Cite `:346-419`, `:353`, `:374` and `:412-418` after opening them. Check whether `checkpoint()` snapshots `lctx`. If it does (`grep -n "pub(crate) fn checkpoint\|fn rollback" crates/leanr_meta/src/*.rs`), a later `rollback` to it would re-install the telescope fvars. In that case, take the checkpoint's mctx part only, or restore lctx to `outer` before taking it. Write down which you did and why in the doc.

- [ ] **Step 5: Update the `consume` doc** (`removeUnusedArguments?` NAMED SEAM). Replace "unreachable here rather than silently skipped" with: reachable now. leanr tables `A → C` (unused `A`) under the arrow and resolves it through `try_resolve`'s telescope, giving `fun _ => inst`. The oracle tables the stripped `C` and transports with its transformer (`:529`), giving the same term. This is answer-neutral, pinned by `piUnused/synth/0` (Task 3). Open `:486-531` and `:558` before citing them.

- [ ] **Step 6: Run the tests to verify they pass**

Run: `cargo test -p leanr_meta --lib && cargo test -p leanr_meta --test oracle_synth --test oracle_fast`
Expected: all pass, oracle_synth still at 30 compared.

- [ ] **Step 7: Run the mutations** (apply, run, observe FAIL, revert):
  - (2a) `mk_lambda` instead of `mk_lambda_eta`. Record that no unit test kills it; Task 3's `piEta` row must.
  - (2b) Mint with `self.mk_aux_mvar(d)` (ambient lctx, not `∀ xs`, not applied to `xs`). Expect `synth_answers_a_pi_goal` or a corpus row to fail. Record which one; Task 3's `piApplied` must kill it at the latest.
  - (2c) Capture `outer` inside the closure. Record the result; Task 3 rows re-check it.

- [ ] **Step 8: Commit**

```bash
cargo fmt --all && cargo clippy -p leanr_meta --all-targets -- -D warnings
git add crates/leanr_meta/src/synth.rs
git commit -m "leanr_meta: synth pi-goals in tryResolve/getSubgoals (forallTelescopeReducing + mkLambdaFVars etaReduce)"
```

---

### Task 3: Synth0 pi-goal oracle rows

**Files:**
- Modify: `tests/fixtures/meta/Synth0.lean` (append), `tests/fixtures/meta/dump_synth.lean` (`synthQueries`, ~:446-540, plus a header note), and `crates/leanr_meta/tests/oracle_synth.rs` (compared count 30 → 30 + new rows).
- Regenerate: `tests/fixtures/meta/Synth0.olean`, `tests/fixtures/meta/synth-queries.jsonl`.

- [ ] **Step 1: Append the family to `Synth0.lean`** (after the last declaration). `N`, `N.zero`, `Pri`, `NoInst` and `Eq` already exist:

```lean
-- === synth pi-goals slice (spec 2026-10-02-synth-pi-goals-design.md) ===
-- Goals of the form `∀ xs, C ..` (SynthInstance.lean forallTelescopeReducing sites).
class Dec (p : Prop) where dec : N
instance instDecN (a b : N) : Dec (Eq a b) := ⟨N.zero⟩
abbrev DecEqN (α : Type) := (a b : α) → Dec (Eq a b)
class BE (α : Type) where be : N
instance instBEOfDecEq [DecEqN α] : BE α := ⟨N.zero⟩
class PB (α : Type) where pb : N
instance (priority := 100) instPBLow : PB N := ⟨N.zero⟩
instance (priority := 5000) instPBHigh [(x : N) → CoeT N x NoBase] : PB N := ⟨N.zero⟩
```

If prelude-mode rejects any line (auto-bound `α`, the anonymous constructor), fix it minimally, e.g. `{α : Type}`, or `{ dec := N.zero }`. Keep the names.

- [ ] **Step 2: Add the queries to `synthQueries`** (append before the closing `]`). `nTy`, `cls1` and `type0` exist. `Dec` is `Prop → Type`, so build its application with `mkApp (mkConst `Dec) ..` (no universe):

```lean
  -- === synth pi-goals slice ===
  , (`piRoot, 0, [], do
      withLocalDeclD `a nTy fun a => withLocalDeclD `b nTy fun b =>
        mkForallFVars #[a, b] (mkApp (mkConst `Dec) (← mkEq a b)))
  , (`piReducible, 0, [], pure (mkApp (mkConst `DecEqN) nTy))
  , (`piApplied, 0, [], do
      withLocalDeclD `a nTy fun a =>
        mkForallFVars #[a] (mkApp (mkConst `Dec) (← mkEq a (mkConst `N.zero))))
  , (`piNested, 0, [], pure (mkApp (mkConst `BE) nTy))
  , (`piUnused, 0, [], pure (mkForall `x BinderInfo.default nTy (cls1 `Pri nTy)))
  , (`piInstBinder, 0, [], pure (mkForall `h BinderInfo.instImplicit (cls1 `NoInst nTy) (cls1 `NoInst nTy)))
  , (`piBranch, 0, [], pure (mkApp (mkConst `PB) nTy))
```

`mkEq` needs `Eq`'s universe and works in prelude mode, since it only builds `@Eq.{1} N a b`. If `mkEq` cannot be resolved, build the term by hand: `mkApp3 (mkConst `Eq [Level.one]) nTy a b`. `piEta` is not a separate row: `piRoot`'s canonical `val` (`instDecN` vs `fun a b => instDecN a b`) already discriminates eta. Confirm this in Step 4 and say so in the header note. Add a header comment block naming, for each row, the mutation it kills (copy the spec § Testing table).

- [ ] **Step 3: Regenerate**

Run: `mise run fixtures:regen`. If that is too broad, run just the two Synth0 lines from `mise.toml` (:152-153):
```bash
(cd tests/fixtures/meta && lean Synth0.lean -o Synth0.olean && LEAN_PATH=$PWD lean --run dump_synth.lean > synth-queries.jsonl)
```
Expected: `git diff --stat tests/fixtures/meta/synth-queries.jsonl` shows ONLY 7 added lines. If any existing record moved, STOP and report.

- [ ] **Step 4: Read the oracle verdicts**

```bash
grep '"id":"pi' tests/fixtures/meta/synth-queries.jsonl | jq -c '{id, ok, near_budget, val}'
```
Check these expectations, and report any that do not match before continuing:
- `piRoot` is ok with `val` = const `instDecN`.
- `piReducible` is ok.
- `piApplied` is ok with a `lam` value.
- `piNested` is ok.
- `piUnused` is ok with `fun x => instPriHigh`.
- `piInstBinder`: whatever the oracle says. Expect `ok:false` per spec § Design 3.
- `piBranch` is ok with `instPBLow`.

Every record must have `near_budget:false`. **If `piUnused`'s term is not `fun _ => instPriHigh`-shaped, STOP.** The `removeUnusedArguments?` neutrality claim is then false, and per the spec the slice re-scopes with the user.

- [ ] **Step 5: Bump the gate count** in `oracle_synth.rs` from 30 to 37, and extend the message: "synth pi-goals task 3 added the seven `pi*` records".

- [ ] **Step 6: Run the gate**

Run: `cargo test -p leanr_meta --test oracle_synth`
Expected: PASS, 37 compared. On a divergence, debug it (superpowers:systematic-debugging) before touching the fixture.

- [ ] **Step 7: Run the mutations against the gate** (apply in `synth.rs`/`instances.rs`, run `oracle_synth`, observe the named record diverge, revert):

| mutation | expected killer |
|---|---|
| (1c) `preprocess` uses a non-reducing telescope | `piReducible/synth/0` |
| (1b) `get_instances` snapshots locals inside the telescope | `piInstBinder/synth/0` |
| (2a) `mk_lambda` for `mk_lambda_eta` | `piRoot/synth/0` |
| (2b) mint `?m : d` at ambient, not applied to `xs` | `piApplied/synth/0` |
| (2c) `outer` captured inside the telescope | record the result |
| restore the `try_resolve` `Unsupported` seam | `piNested/synth/0` and `piBranch/synth/0` (error vs answer) |
| `try_resolve` returns `Err` instead of `Ok(None)` when `is_def_eq(body, …)` fails under a non-empty `xs` | `piBranch/synth/0` |

Put every surviving mutation in the commit message with the reason it is unobservable.

- [ ] **Step 8: Commit**

```bash
cargo fmt --all && cargo clippy -p leanr_meta --all-targets -- -D warnings
git add tests/fixtures/meta/Synth0.lean tests/fixtures/meta/Synth0.olean tests/fixtures/meta/dump_synth.lean tests/fixtures/meta/synth-queries.jsonl crates/leanr_meta/tests/oracle_synth.rs
git commit -m "tests: synth pi-goal oracle rows (Synth0 piRoot..piBranch)"
```

---

### Task 4: ElabOp drops `BEq Bool`; elab pi rows; doc and spec ledger

**Files:**
- Modify: `tests/fixtures/elab/elab_op_support.lean.in` (:69-70), `tests/fixtures/elab/dump_elab.lean` (op row list, near `meta/eta-*` ~:1318), `crates/leanr_elab/tests/oracle_op.rs` (`CORPUS_FLOOR` :177 and its comment; the suffix-gate comment :284).
- Regenerate: `tests/fixtures/elab/ElabOp.lean`, `ElabOp.olean`, `op-expansions.jsonl`, `op-queries.jsonl`.
- Modify (docs): any remaining hit of `grep -rn "pi-shaped\|forall-shaped\|forallTelescope" crates/leanr_meta crates/leanr_elab`, including `MetaError::Unsupported`'s doc and `crates/leanr_meta/src/lib.rs`.
- Modify (specs): `docs/superpowers/specs/2026-10-01-macro-expansion-binop-design.md` (§ Landed › P3: the R5 bullet ~:698 and the pi-goal bullet ~:730); `docs/superpowers/specs/2026-10-02-check-assignment-ctx-approx-design.md` (§ Landed › Eta follow-up, ~:535); `docs/superpowers/specs/2026-10-02-synth-pi-goals-design.md` (§ Landed).

- [ ] **Step 1: Delete the suffix instance.** In `elab_op_support.lean.in`, delete these lines:
```lean
-- Closed `BEq Bool` (P3 T4): leanr's synth_instance lacks pi-shaped goals (`DecidableEq Bool`, SynthInstance.lean:740-742).
instance : BEq Bool := ⟨fun _ b => b⟩
```

- [ ] **Step 2: Add the elab rows** to `dump_elab.lean`, after the `meta/eta-*` block:
```lean
  -- synth pi-goals slice: Prelude's `instBEqOfDecidableEq` needs the pi
  -- subgoal `DecidableEq α` (SynthInstance.lean forallTelescopeReducing).
  , ("meta/synth-pi-beq-nat",    "(inferInstance : BEq Nat)")
  , ("meta/synth-pi-deceq-nat",  "(inferInstance : DecidableEq Nat)")
  , ("meta/synth-pi-beq-bool",   "(inferInstance : BEq Bool)")
```

- [ ] **Step 3: Regenerate**

Run: `mise run fixtures:regen-elab-op`
Expected: success, including the `op-expansions` drift-guard diff. Then:
```bash
git diff -U0 tests/fixtures/elab/op-queries.jsonl | grep '^[-+]{' | jq -rc '.id' | sort | uniq -c
```
Expected: exactly `op/beq-prop`, `op/bne-prop` and `op/beq-prop-bool` changed (each shows a - and a +), plus 3 added `meta/synth-pi-*`. Their new terms mention `instBEqOfDecidableEq`. Any other moved id: STOP and report it (spec § Testing: no silent re-blessing).

- [ ] **Step 4: Run the elab gates**

Run: `cargo test -p leanr_elab --test oracle_op`
Expected: PASS with 97 replayed records. Set `CORPUS_FLOOR` to 97 and extend its comment: "94 -> 97 (synth pi-goals T4): meta/synth-pi-{beq-nat,deceq-nat,beq-bool}; op/beq-prop, op/bne-prop, op/beq-prop-bool re-recorded against instBEqOfDecidableEq (suffix `BEq Bool` dropped)". In `elab_op_has_the_test_support_suffix`, change the `(inferInstance : BEq Bool)` comment to: "Prelude's `BEq Bool` through `instBEqOfDecidableEq`, a pi subgoal (synth pi-goals slice)". Then run all of leanr_elab's tests: `cargo test -p leanr_elab`. Expected: PASS.

- [ ] **Step 5: Run the mutation.** Restore the `try_resolve` `Unsupported` seam. `oracle_op` must fail on the three re-recorded rows and the three new rows. Revert.

- [ ] **Step 6: Sweep the docs.** Run `grep -rn "pi-shaped\|forall-shaped\|forallTelescope\|no Meta-layer fvar" crates/leanr_meta crates/leanr_elab`. Rewrite or remove every comment that still describes the closed seams, and open each oracle cite you write. Leave the comments that correctly describe leanr_elab's own telescope.

- [ ] **Step 7: Update the spec ledgers**
  - macro/binop% spec: strike through the "synth pi-goal gap" bullet: `~~…~~ CLOSED [synth pi-goals slice: 2026-10-02-synth-pi-goals-design.md § Landed]`. Append "Reverted [synth pi-goals slice]: the suffix no longer declares `BEq Bool`; the three rows pin `instBEqOfDecidableEq`" to R5.
  - checkAssignment spec ~:535: mark the `try_resolve … mk_lambda_eta` follow-up CLOSED the same way.
  - synth pi-goals spec § Landed: list the commits, the corpus counts (synth 30→37, op 94→97), the mutation table with each killer record and any survivors, the `piUnused`/`piInstBinder` oracle verdicts as observed, and the open follow-ups: approach B (shared meta/elab telescope), synthesis onto real depth, the `removeUnusedArguments?` port, and the `get_instances` non-class divergence.

- [ ] **Step 8: Run full CI in the foreground**

Run: `mise run ci; echo CI_EXIT=$?`
Expected: `CI_EXIT=0`.

- [ ] **Step 9: Commit**

```bash
git add tests/fixtures/elab crates/leanr_elab/tests/oracle_op.rs crates/leanr_meta crates/leanr_elab docs/superpowers/specs
git commit -m "leanr_elab: drop ElabOp's BEq Bool suffix; synth pi-goal elab rows; close the pi-goal seams in the spec ledgers"
```
