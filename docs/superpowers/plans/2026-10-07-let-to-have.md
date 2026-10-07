# letToHave Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A `let` in a definition's type or value reaches the kernel with the oracle's `nondep` flag. This plan ports `Meta.letToHave`, adds the `abstractNestedProofs` let arm it depends on, and deletes the `letToHave` seam.

**Architecture:**
- `leanr_meta` gains zeta-delta tracking: two `MetaCtx` fields, the record in whnf's let-fvar arm, a snapshot field, and a fresh-cache scope.
- `leanr_meta` gains a new `let_to_have.rs`, a faithful port of `Lean/Meta/LetToHave.lean`.
- `abstract_proofs.rs` gets the `letE` arm of `AbstractNestedProofs.visit`, which today is a seam.
- `leanr_elab/src/command/def.rs` replaces `reject_let` with the oracle's `letToHaveType` and `letToHaveValue` gates, after `abstractNestedProofs`.

**Tech Stack:** Rust (leanr workspace), the Lean v4.33.0-rc1 oracle (`dump_decls.lean files`), cargo tests, and `mise` tasks.

**Spec:** `docs/superpowers/specs/2026-10-07-let-to-have-design.md`, commit 7f04f0d on branch `d-let-to-have`. Read it first. This plan overrides it in the places listed under "Plan-time findings" below.

## Global Constraints

- `leanr_kernel` is untouched (TCB). Everything new lives in `leanr_meta` and `leanr_elab`; additive `leanr_meta` state follows the M4b accessor precedent.
- No new dependencies.
- Every cargo run looks like `export CARGO_TARGET_DIR=/workspace/target/wt-d; ( ulimit -v 16000000; CARGO_BUILD_JOBS=6 timeout 1500 cargo test … )`. Run it in the foreground, one at a time. Never build under `/tmp`.
- Run `cargo fmt --all` before every commit.
- **Mutation testing is required.** Each task's mutations are RUN, reverted, and recorded in the commit body as "mutation → which tests fail". An equivalent mutation is recorded with its reason. Afterwards grep for leftovers (`if false &&`, `// MUT`).
- Oracle cites: open the line before you write it into a comment. This project's cites drift by 1–2 lines.
- **Full CI, serialized and blocking in the same turn:**
  `( flock /workspace/target/ci.lock sh -c 'export CARGO_TARGET_DIR=/workspace/target/wt-d; ulimit -v 16000000; CARGO_BUILD_JOBS=6 mise run ci'; echo "CI_EXIT=$?" ) > /workspace/target/wt-d-ci.log 2>&1`
  Never end a turn before reading `CI_EXIT`.
- **Before Task 1, rebase `d-let-to-have` on `origin/main`.** Worktrees A, C and B land first and each appends its own fileQueries block. Recompute `CORPUS_FLOOR` from the rebased `file-queries.jsonl`; don't trust any number in this plan.

## Plan-time findings (these override the spec)

1. **`abstractNestedProofs` returns `Unsupported` on every `letE`** (`abstract_proofs.rs:363-367`, "abstractNestedProofs under let — letToHave follow-up"). The spec missed this because `reject_let` runs first. Every def, abbrev or opaque value with a `let` reaches it. Task 3 ports the oracle's `letE` arm: `AbstractNestedProofs.lean:101`, `lambdaLetTelescope` + `visitBinders` (`:77-89`, which visits let VALUES too, `:85-86`) + `mkLambdaFVars (usedLetOnly := false) (generalizeNondepLet := false)`.
2. **Pending aux constants.** After abstraction, `letToHave`'s check mode runs `visitConst` on `d._proof_N` (`LetToHave.lean:201-208`), which leanr has not yet added to the env. That is the P1 pending-aux seam. Every proof abstracted under a genuine `let` therefore raises the existing seam message, unless a pending-constant overlay exists, and that overlay is out of scope. Rows `auxProofLet`, `auxProofLetDep` and `auxProofLetDepOnly` (oracle: H, H, L) become seam unit tests, not corpus rows. `auxProofLetDep` is also what kills the "letToHave before abstraction" mutation: under the wrong order it elaborates to `Ok`.
3. **Zeta-delta records are backtrackable.** The oracle's `SavedState.restore` restores `zetaDeltaFVarIds` (`Meta/Basic.lean:596`), so a failed `isDefEq` (`checkpointDefEq`, `:2463-2468`) drops what it recorded. `withNewMCtxDepthImp` (`:1974-1980`) does NOT restore it. leanr's `MetaSnapshot` gets the set, and `with_new_mctx_depth` keeps it across its rollback.
4. **The fresh-cache scope is most likely equivalent in leanr.**
   - Every leanr whnf/whnf_core/infer cache entry is fvar-free (`cacheable`, `metactx.rs:1776-1779`). An expression whose reduction follows a let-fvar mentions that fvar, so it is never cached.
   - Top-level `is_def_eq` clears both defeq caches (`defeq.rs:97-98`).
   - The scope is ported anyway, for oracle fidelity and to stay safe if caching is relaxed later. Its mutation is run and recorded, and it is expected to be equivalent.
5. **The async theorem header pass is unobservable in leanr.**
   - `check_async_signature` (`def.rs:231-253`) returns only level params. letToHave changes no level params, and the theorem's committed type comes from the main path, which runs the type pass.
   - So `def.rs:250-251` just loses its `reject_let`. A comment records why there's no call there. Spec § Components 3's "async header runs the type pass" is not ported.
6. **Audit result (spec § Component 1): no fixes needed.** The oracle records zeta-delta in exactly two places: `WHNF.lean:408` (`whnfEasyCases`) and `LetToHave.lean:164-181` (`visitDepExpr`). `Closure.lean:290` READS the set, but only in `zetaDelta := false` mode, which leanr doesn't port. Ruling table:

| leanr site | follows a let value? | oracle counterpart | records? | action |
|---|---|---|---|---|
| `whnf.rs:248-268` easy-cases `FVar` arm | yes | `whnfEasyCases` `WHNF.lean:397-409` | **yes, `:408`** | add the record (Task 2) |
| `assign.rs:966-984` `simp_assignment_arg_aux` | yes | `simpAssignmentArgAux` `ExprDefEq.lean:1226-1235` (`getValue?`) | no | none |
| `assign.rs:1071` `mk_lambda_fvars_with_let_deps` | no (is-let test) | `hasLetDeclsInBetween` | no | none |
| `check_assignment.rs:105` | no (is-let test) | `checkFVar` `ExprDefEq.lean:851-878` | no | none |
| `check_assignment.rs:302` `ca_check_fvar` | yes | `checkFVar` `:873` (`check v`) | no | none |
| `check_assignment.rs:394` | no (dependency test) | `localDeclDependsOn` | no | none |
| `transform.rs:119` `zeta_reduce` | yes | `Meta.zetaReduce` `Transform.lean:198-209` (`decl.value?`) | no | none |
| `closure.rs:281` | yes (`zetaDelta := true`) | `Closure.lean:237-243` (`getValue?`) | no | none |
| `infer.rs:799`, `mk_binding.rs:224/822`, `metactx.rs:1243/1413` | no (rebuild/copy) | `mkBinding` | no | none |

7. **Corpus: 42 rows.** All were re-probed in `/workspace/target/designDplan/`: `final_rows.txt`, `final_expected.txt`, `oracle.jsonl`, plus `show.py` for the H/L summary. That is 28 from the design probe (minus `lth/instance`) and 14 new ones. 4 probed rows are excluded: 3 pending seams and `auxProofNoLet`, which needs no let.

## Review Focus

1. **A deep `let` chain** (thousands of nested lets) must return `Ok` or `DepthBudgetExhausted`, never overflow the stack. Every recursive visit goes through `guarded`. Test: Task 4, `a_deep_let_chain_never_overflows`.
2. **An error inside the tracking scope**, such as the pending seam or a type error, must restore `track_zeta_delta`, the set and every cache, because overload stages and retries catch errors. Test: Task 2, `tracking_scope_restores_on_err`.
3. **A value with only `have`s (no genuine let)** must come back as the SAME `ExprId`, with no re-interning, the way the oracle's `hasDepLet` early exit does (`:420`). Test: Task 4, `no_dependent_let_is_the_identity`.
4. **A `let` whose value is visited with check off and later reused from the cache under check on** must not be re-checked, faithful to `checkCache` (`:137-148`). Test: Task 4, `cached_unchecked_subterm_is_not_rechecked`.
5. **A `have` must never be recorded**, even under tracking. A recorded `have` would leave a dependent-looking set but no visible change; the guard is the whnf arm's `!e.nondep` filter. Test: Task 2, `tracking_records_a_let_never_a_have`.

---

## File Structure

| File | Responsibility | Task |
|---|---|---|
| `tests/fixtures/elab/dump_decls.lean` | append the `-- worktree D: letToHave` fileQueries block | 1 |
| `tests/fixtures/elab/file-queries.jsonl` | regenerated oracle records | 1 |
| `crates/leanr_elab/tests/oracle_file.rs` | `PENDING` (Task 1 adds `lth/`, Task 5 removes it), `CORPUS_FLOOR` | 1, 5 |
| `crates/leanr_meta/src/metactx.rs` | new fields, snapshot field, `with_fresh_cache`, `with_tracking_zeta_delta`, `zeta_delta_fvar_ids()`, `with_infer_type_config`, `mk_lambda_let_fvars`; the `with_new_mctx_depth` carve-out | 2, 3 |
| `crates/leanr_meta/src/whnf.rs` | record at the easy-cases `FVar` arm; module-doc seam line | 2 |
| `crates/leanr_meta/src/abstract_proofs.rs` | `letE` arm in `anp_visit` / `anp_visit_binders`; `pending_lookup_seam` takes `who` | 3 |
| `crates/leanr_meta/src/let_to_have.rs` (new) | the `LetToHave.lean` port | 4 |
| `crates/leanr_meta/src/lib.rs` | `mod let_to_have;` | 4 |
| `crates/leanr_elab/src/command/def.rs` | gates replace `reject_let`; the call follows abstraction | 5 |
| `crates/leanr_elab/tests/oracle_decl.rs`, `crates/leanr_elab/tests/seam_audit.rs` | the seam tests become admission and pending-seam tests | 5 |
| `docs/superpowers/specs/2026-10-07-let-to-have-design.md` | § Plan amendments + § Landed | 6 |

---

### Task 1: Stage the corpus rows (red, gated as PENDING)

**Files:**
- Modify: `tests/fixtures/elab/dump_decls.lean` (end of `fileQueries`, currently `:721`; after the rebase, the end of whatever list is there)
- Modify: `tests/fixtures/elab/file-queries.jsonl` (regenerated)
- Modify: `crates/leanr_elab/tests/oracle_file.rs` (`PENDING`, `CORPUS_FLOOR`)

**Interfaces:** Consumes nothing. Produces the 42 `lth/*` records that Task 5 un-pends.

- [ ] **Step 1: Rebase and record the floor**

```bash
git fetch origin && git rebase origin/main
wc -l tests/fixtures/elab/file-queries.jsonl   # = N_before
```

- [ ] **Step 2: Append the block.** Add a trailing comma to the current last entry, then append these lines before the closing `]`. Leave the last row without a comma.

```lean
  -- worktree D: letToHave (nondependent `let` → `have`; spec 2026-10-07-let-to-have-design.md)
  ("lth/defVal", "def d1 : Nat := let x := Nat.zero; x"),
  ("lth/defHave", "def d2 : Nat := have x := Nat.zero; x"),
  ("lth/defDep", "def d3 : Nat := let T := Nat; (Nat.zero : T)"),
  ("lth/defDepRfl", "def d4 : Eq Nat.zero Nat.zero := let x := Nat.zero; (rfl : Eq x Nat.zero)"),
  ("lth/defNested", "def d5 : Nat := let x := Nat.zero; let y := x; y"),
  ("lth/defNestedDep", "def d6 : Nat := let T := Nat; let y : T := Nat.zero; y"),
  ("lth/defLam", "def d7 : Nat -> Nat := fun n => let x := n; x"),
  ("lth/defLamDep", "def d8 : Nat -> Nat := fun n => let T := Nat; (n : T)"),
  ("lth/defType", "def d9 : (let T := Nat; T) := Nat.zero"),
  ("lth/defTypeArrow", "def d10 : (let T := Nat; T -> T) := fun x => x"),
  ("lth/thmVal", "theorem t1 : Eq Nat.zero Nat.zero := let x := Nat.zero; rfl"),
  ("lth/thmValDep", "theorem t2 : Eq Nat.zero Nat.zero := let x := Nat.zero; (rfl : Eq x x)"),
  ("lth/thmType", "theorem t3 : (let x := Nat.zero; Eq x x) := rfl"),
  ("lth/abbrev", "abbrev a1 : Nat := let x := Nat.zero; x"),
  ("lth/example", "example : Nat := let x := Nat.zero; x"),
  ("lth/opaque", "opaque o1 : Nat := let x := Nat.zero; x"),
  ("lth/opaqueType", "opaque o2 : (let T := Nat; T) := Nat.zero"),
  ("lth/propDef", "def p1 : Eq Nat.zero Nat.zero := let x := Nat.zero; rfl"),
  ("lth/axiomType", "axiom ax1 : (let T := Nat; T)"),
  ("lth/letProofVal", "def d11 : Nat := let h : Eq Nat.zero Nat.zero := rfl; Nat.zero"),
  ("lth/unusedLet", "def d12 : Nat := let x := Bool.true; Nat.zero"),
  ("lth/letInArg", "def d13 : Nat := pick (let x := Nat.zero; x) Nat.zero"),
  ("lth/depAfterNondep", "def d14 : Nat := let x := Nat.zero; let T := Nat; (x : T)"),
  ("lth/exampleType", "example : (let T := Nat; T) := Nat.zero"),
  ("lth/defLetTypeOnly", "def d15 : Nat := let x : Nat := Nat.zero; Nat.zero"),
  ("lth/nonPropDep", "def d17 : PProd (Eq Nat.zero Nat.zero) Nat := let x := Nat.zero; PProd.mk (rfl : Eq x Nat.zero) x"),
  ("lth/nonPropDepIdx", "def d19 : PProd Nat Nat := let x := Nat.zero; let y := x; PProd.mk x Nat.zero"),
  ("lth/lamBinderDep", "def d20 : Nat := let T := Nat; (fun (z : T) => z) Nat.zero"),
  ("lth/proofArgDep", "def d21 : Nat := let x := Nat.zero; PProd.fst (PProd.mk x (rfl : Eq x x))"),
  ("lth/proofArgNoDep", "def d22 : Nat := let x := Nat.zero; PProd.fst (PProd.mk x (rfl : Eq Nat.zero Nat.zero))"),
  ("lth/proofInLetVal", "def d23 : PProd Nat (Eq Nat.zero Nat.zero) := let p := PProd.mk Nat.zero (rfl : Eq Nat.zero Nat.zero); p"),
  ("lth/letInLetVal", "def d24 : Nat := let x := (let y := Nat.zero; y); x"),
  ("lth/letInBinderType", "def d25 : (n : (let T := Nat; T)) -> Nat := fun n => n"),
  ("lth/haveDep", "def d26 : Nat := have x := Nat.zero; let T := Nat; (x : T)"),
  ("lth/sameNameTwice", "def d27 : Nat := let x := Nat.zero; let x := x; x"),
  ("lth/thmHeaderAsync", "theorem t4 : (let x := Nat.zero; Eq x Nat.zero) := rfl"),
  ("lth/lamTypeDep", "def d32 : Nat -> Nat := let T := Nat; fun (z : T) => z"),
  ("lth/letTypeAnn", "def d33 : Nat := let T : Type := Nat; let y : T := Nat.zero; Nat.zero"),
  ("lth/auxProofHave", "def d35 : PProd Nat Nat := have x := Nat.zero; PProd.mk Nat.zero (PProd.fst (PProd.mk x (eq_of_heq (HEq.refl x))))"),
  ("lth/auxProofOutsideLet", "def d36 : PProd Nat (Eq Nat.zero Nat.zero) := PProd.mk (let x := Nat.zero; x) (eq_of_heq (HEq.refl Nat.zero))"),
  ("lth/letUnderLamTypeOnly", "def d37 : Nat -> Nat := fun (n : (let T := Nat; T)) => n"),
  ("lth/auxProofInLetValue", "def d38 : Nat := let p := PProd.mk Nat.zero (eq_of_heq (HEq.refl Nat.zero)); PProd.fst p")
```

- [ ] **Step 3: Regenerate and check the diff**

```bash
cd tests/fixtures/elab && LEAN_PATH=$PWD lean --run dump_decls.lean files > file-queries.jsonl 2> /workspace/target/wt-d-regen.err; cd -
wc -l tests/fixtures/elab/file-queries.jsonl          # expect N_before + 42
git diff --stat tests/fixtures/elab/file-queries.jsonl # 42 insertions, 0 deletions
cat /workspace/target/wt-d-regen.err                   # expect empty
```

If the diff shows any other change, that is drift. STOP and report it.

Check the expected H/L pattern against the committed probe:

```bash
python3 /workspace/target/designDplan/show.py <(grep '"id":"lth/' tests/fixtures/elab/file-queries.jsonl) | diff - /workspace/target/designDplan/final_expected.txt
```

(The expected patterns are also listed in the table in Task 5.)

- [ ] **Step 4: Gate them as PENDING and bump the floor.** In `crates/leanr_elab/tests/oracle_file.rs`:

```rust
/// `lth/`: staged by the letToHave plan's Task 1; Task 5 removes it.
const PENDING: &[&str] = &["lth/"];
```

```rust
/// `wc -l tests/fixtures/elab/file-queries.jsonl` at the last deliberate
/// regen (letToHave: N_before + 42). `>=`: adding a record is a one-line
/// bump, not a failing gate.
const CORPUS_FLOOR: usize = /* N_before + 42 */;
```

- [ ] **Step 5: Run the file gate.** Expected: PASS (the rows are pending).

```bash
( ulimit -v 16000000; CARGO_BUILD_JOBS=6 timeout 1500 cargo test -p leanr_elab --test oracle_file )
```

- [ ] **Step 6: Prove the rows are red.** Temporarily set `PENDING` to `&[]`, rerun, and expect failures on the `lth/*` rows (`letToHave … later M4`). Restore `&["lth/"]`.

- [ ] **Step 7: Commit**

```bash
cargo fmt --all
git add tests/fixtures/elab/dump_decls.lean tests/fixtures/elab/file-queries.jsonl crates/leanr_elab/tests/oracle_file.rs
git commit -m "letToHave: stage 42 oracle rows (PENDING lth/)"
```

---

### Task 2: Zeta-delta tracking in `leanr_meta`

**Files:**
- Modify: `crates/leanr_meta/src/metactx.rs` (struct fields near `:158`, `new` near `:459`, `with_new_mctx_depth` `:559-574`, `checkpoint`/`rollback` `:2060-2079`, `MetaSnapshot` `:2173-2178`)
- Modify: `crates/leanr_meta/src/whnf.rs` (`:258-268`; module doc `:72-75`)
- Test: inline `#[cfg(test)]` in `metactx.rs`

**Interfaces:**
- Produces:
  - `pub(crate) track_zeta_delta: bool`
  - `pub(crate) zeta_delta_fvar_ids: HashSet<NameId>`
  - `pub fn zeta_delta_fvar_ids(&self) -> &HashSet<NameId>`
  - `pub fn with_tracking_zeta_delta<R>(&mut self, f: impl FnOnce(&mut Self) -> Result<R, MetaError>) -> Result<R, MetaError>`
  - `pub(crate) fn with_fresh_cache<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R`

- [ ] **Step 1: Write the failing tests** (in `metactx.rs`'s `mod tests`)

```rust
    /// oracle: `whnfEasyCases` records a followed genuine let under
    /// `trackZetaDelta` (`WHNF.lean:404-408`); a `have` is never followed.
    #[test]
    fn tracking_records_a_let_never_a_have() {
        with_prelude0_ctx(|ctx| {
            let nat = ctx.const_named("N");
            let zero = ctx.const_named("N.zero");
            let cp = ctx.lctx_checkpoint();
            let h = ctx.push_let_decl(None, nat, zero, true).expect("have");
            let l = ctx.push_let_decl(None, nat, zero, false).expect("let");
            let (hid, lid) = (ctx.fvar_id_of(h).unwrap(), ctx.fvar_id_of(l).unwrap());
            // Tracking off: following `l` records nothing.
            ctx.whnf(l).expect("whnf");
            assert!(ctx.zeta_delta_fvar_ids().is_empty());
            let seen = ctx
                .with_tracking_zeta_delta(|c| {
                    c.whnf(h)?;
                    c.whnf(l)?;
                    Ok(c.zeta_delta_fvar_ids().clone())
                })
                .expect("tracked");
            assert!(seen.contains(&lid), "a followed let is recorded");
            assert!(!seen.contains(&hid), "a have is never recorded");
            // `withTrackingZetaDelta`: records do not persist past the scope.
            assert!(ctx.zeta_delta_fvar_ids().is_empty());
            assert!(!ctx.track_zeta_delta);
            ctx.lctx_restore(cp);
        });
    }

    /// oracle: `checkpointDefEq` restores the saved state on failure
    /// (`Meta/Basic.lean:2463-2468`), and `SavedState.restore` includes
    /// `zetaDeltaFVarIds` (`:596`): a FAILED `isDefEq` forgets what it unfolded.
    #[test]
    fn a_failed_def_eq_discards_its_zeta_delta_records() {
        with_prelude0_ctx(|ctx| {
            let nat = ctx.const_named("N");
            let zero = ctx.const_named("N.zero");
            let succ = ctx.const_named("N.succ");
            let one = ctx.mk_app_spine(succ, &[zero]).expect("app");
            let cp = ctx.lctx_checkpoint();
            let l = ctx.push_let_decl(None, nat, zero, false).expect("let");
            let lid = ctx.fvar_id_of(l).unwrap();
            let (failed, ok) = ctx
                .with_tracking_zeta_delta(|c| {
                    assert!(!c.is_def_eq(l, one)?, "N.zero is not N.succ N.zero");
                    let failed = c.zeta_delta_fvar_ids().contains(&lid);
                    assert!(c.is_def_eq(l, zero)?);
                    Ok((failed, c.zeta_delta_fvar_ids().contains(&lid)))
                })
                .expect("tracked");
            assert!(!failed, "the failed defeq's record is rolled back");
            assert!(ok, "the successful defeq's record stays");
            ctx.lctx_restore(cp);
        });
    }

    /// oracle: `withNewMCtxDepthImp` restores only `mctx`/`postponed`
    /// (`Meta/Basic.lean:1974-1980`): records made inside SURVIVE it.
    #[test]
    fn new_mctx_depth_keeps_zeta_delta_records() {
        with_prelude0_ctx(|ctx| {
            let nat = ctx.const_named("N");
            let zero = ctx.const_named("N.zero");
            let cp = ctx.lctx_checkpoint();
            let l = ctx.push_let_decl(None, nat, zero, false).expect("let");
            let lid = ctx.fvar_id_of(l).unwrap();
            let kept = ctx
                .with_tracking_zeta_delta(|c| {
                    c.with_new_mctx_depth(false, |c| c.whnf(l))?;
                    Ok(c.zeta_delta_fvar_ids().contains(&lid))
                })
                .expect("tracked");
            assert!(kept);
            ctx.lctx_restore(cp);
        });
    }

    /// Review Focus 2: an `Err` inside the scope restores the flag, the
    /// set and every cache (`withTrackingZetaDelta`'s `finally`s).
    #[test]
    fn tracking_scope_restores_on_err() {
        with_prelude0_ctx(|ctx| {
            let n = ctx.const_named("N");
            ctx.infer_type(n).expect("warm the infer cache");
            let warm = ctx.infer_cache.len();
            assert!(warm > 0);
            let r: Result<(), MetaError> = ctx.with_tracking_zeta_delta(|c| {
                assert!(c.infer_cache.is_empty(), "fresh cache inside the scope");
                Err(MetaError::Infer("boom".into()))
            });
            assert!(r.is_err());
            assert!(!ctx.track_zeta_delta);
            assert!(ctx.zeta_delta_fvar_ids().is_empty());
            assert_eq!(ctx.infer_cache.len(), warm, "outer cache restored");
        });
    }
```

- [ ] **Step 2: Run them to see them fail.** Expected: compile errors (`zeta_delta_fvar_ids`, `with_tracking_zeta_delta`, `track_zeta_delta` not defined).

```bash
( ulimit -v 16000000; CARGO_BUILD_JOBS=6 timeout 1500 cargo test -p leanr_meta --lib metactx::tests::tracking -- --nocapture )
```

- [ ] **Step 3: Implement.** Struct fields, placed after `defeq_cache_transient`:

```rust
    /// oracle: `Meta.Context.trackZetaDelta` (`Meta/Basic.lean`, read at
    /// `WHNF.lean:407`). Set only by [`MetaCtx::with_tracking_zeta_delta`].
    pub(crate) track_zeta_delta: bool,
    /// oracle: `Meta.State.zetaDeltaFVarIds` (`Meta/Basic.lean:443-444`):
    /// the genuine let-fvars `whnf` unfolded while `track_zeta_delta` was
    /// on. Backtrackable like the mctx: part of [`MetaSnapshot`]
    /// (`SavedState.restore`, `:596`).
    pub(crate) zeta_delta_fvar_ids: HashSet<NameId>,
```

In `new`, after `defeq_cache_transient: HashMap::new(),`:

```rust
            track_zeta_delta: false,
            zeta_delta_fvar_ids: HashSet::new(),
```

Snapshot (`MetaSnapshot`, `checkpoint`, `rollback`):

```rust
pub struct MetaSnapshot {
    expr_assignments: HashMap<MVarId, ExprId>,
    level_assignments: HashMap<LMVarId, LevelId>,
    delayed_assignments: HashMap<MVarId, crate::DelayedMVarAssignment>,
    postponed: Vec<(LevelId, LevelId)>,
    /// `SavedState.restore` restores `zetaDeltaFVarIds` (`Meta/Basic.lean:596`).
    zeta_delta_fvar_ids: HashSet<NameId>,
}
```

```rust
            postponed: self.postponed.clone(),
            zeta_delta_fvar_ids: self.zeta_delta_fvar_ids.clone(),
```

```rust
        self.postponed = snap.postponed;
        self.zeta_delta_fvar_ids = snap.zeta_delta_fvar_ids;
```

The `with_new_mctx_depth` carve-out: replace `self.rollback(snap);` with

```rust
        // `withNewMCtxDepthImp` (`Meta/Basic.lean:1974-1980`) restores only
        // `mctx` and `postponed`: zeta-delta records made inside survive.
        let zeta = std::mem::take(&mut self.zeta_delta_fvar_ids);
        self.rollback(snap);
        self.zeta_delta_fvar_ids = zeta;
```

The scopes (next to `with_transparency`):

```rust
    /// oracle: `withFreshCache` (`Meta/Basic.lean:1183-1190`): run `f`
    /// with every Meta cache empty, then restore the saved caches.
    ///
    /// leanr's whnf/whnf_core/infer caches hold fvar-free keys only
    /// (`cacheable`) and top-level `is_def_eq` clears both defeq caches, so
    /// no cached answer can hide a let-fvar unfold today. The scope is kept
    /// for fidelity; its mutation is recorded as equivalent.
    pub(crate) fn with_fresh_cache<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        let whnf = std::mem::take(&mut self.whnf_cache);
        let whnf_core = std::mem::take(&mut self.whnf_core_cache);
        let infer = std::mem::take(&mut self.infer_cache);
        let perm = std::mem::take(&mut self.defeq_cache_perm);
        let transient = std::mem::take(&mut self.defeq_cache_transient);
        let r = f(self);
        self.whnf_cache = whnf;
        self.whnf_core_cache = whnf_core;
        self.infer_cache = infer;
        self.defeq_cache_perm = perm;
        self.defeq_cache_transient = transient;
        r
    }

    /// oracle: `withTrackingZetaDelta` (`Meta/Basic.lean:1243-1245`):
    /// `withFreshCache`, `trackZetaDelta := true`, and a cleared
    /// `zetaDeltaFVarIds` restored on exit (`withResetZetaDeltaFVarIds`,
    /// `:1227-1233`). Records made inside do not persist. `f` returns rather
    /// than unwinds, so the restore covers `Err` too.
    pub fn with_tracking_zeta_delta<R>(
        &mut self,
        f: impl FnOnce(&mut Self) -> Result<R, MetaError>,
    ) -> Result<R, MetaError> {
        let saved_track = std::mem::replace(&mut self.track_zeta_delta, true);
        let saved_set = std::mem::take(&mut self.zeta_delta_fvar_ids);
        let r = self.with_fresh_cache(f);
        self.track_zeta_delta = saved_track;
        self.zeta_delta_fvar_ids = saved_set;
        r
    }

    /// oracle: `getZetaDeltaFVarIds` (`Meta/Basic.lean:1214-1215`).
    pub fn zeta_delta_fvar_ids(&self) -> &HashSet<NameId> {
        &self.zeta_delta_fvar_ids
    }
```

In `whnf.rs`, the easy-cases `FVar` arm becomes:

```rust
                Node::FVar { id } => {
                    // The config bit and the value lookup are cheap; the
                    // `local_entry` row scan is O(depth), so it runs last.
                    let followed = id
                        .filter(|_| self.cfg.zeta_delta)
                        .and_then(|i| self.lctx.get(i).and_then(|d| d.value).map(|v| (i, v)))
                        .filter(|&(i, _)| self.local_entry(i).is_some_and(|e| !e.nondep));
                    match followed {
                        Some((i, v)) => {
                            // oracle `:407-408`: `if (← read).trackZetaDelta
                            // then addZetaDeltaFVarId fvarId`.
                            if self.track_zeta_delta {
                                self.zeta_delta_fvar_ids.insert(i);
                            }
                            v
                        }
                        None => return Ok(EasyOrHard::Easy(e)),
                    }
                }
```

Then update the comment block above it (`:253-255`) and the module-doc seam line (`:72-75`): `trackZetaDelta` is now modeled, while `isImplementationDetail` and `zetaDeltaSet` remain seams with no elab producer.

- [ ] **Step 4: Run the tests and the meta gates.** Expected: PASS.

```bash
( ulimit -v 16000000; CARGO_BUILD_JOBS=6 timeout 1500 cargo test -p leanr_meta --lib )
( ulimit -v 16000000; CARGO_BUILD_JOBS=6 timeout 1500 cargo test --release -p leanr_meta --test oracle_fast )
```

- [ ] **Step 5: Run the mutations, then record and revert each one**

| # | mutation | expected killer |
|---|---|---|
| T2a | drop the `insert(i)` in whnf | `tracking_records_a_let_never_a_have` |
| T2b | record before the `!e.nondep` filter (record haves too) | `tracking_records_a_let_never_a_have` |
| T2c | `MetaSnapshot` without the set (rollback leaves it) | `a_failed_def_eq_discards_its_zeta_delta_records` |
| T2d | drop the `with_new_mctx_depth` carve-out | `new_mctx_depth_keeps_zeta_delta_records` |
| T2e | `with_tracking_zeta_delta` skips `with_fresh_cache` | `tracking_scope_restores_on_err` (the cache assertion); the record behaviour should be EQUIVALENT (finding 4). Record both. |
| T2f | not restoring `track_zeta_delta` on exit | `tracking_scope_restores_on_err` |

- [ ] **Step 6: Commit.** Write the audit table (Plan-time finding 6) and the mutation results into the body.

```bash
cargo fmt --all
git add crates/leanr_meta/src/metactx.rs crates/leanr_meta/src/whnf.rs
git commit   # "leanr_meta: zeta-delta tracking (trackZetaDelta, backtrackable set, fresh-cache scope)"
```

---

### Task 3: `abstractNestedProofs`' `letE` arm

**Files:**
- Modify: `crates/leanr_meta/src/abstract_proofs.rs`:
  - module doc `:13-15` (drop the `letE` seam bullet);
  - `anp_visit` `:363-367`;
  - `anp_visit_binders` `:409-501`;
  - `pending_lookup_seam` `:311-330`.
- Modify: `crates/leanr_meta/src/metactx.rs` (new `mk_lambda_let_fvars`, next to `mk_let_expr` `:1405`).
- Test: inline in `abstract_proofs.rs`.

**Interfaces:**
- Produces:
  - `pub(crate) fn mk_lambda_let_fvars(&mut self, fvars: &[ExprId], body: ExprId) -> Result<ExprId, MetaError>`, which is `mkLambdaFVars xs b (usedLetOnly := false) (generalizeNondepLet := false)`.
  - `pub(crate) fn pending_lookup_seam(&self, aux: &AuxLemmas, err: MetaError, who: &str) -> MetaError`.
- Consumes: Task 2 only indirectly (no API).

- [ ] **Step 1: Write the failing tests** (`abstract_proofs.rs` `mod tests`; they use `with_prelude0_ctx`)

This uses the module's own helpers (`name` at `:750-758`, `c` and `with_meta0_ctx` from `test_support`; Meta0 declares `N`).

```rust
    /// oracle `:101`: `lambdaLetTelescope` + `mkLambdaFVars (usedLetOnly :=
    /// false) (generalizeNondepLet := false)`: a proof-free let/have
    /// telescope rebuilds to the SAME term. An unused let is kept, and a
    /// `have` stays a `have` (not a lambda).
    #[test]
    fn a_proof_free_let_telescope_round_trips() {
        with_meta0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let n = c(ctx, "N");
            let zero = c(ctx, "N.zero");
            let b0 = ctx.scratch.expr_bvar(base, &Nat::from(0u64)).unwrap();
            let b1 = ctx.scratch.expr_bvar(base, &Nat::from(1u64)).unwrap();
            // let x : N := N.zero; have y : N := x; let u : N := N.zero; y
            let u = ctx.scratch.expr_let(base, None, n, zero, b1, false).unwrap();
            let y = ctx.scratch.expr_let(base, None, n, b0, u, true).unwrap();
            let e = ctx.scratch.expr_let(base, None, n, zero, y, false).unwrap();
            ctx.infer_type(e).expect("well typed");
            let foo = name(ctx, "fooL");
            let mut aux = AuxLemmas::new(foo);
            let r = ctx.abstract_nested_proofs(&mut aux, e).expect("no seam under let");
            assert_eq!(r, e, "a proof-free telescope is rebuilt identically");
            assert!(aux.into_pending().is_empty());
        });
    }
```

(`Nat` here is `leanr_kernel::Nat`. Add it to the test module's `use leanr_kernel::{…}` line if it isn't in scope through `super::*`; the parent module imports `Nat` for `expr_proj`. The existing pending-aux test at `:1160-1170` asserts the exact `abstractNestedProofs: lookup of pending aux lemma fooP._proof_1 — …` message and pins the `who` parameter for this caller unchanged. The let-VALUE visit is pinned end-to-end by corpus row `lth/auxProofInLetValue` in Task 5.)

- [ ] **Step 2: Run the round-trip test.** Expected: FAIL with `Unsupported("abstractNestedProofs under let …")`.

```bash
( ulimit -v 16000000; CARGO_BUILD_JOBS=6 timeout 1500 cargo test -p leanr_meta --lib abstract_proofs::tests::a_proof_free_let_telescope_round_trips )
```

- [ ] **Step 3: Implement.** `metactx.rs`:

```rust
    /// oracle: `mkLambdaFVars xs e (usedLetOnly := false)
    /// (generalizeNondepLet := false)` (`MetavarContext.lean:1312-1347`, the
    /// ldecl arm `:1327-1336` with both flags off): a cdecl becomes `lam`,
    /// and EVERY ldecl becomes `letE` with the decl's own `nondep` (a `have`
    /// stays a `have`; an unused let is kept). The peel-one-fvar loop is
    /// `infer.rs::rebuild_forall`'s oracle-verified abstraction.
    pub(crate) fn mk_lambda_let_fvars(
        &mut self,
        fvars: &[ExprId],
        body: ExprId,
    ) -> Result<ExprId, MetaError> {
        let body = self.elim_mvar_deps(fvars, body)?;
        let base = Some(self.view.store);
        let mut r = body;
        for i in (0..fvars.len()).rev() {
            r = abstract_fvars(self.scratch, base, r, std::slice::from_ref(&fvars[i]), &mut self.guard)?;
            let Node::FVar { id: Some(id) } = self.node(fvars[i]) else {
                return Err(MetaError::Infer("mk_lambda_let_fvars: not an fvar".into()));
            };
            let decl = self
                .lctx
                .get(id)
                .ok_or_else(|| MetaError::Infer("mk_lambda_let_fvars: fvar not declared".into()))?;
            let (name, ty, bi, value) = (decl.binder_name, decl.ty, decl.binder_info, decl.value);
            let ty = abstract_fvars(self.scratch, base, ty, &fvars[..i], &mut self.guard)?;
            r = match value {
                Some(v) => {
                    let v = abstract_fvars(self.scratch, base, v, &fvars[..i], &mut self.guard)?;
                    let nondep = self.local_entry(id).is_some_and(|e| e.nondep);
                    self.scratch.expr_let(base, name, ty, v, r, nondep)?
                }
                None => self.scratch.expr_lam(base, name, ty, r, bi)?,
            };
        }
        Ok(r)
    }
```

`abstract_proofs.rs`:

1. In `anp_visit`, replace the `Node::LetE { .. } => return Err(…)` arm by folding `LetE` into the binder arm:

```rust
                Node::Lam { .. } | Node::LetE { .. } | Node::Forall { .. } => {
                    let cp = self.lctx_checkpoint();
                    let r = self.anp_visit_binders(aux, cache, e);
                    self.lctx_restore(cp);
                    r?
                }
```

2. In `anp_visit_binders`:
   - `is_lambda` becomes `matches!(self.node(e), Node::Lam { .. } | Node::LetE { .. })`.
   - The phase-1 loop accepts `LetE` in lambda mode and records the value plus the nondep flag.
   - Phase 1 visits the values after the types (`:85-86`, `value? (allowNondep := true)`, so `have` values are visited too).
   - Phase 2 re-pushes with `push_let_decl`.
   - The rebuild uses `mk_lambda_let_fvars`.

   Concretely, the binder record becomes `(name, d, bi, Option<(ExprId /*value*/, bool /*nondep*/)>)`. Phase 1 pushes `push_let_decl(decl_name, d, v, non_dep)` for a `LetE`, where `v = instantiate_rev(value, &xs)`. After the type loop, run `values.push(self.guarded(|c| c.anp_visit(aux, cache, v))?)` for each let binder. Phase 2 does `let v2 = self.anp_replace_fvars(values[k], &xs[..i], &ys)?; self.push_let_decl(name, t, v2, non_dep)?`. The tail becomes:

```rust
        if is_lambda {
            self.mk_lambda_let_fvars(&ys, b)
        } else {
            self.mk_forall(&ys, b)
        }
```

   Update the doc comment: the last paragraph's "letE is a seam" is now false.

3. `pending_lookup_seam(&self, aux, err, who: &str)`: the message becomes `format!("{who}: lookup of pending aux lemma {nm} — M4c-1 seam (needs pending-constant overlay)")`, and existing callers pass `"abstractNestedProofs"`. Make it `pub(crate)`.

- [ ] **Step 4: Run.** Expected: PASS, and the existing abstract_proofs tests still pass.

```bash
( ulimit -v 16000000; CARGO_BUILD_JOBS=6 timeout 1500 cargo test -p leanr_meta --lib abstract_proofs )
```

- [ ] **Step 5: Run the mutations, then record and revert each one.** T3a–T3c are re-run in Task 5, where the rows are live. Here, record the unit-test result.

| # | mutation | expected killer |
|---|---|---|
| T3a | rebuild with `mk_lambda` (generalizes a `have` to a lambda / refuses a let) | `a_proof_free_let_telescope_round_trips` |
| T3b | `mk_lambda_let_fvars` drops an unused let (`usedLetOnly := true`) | `a_proof_free_let_telescope_round_trips` |
| T3c | phase 1 does not visit let values | corpus `lth/auxProofInLetValue` (Task 5); unit tests are expected to survive. Record it. |

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
git add crates/leanr_meta/src/abstract_proofs.rs crates/leanr_meta/src/metactx.rs
git commit   # "leanr_meta: abstractNestedProofs letE arm (lambdaLetTelescope + mkLambdaFVars usedLetOnly:=false)"
```

---

### Task 4: `let_to_have.rs`, the `LetToHave.lean` port

**Files:**
- Create: `crates/leanr_meta/src/let_to_have.rs`
- Modify: `crates/leanr_meta/src/lib.rs` (add `mod let_to_have;` in alphabetical order, after `mod level_params;` or wherever `l…` sorts)
- Modify: `crates/leanr_meta/src/metactx.rs` (`with_infer_type_config`, next to `with_transparency`)
- Test: inline in `let_to_have.rs`

**Interfaces:**
- Consumes:
  - `with_tracking_zeta_delta` and the `zeta_delta_fvar_ids` field (Task 2);
  - `pending_lookup_seam(aux, err, who)` (Task 3);
  - existing `infer_type`, `whnf`, `is_def_eq`, `instantiate1`, `instantiate_mvars`, `push_local_decl_without_instance(name, ty, bi, LocalDeclKind)`, `push_let_decl(name, ty, value, non_dep)`, `lctx_checkpoint`/`lctx_restore`, `local_entry`, `fvar_id_of`, `has_loose_bvar(e, idx)`, `mk_level_imax_prime`, `get_app_fn`, `get_app_args`, `guarded`, `step`.
- Produces: `pub fn let_to_have(&mut self, aux: &AuxLemmas, e: ExprId) -> Result<ExprId, MetaError>` (Task 5's only entry point).

- [ ] **Step 1: Write the failing tests** (`let_to_have.rs` `mod tests`). Build the terms with the store constructors; `N`, `N.zero` and `N.succ` come from Prelude0. Use `AuxLemmas::new(<any NameId>)`, built the way `abstract_proofs.rs`'s tests intern `foo_p`.

```rust
#[cfg(test)]
mod tests {
    use leanr_kernel::bank::terms::Node;
    use leanr_kernel::{BinderInfo, Nat};

    use crate::test_support::with_prelude0_ctx;
    use crate::{AuxLemmas, MetaCtx};

    fn bvar(ctx: &mut MetaCtx, i: u64) -> leanr_kernel::bank::ExprId {
        ctx.scratch.expr_bvar(Some(ctx.view.store), &Nat::from(i)).unwrap()
    }
    fn aux(ctx: &mut MetaCtx) -> AuxLemmas {
        let base = Some(ctx.view.store);
        let s = ctx.scratch.intern_str(base, "lth").unwrap();
        AuxLemmas::new(ctx.scratch.name_str(base, None, s).unwrap())
    }
    fn nondeps(ctx: &MetaCtx, mut e: leanr_kernel::bank::ExprId) -> Vec<bool> {
        let mut out = Vec::new();
        loop {
            match ctx.node(e) {
                Node::LetE { body, non_dep, .. } => { out.push(non_dep); e = body; }
                Node::Lam { body, .. } => e = body,
                Node::App { f, .. } => e = f,
                _ => return out,
            }
        }
    }

    /// `let x := N.zero; x` → `have` (`finalize`, `:354-358`).
    #[test]
    fn an_unused_value_becomes_a_have() {
        with_prelude0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let n = ctx.const_named("N");
            let zero = ctx.const_named("N.zero");
            let b0 = bvar(ctx, 0);
            let e = ctx.scratch.expr_let(base, None, n, zero, b0, false).unwrap();
            let a = aux(ctx);
            let r = ctx.let_to_have(&a, e).unwrap();
            assert_eq!(nondeps(ctx, r), vec![true]);
        });
    }

    /// `let T := N; (fun (z : T) => z) N.zero` keeps `T` a `let`: visitApp's
    /// `isDefEq T N` (`:239`) unfolds `T` under check.
    #[test]
    fn a_definitionally_used_let_stays_a_let() {
        with_prelude0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let n = ctx.const_named("N");
            let zero = ctx.const_named("N.zero");
            let z1 = ctx.scratch.level_zero(base).unwrap();
            let z1 = ctx.scratch.level_succ(base, z1).unwrap();
            let ty1 = ctx.scratch.expr_sort(base, z1).unwrap(); // Type
            let b0 = bvar(ctx, 0);
            // fun (z : T) => z — the binder type `#0` is `T` (outside the
            // lambda's own binder); the body `#0` is `z`.
            let lam = ctx.scratch.expr_lam(base, None, b0, b0, BinderInfo::Default).unwrap();
            let body = ctx.scratch.expr_app(base, lam, zero).unwrap();
            let e = ctx.scratch.expr_let(base, None, ty1, n, body, false).unwrap();
            ctx.infer_type(e).expect("well typed");
            let a = aux(ctx);
            let r = ctx.let_to_have(&a, e).unwrap();
            assert_eq!(nondeps(ctx, r), vec![false]);
        });
    }

    /// Review Focus 3: no genuine let → the input id itself (`:420`).
    #[test]
    fn no_dependent_let_is_the_identity() {
        with_prelude0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let n = ctx.const_named("N");
            let zero = ctx.const_named("N.zero");
            let b0 = bvar(ctx, 0);
            let e = ctx.scratch.expr_let(base, None, n, zero, b0, true).unwrap();
            let a = aux(ctx);
            assert_eq!(ctx.let_to_have(&a, e).unwrap(), e);
        });
    }

    /// `let T := Type; let y : T := N; …`: the outer let is checked by the
    /// inner value's `isDefEq T vType` (`:325-328`), so `T` stays a `let`;
    /// `y` is unused → `have`. Mirrors corpus `lth/defNestedDep`/`letTypeAnn`.
    #[test]
    fn a_value_check_under_a_let_records_the_outer_let() {
        with_prelude0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let n = ctx.const_named("N");
            let zero = ctx.const_named("N.zero");
            let l1 = ctx.scratch.level_zero(base).unwrap();
            let l1 = ctx.scratch.level_succ(base, l1).unwrap();
            let ty = ctx.scratch.expr_sort(base, l1).unwrap();
            let b0 = bvar(ctx, 0);
            // let T : Type := N; let y : T := N.zero; N.zero
            let inner = ctx.scratch.expr_let(base, None, b0, zero, zero, false).unwrap();
            let e = ctx.scratch.expr_let(base, None, ty, n, inner, false).unwrap();
            ctx.infer_type(e).expect("well typed");
            let a = aux(ctx);
            let r = ctx.let_to_have(&a, e).unwrap();
            assert_eq!(nondeps(ctx, r), vec![false, true]);
        });
    }

    /// Review Focus 1: deep chains end in Ok or DepthBudgetExhausted.
    #[test]
    fn a_deep_let_chain_never_overflows() {
        with_prelude0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let n = ctx.const_named("N");
            let zero = ctx.const_named("N.zero");
            let mut e = bvar(ctx, 0);
            for _ in 0..5000 {
                e = ctx.scratch.expr_let(base, None, n, zero, e, false).unwrap();
            }
            let a = aux(ctx);
            match ctx.let_to_have(&a, e) {
                Ok(_) | Err(crate::MetaError::DepthBudgetExhausted) => {}
                Err(other) => panic!("unexpected {other:?}"),
            }
        });
    }

    /// Review Focus 4: `checkCache` (`:137-148`) returns a cached result even
    /// when it was computed with check OFF. Here `N.succ (N.succ N.zero)` is
    /// visited unchecked as an argument outside any let, and the same id
    /// again as a let body; it must not error and the let becomes a `have`.
    #[test]
    fn cached_unchecked_subterm_is_not_rechecked() {
        with_prelude0_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let n = ctx.const_named("N");
            let zero = ctx.const_named("N.zero");
            let succ = ctx.const_named("N.succ");
            let one = ctx.scratch.expr_app(base, succ, zero).unwrap();
            let two = ctx.scratch.expr_app(base, succ, one).unwrap();
            let inner = ctx.scratch.expr_let(base, None, n, zero, two, false).unwrap();
            let e = ctx.scratch.expr_app(base, succ, inner).unwrap();
            let a = aux(ctx);
            let r = ctx.let_to_have(&a, e).unwrap();
            let Node::App { arg, .. } = ctx.node(r) else { panic!("an app") };
            assert_eq!(nondeps(ctx, arg), vec![true]);
        });
    }
}
```

> **Implementer:** compile each test before writing the port, fixing constructor argument orders against `crates/leanr_kernel/src/bank/terms.rs:441-600`. `expr_lam`/`expr_forall` take `(base, name, ty, body, bi)`; `expr_let` takes `(base, name, ty, value, body, non_dep)`. In `a_definitionally_used_let_stays_a_let` the lambda's binder type is `#0` (= `T`) and its body is `#0` (= `z`). Under the outer let, `#0` inside the lambda body means `z`, and the binder type `#0` means `T`. That is correct de Bruijn because the binder type sits outside the lambda's own binder. `cached_unchecked_subterm_is_not_rechecked` is a smoke test for the cache path (it must not error). If you can construct a discriminating version, where a check-off cached result changes the outcome, replace it and say so in the commit. Otherwise record its mutation (T4f) as equivalent.

- [ ] **Step 2: Run.** Expected: compile failure (`let_to_have` missing).

- [ ] **Step 3: Implement `with_infer_type_config`** (`metactx.rs`):

```rust
    /// oracle: `withInferTypeConfig` (`Meta/InferType.lean:228-234`):
    /// `withAtLeastTransparency .default`, then beta/iota/zeta/zetaHave/
    /// zetaDelta on and `proj := .yesWithDelta` (`etaStruct := .all`: leanr
    /// has no `etaStruct` field). The only caller runs under `.all`, which is
    /// already at least `.default`, so the transparency half is a no-op there
    /// and is ported as: raise to `Default` when below it.
    pub(crate) fn with_infer_type_config<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        let saved = self.cfg;
        if matches!(
            self.cfg.transparency,
            TransparencyMode::None
                | TransparencyMode::Reducible
                | TransparencyMode::Instances
                | TransparencyMode::Implicit
        ) {
            self.cfg.transparency = TransparencyMode::Default;
        }
        self.cfg.beta = true;
        self.cfg.iota = true;
        self.cfg.zeta = true;
        self.cfg.zeta_have = true;
        self.cfg.zeta_delta = true;
        self.cfg.proj = crate::ProjReduction::YesWithDelta;
        let r = f(self);
        self.cfg = saved;
        r
    }
```

(Open `transparency.rs:23-30` and the oracle's `TransparencyMode.lt` to confirm the ordering. If `Implicit` sits above `Default` in the oracle's lattice, drop it from the list.)

- [ ] **Step 4: Implement `let_to_have.rs`.** Every oracle line range below was opened at plan time.

```rust
//! oracle: `Meta.letToHave` (`Lean/Meta/LetToHave.lean`, v4.33.0-rc1):
//! rewrite every genuine `let` (`nondep := false`) that is not
//! definitionally used into a `have`. "Used" is approximated as the oracle
//! does: re-type-check the term, but only under a genuine let
//! (`Context.check`, `:111`), with `whnf`'s zeta-delta tracking on
//! (`withTrackingZetaDelta`); a let whose fvar was never unfolded becomes a
//! `have` (`finalize`, `:338-368`).
//!
//! Deviations, each output-equivalent:
//! - `visitConst` (`:201-208`) and `visitProj` (`:370-396`) defer to
//!   `infer_type` (`inferConstType` / `inferProjType`, the same arity check
//!   and the same field-type walk) after the oracle's own `whnf` of the
//!   structure type, which is the step that can record a zeta-delta.
//! - no `incCount` / trace output.
//! - an error naming a PENDING aux lemma becomes the M4c-1 pending-constant
//!   seam (`pending_lookup_seam`, `who = "letToHave"`): after
//!   `abstractNestedProofs`, `visitConst` on `d._proof_N` under a genuine
//!   let needs a constant the oracle has already added.

use std::collections::{HashMap, HashSet};

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::{abstract_fvars, instantiate_rev, lower_loose_bvars, Nat};

use crate::local_decl_kind::LocalDeclKind;
use crate::{AuxLemmas, MVarId, MetaCtx, MetaError, TransparencyMode};

/// oracle `Result` (`:78-85`).
#[derive(Clone, Copy)]
struct Res {
    expr: ExprId,
    ty: Option<ExprId>,
}

/// oracle `Context` (`:87-90`) + `State.results` (`:92-96`).
#[derive(Default)]
struct Lth {
    /// The genuine lets in scope (`letFVars`). Only emptiness matters for
    /// `check`; `checkMVar` marks all of them.
    let_fvars: Vec<NameId>,
    results: HashMap<ExprId, Res>,
}

impl Lth {
    fn check(&self) -> bool {
        !self.let_fvars.is_empty()
    }
}

impl<'e> MetaCtx<'e> {
    /// oracle: `letToHave` (`:440-443`) → `main` (`:416-431`).
    pub fn let_to_have(&mut self, aux: &AuxLemmas, e: ExprId) -> Result<ExprId, MetaError> {
        let e = self.instantiate_mvars(e)?;
        if !self.lth_has_dep_let(e) {
            return Ok(e);
        }
        let r = self.with_tracking_zeta_delta(|c| {
            c.with_transparency(TransparencyMode::All, |c| {
                c.with_infer_type_config(|c| {
                    let mut st = Lth::default();
                    c.lth_visit(&mut st, e).map(|r| r.expr)
                })
            })
        });
        r.map_err(|err| self.pending_lookup_seam(aux, err, "letToHave"))
    }

    /// `hasDepLet` (`:67-68`).
    fn lth_has_dep_let(&self, e: ExprId) -> bool {
        let mut seen: HashSet<ExprId> = HashSet::new();
        let mut stack = vec![e];
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match self.node(t) {
                Node::LetE { non_dep: false, .. } => return true,
                Node::LetE { ty, value, body, .. } => stack.extend([ty, value, body]),
                Node::App { f, arg } => stack.extend([f, arg]),
                Node::Lam { binder_type, body, .. } | Node::Forall { binder_type, body, .. } => {
                    stack.extend([binder_type, body])
                }
                Node::MData { expr, .. } => stack.push(expr),
                Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => stack.push(structure),
                _ => {}
            }
        }
        false
    }

    /// `canSkip` (`:75-76`).
    fn lth_can_skip(&self, e: ExprId, max_depth: u32) -> bool {
        let d = self.data(e);
        !d.has_fvar() && !d.has_expr_mvar() && u32::from(d.approx_depth()) <= max_depth && !self.lth_has_dep_let(e)
    }

    /// `Result.type` (`:101-109`).
    fn lth_type(&mut self, st: &mut Lth, r: Res) -> Result<ExprId, MetaError> {
        if let Some(t) = r.ty {
            return Ok(t);
        }
        let t = self.infer_type(r.expr)?;
        st.results.insert(r.expr, Res { expr: r.expr, ty: Some(t) });
        Ok(t)
    }

    /// `checkCache` (`:137-148`).
    fn lth_check_cache(
        &mut self,
        st: &mut Lth,
        e: ExprId,
        f: impl FnOnce(&mut Self, &mut Lth) -> Result<Res, MetaError>,
    ) -> Result<Res, MetaError> {
        if let Some(r) = st.results.get(&e).copied() {
            return Ok(r);
        }
        let r = if self.lth_can_skip(e, 2) { Res { expr: e, ty: None } } else { f(self, st)? };
        st.results.insert(e, r);
        Ok(r)
    }

    /// `visit` (`:398-412`).
    fn lth_visit(&mut self, st: &mut Lth, e: ExprId) -> Result<Res, MetaError> {
        self.step()?;
        self.guarded(|c| c.lth_visit_core(st, e))
    }

    fn lth_visit_core(&mut self, st: &mut Lth, e: ExprId) -> Result<Res, MetaError> {
        let base = Some(self.view.store);
        match self.node(e) {
            Node::BVar { .. } | Node::BVarBig { .. } => {
                Err(MetaError::Infer("letToHave: unexpected bound variable".into()))
            }
            // `visitFVar` (`:153-155`).
            Node::FVar { id } => {
                let id = id.ok_or_else(|| MetaError::Infer("letToHave: anonymous fvar".into()))?;
                let ty = self
                    .lctx
                    .get(id)
                    .map(|d| d.ty)
                    .ok_or_else(|| MetaError::Infer("letToHave: unknown free variable".into()))?;
                Ok(Res { expr: e, ty: Some(ty) })
            }
            // `visitMVar` (`:196-199`).
            Node::MVar { id } => {
                let id = MVarId(id.ok_or_else(|| MetaError::Infer("letToHave: anonymous mvar".into()))?);
                let ty = self
                    .mctx
                    .decl(id)
                    .map(|d| d.ty)
                    .ok_or_else(|| MetaError::Infer("letToHave: unknown metavariable".into()))?;
                if st.check() {
                    self.lth_check_mvar(st, id, &[])?;
                }
                Ok(Res { expr: e, ty: Some(ty) })
            }
            Node::Sort { level } => {
                let u = self.scratch.level_succ(base, level)?;
                Ok(Res { expr: e, ty: Some(self.scratch.expr_sort(base, u)?) })
            }
            // `visitConst` (`:201-208`): `whenCheck`, then the type.
            Node::Const { .. } => {
                if !st.check() {
                    return Ok(Res { expr: e, ty: None });
                }
                Ok(Res { expr: e, ty: Some(self.infer_type(e)?) })
            }
            Node::App { .. } => self.lth_check_cache(st, e, |c, st| c.lth_visit_app_args(st, e)),
            Node::Forall { .. } => self.lth_check_cache(st, e, |c, st| c.lth_visit_forall(st, e)),
            Node::Lam { .. } | Node::LetE { .. } => {
                self.lth_check_cache(st, e, |c, st| c.lth_visit_lambda_let(st, e))
            }
            // `.lit v => { type? := v.type }`.
            Node::LitNat { .. } | Node::LitStr { .. } => Ok(Res { expr: e, ty: Some(self.infer_type(e)?) }),
            Node::MData { data, expr } => {
                let r = self.lth_visit(st, expr)?;
                let e2 = if r.expr == expr { e } else { self.scratch.expr_mdata(base, data, r.expr)? };
                Ok(Res { expr: e2, ty: r.ty })
            }
            Node::Proj { .. } | Node::ProjBig { .. } => {
                self.lth_check_cache(st, e, |c, st| c.lth_visit_proj(st, e))
            }
        }
    }

    /// `visitDepExpr` (`:164-181`).
    fn lth_visit_dep_expr(&mut self, e: ExprId) -> Result<(), MetaError> {
        let mut visited: HashSet<NameId> = HashSet::new();
        let mut worklist = vec![e];
        while let Some(t) = worklist.pop() {
            let t = self.instantiate_mvars(t)?;
            for fid in self.lth_collect_fvars(t) {
                if visited.insert(fid) {
                    // `isLetVar`: a genuine let only.
                    let is_let = self.lctx.get(fid).is_some_and(|d| d.value.is_some())
                        && self.local_entry(fid).is_some_and(|en| !en.nondep);
                    if is_let {
                        self.zeta_delta_fvar_ids.insert(fid);
                    }
                    if let Some(d) = self.lctx.get(fid) {
                        worklist.push(d.ty);
                    }
                }
            }
        }
        Ok(())
    }

    fn lth_collect_fvars(&self, e: ExprId) -> Vec<NameId> {
        let mut out = Vec::new();
        let mut seen: HashSet<ExprId> = HashSet::new();
        let mut stack = vec![e];
        while let Some(t) = stack.pop() {
            if !self.data(t).has_fvar() || !seen.insert(t) {
                continue;
            }
            match self.node(t) {
                Node::FVar { id: Some(id) } => out.push(id),
                Node::App { f, arg } => stack.extend([f, arg]),
                Node::Lam { binder_type, body, .. } | Node::Forall { binder_type, body, .. } => {
                    stack.extend([binder_type, body])
                }
                Node::LetE { ty, value, body, .. } => stack.extend([ty, value, body]),
                Node::MData { expr, .. } => stack.push(expr),
                Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => stack.push(structure),
                _ => {}
            }
        }
        out
    }

    /// `checkMVar` (`:183-194`).
    fn lth_check_mvar(&mut self, st: &mut Lth, mvar: MVarId, args: &[ExprId]) -> Result<(), MetaError> {
        let Some(d) = self.mctx.delayed_assignment(mvar).cloned() else {
            return Ok(());
        };
        if d.fvars.len() > args.len() {
            // An invalid delayed assignment: inhibit every enclosing let.
            for &f in &st.let_fvars {
                self.zeta_delta_fvar_ids.insert(f);
            }
            return Ok(());
        }
        let pending = self
            .mctx
            .decl(d.mvar_id_pending)
            .map(|p| p.lctx.clone())
            .ok_or_else(|| MetaError::Infer("letToHave: unknown pending metavariable".into()))?;
        for (fvar, &arg) in d.fvars.iter().zip(args) {
            let Some(fid) = self.fvar_id_of(*fvar) else { continue };
            let is_let = pending.lctx().get(fid).is_some_and(|x| x.value.is_some())
                && pending.entries().iter().any(|en| en.id == fid && !en.nondep);
            if is_let {
                self.lth_visit_dep_expr(arg)?;
            }
        }
        Ok(())
    }

    /// `ensureType` (`:214-226`).
    fn lth_ensure_type(&mut self, st: &mut Lth, r: Res) -> Result<Res, MetaError> {
        if !st.check() {
            return Ok(r);
        }
        let ty = self.lth_type(st, r)?;
        if matches!(self.node(ty), Node::Sort { .. }) {
            return Ok(Res { expr: r.expr, ty: Some(ty) });
        }
        let w = self.whnf(ty)?;
        if !matches!(self.node(w), Node::Sort { .. }) {
            return Err(MetaError::Infer("letToHave: type expected".into()));
        }
        let r2 = Res { expr: r.expr, ty: Some(w) };
        st.results.insert(r.expr, r2);
        Ok(r2)
    }

    /// `visitType` (`:247-249`).
    fn lth_visit_type(&mut self, st: &mut Lth, e: ExprId) -> Result<Res, MetaError> {
        let r = self.lth_visit(st, e)?;
        self.lth_ensure_type(st, r)
    }

    fn lth_update_app(&mut self, e: ExprId, f: ExprId, a: ExprId) -> Result<ExprId, MetaError> {
        match self.node(e) {
            Node::App { f: f0, arg: a0 } if f0 == f && a0 == a => Ok(e),
            _ => Ok(self.scratch.expr_app(Some(self.view.store), f, a)?),
        }
    }

    /// `visitApp` (`:231-244`).
    fn lth_visit_app(&mut self, st: &mut Lth, e: ExprId, f: Res, a: Res) -> Result<Res, MetaError> {
        let e2 = self.lth_update_app(e, f.expr, a.expr)?;
        if !st.check() {
            return Ok(Res { expr: e2, ty: None });
        }
        let mut fty = self.lth_type(st, f)?;
        if !matches!(self.node(fty), Node::Forall { .. }) {
            fty = self.whnf(fty)?;
        }
        let Node::Forall { binder_type, body, .. } = self.node(fty) else {
            return Err(MetaError::Infer("letToHave: function expected".into()));
        };
        let aty = self.lth_type(st, a)?;
        if !self.is_def_eq(binder_type, aty)? {
            return Err(MetaError::Infer("letToHave: application type mismatch".into()));
        }
        let ty = self.instantiate1(body, a.expr)?;
        Ok(Res { expr: e2, ty: Some(ty) })
    }

    /// `visitAppArgs` (`:251-264`).
    fn lth_visit_app_args(&mut self, st: &mut Lth, e: ExprId) -> Result<Res, MetaError> {
        if st.check() {
            let head = self.get_app_fn(e);
            if let Node::MVar { id: Some(m) } = self.node(head) {
                let args = self.get_app_args(e);
                self.lth_check_mvar(st, MVarId(m), &args)?;
            }
            self.lth_app_go(st, e)
        } else {
            let r = self.lth_app_go_unchecked(st, e)?;
            Ok(Res { expr: r, ty: None })
        }
    }

    fn lth_app_go(&mut self, st: &mut Lth, e: ExprId) -> Result<Res, MetaError> {
        let Node::App { f, arg } = self.node(e) else {
            return self.lth_visit(st, e);
        };
        let fr = self.lth_check_cache(st, f, |c, st| c.guarded(|c| c.lth_app_go(st, f)))?;
        let ar = self.lth_visit(st, arg)?;
        self.lth_visit_app(st, e, fr, ar)
    }

    fn lth_app_go_unchecked(&mut self, st: &mut Lth, e: ExprId) -> Result<ExprId, MetaError> {
        let Node::App { f, arg } = self.node(e) else {
            return Ok(self.lth_visit(st, e)?.expr);
        };
        let f2 = self.guarded(|c| c.lth_app_go_unchecked(st, f))?;
        let a2 = self.lth_visit(st, arg)?.expr;
        self.lth_update_app(e, f2, a2)
    }

    /// `visitForall` (`:266-300`).
    fn lth_visit_forall(&mut self, st: &mut Lth, e: ExprId) -> Result<Res, MetaError> {
        if self.lth_can_skip(e, 5) {
            return Ok(Res { expr: e, ty: None });
        }
        let cp = self.lctx_checkpoint();
        let r = self.lth_forall_go(st, e);
        self.lctx_restore(cp);
        r
    }

    fn lth_forall_go(&mut self, st: &mut Lth, e0: ExprId) -> Result<Res, MetaError> {
        let base = Some(self.view.store);
        let mut fvars: Vec<ExprId> = Vec::new();
        let mut doms: Vec<Res> = Vec::new();
        let mut cur = e0;
        loop {
            // `findCacheNoBVars?` (`:150-151`, `:273-274`).
            if self.data(cur).loose_bvar_range() == 0 {
                if let Some(r) = st.results.get(&cur).copied() {
                    return self.lth_forall_finalize(st, &fvars, &doms, r);
                }
            }
            match self.node(cur) {
                Node::Forall { binder_name, binder_type, body, binder_info } => {
                    let t0 = instantiate_rev(self.scratch, base, binder_type, &fvars, &mut self.guard)?;
                    let t = self.lth_visit_type(st, t0)?;
                    let x = self.push_local_decl_without_instance(
                        binder_name,
                        t.expr,
                        binder_info,
                        LocalDeclKind::Default,
                    )?;
                    fvars.push(x);
                    doms.push(t);
                    cur = body;
                }
                _ => {
                    let b = instantiate_rev(self.scratch, base, cur, &fvars, &mut self.guard)?;
                    let r = self.lth_visit(st, b)?;
                    return self.lth_forall_finalize(st, &fvars, &doms, r);
                }
            }
        }
    }

    /// `visitForall.finalize` (`:286-300`): `LocalContext.mkForall` (pure
    /// abstraction over cdecls), then the `imax`-fold of the levels under check.
    fn lth_forall_finalize(&mut self, st: &mut Lth, fvars: &[ExprId], doms: &[Res], body: Res) -> Result<Res, MetaError> {
        let base = Some(self.view.store);
        let mut e2 = body.expr;
        for i in (0..fvars.len()).rev() {
            e2 = abstract_fvars(self.scratch, base, e2, std::slice::from_ref(&fvars[i]), &mut self.guard)?;
            let fid = self.fvar_id_of(fvars[i]).ok_or_else(|| MetaError::Infer("letToHave: not an fvar".into()))?;
            let (name, ty, bi) = {
                let d = self.lctx.get(fid).ok_or_else(|| MetaError::Infer("letToHave: fvar not declared".into()))?;
                (d.binder_name, d.ty, d.binder_info)
            };
            let ty = abstract_fvars(self.scratch, base, ty, &fvars[..i], &mut self.guard)?;
            e2 = self.scratch.expr_forall(base, name, ty, e2, bi)?;
        }
        if !st.check() {
            return Ok(Res { expr: e2, ty: None });
        }
        let bt = self.lth_ensure_type(st, body)?.ty.expect("ensure_type under check sets ty");
        let Node::Sort { level: mut u } = self.node(bt) else {
            return Err(MetaError::Infer("letToHave: type expected".into()));
        };
        for dom in doms.iter().rev() {
            let dt = self.lth_type(st, *dom)?;
            let Node::Sort { level } = self.node(dt) else {
                return Err(MetaError::Infer("letToHave: type expected".into()));
            };
            u = self.mk_level_imax_prime(level, u)?;
        }
        Ok(Res { expr: e2, ty: Some(self.scratch.expr_sort(base, u)?) })
    }

    /// `visitLambdaLet` (`:302-368`).
    fn lth_visit_lambda_let(&mut self, st: &mut Lth, e: ExprId) -> Result<Res, MetaError> {
        if self.lth_can_skip(e, 5) {
            return Ok(Res { expr: e, ty: None });
        }
        let cp = self.lctx_checkpoint();
        let saved = st.let_fvars.clone();
        let r = self.lth_lambda_let_go(st, e);
        st.let_fvars = saved;
        self.lctx_restore(cp);
        r
    }

    fn lth_lambda_let_go(&mut self, st: &mut Lth, e0: ExprId) -> Result<Res, MetaError> {
        let base = Some(self.view.store);
        let mut let_fvars = st.let_fvars.clone();
        let mut fvars: Vec<ExprId> = Vec::new();
        let mut cur = e0;
        loop {
            match self.node(cur) {
                Node::Lam { binder_name, binder_type, body, binder_info } => {
                    st.let_fvars = let_fvars.clone();
                    let t0 = instantiate_rev(self.scratch, base, binder_type, &fvars, &mut self.guard)?;
                    let t = self.lth_visit_type(st, t0)?;
                    let x = self.push_local_decl_without_instance(
                        binder_name,
                        t.expr,
                        binder_info,
                        LocalDeclKind::Default,
                    )?;
                    fvars.push(x);
                    cur = body;
                }
                Node::LetE { decl_name, ty, value, body, non_dep } => {
                    st.let_fvars = let_fvars.clone();
                    let t0 = instantiate_rev(self.scratch, base, ty, &fvars, &mut self.guard)?;
                    let t = self.lth_visit_type(st, t0)?;
                    let v0 = instantiate_rev(self.scratch, base, value, &fvars, &mut self.guard)?;
                    let v = self.lth_visit(st, v0)?;
                    // `:325-328`: under an enclosing genuine let, the value's
                    // type must match (in the lctx BEFORE this let).
                    if !let_fvars.is_empty() {
                        let vty = self.lth_type(st, v)?;
                        if !self.is_def_eq(t.expr, vty)? {
                            return Err(MetaError::Infer("letToHave: invalid let declaration".into()));
                        }
                    }
                    let x = self.push_let_decl(decl_name, t.expr, v.expr, non_dep)?;
                    if !non_dep {
                        let fid = self.fvar_id_of(x).ok_or_else(|| MetaError::Infer("letToHave: not an fvar".into()))?;
                        let_fvars.insert(0, fid); // `fvarId :: letFVars` (`:331`)
                    }
                    fvars.push(x);
                    cur = body;
                }
                _ => {
                    st.let_fvars = let_fvars;
                    let b = instantiate_rev(self.scratch, base, cur, &fvars, &mut self.guard)?;
                    let body = self.lth_visit(st, b)?;
                    return self.lth_lambda_let_finalize(&fvars, body);
                }
            }
        }
    }

    /// `visitLambdaLet.finalize` (`:338-368`).
    fn lth_lambda_let_finalize(&mut self, fvars: &[ExprId], body: Res) -> Result<Res, MetaError> {
        let base = Some(self.view.store);
        let mut expr = abstract_fvars(self.scratch, base, body.expr, fvars, &mut self.guard)?;
        let mut ty = match body.ty {
            Some(t) => Some(abstract_fvars(self.scratch, base, t, fvars, &mut self.guard)?),
            None => None,
        };
        for i in (0..fvars.len()).rev() {
            let fid = self.fvar_id_of(fvars[i]).ok_or_else(|| MetaError::Infer("letToHave: not an fvar".into()))?;
            let (name, t, bi, value) = {
                let d = self.lctx.get(fid).ok_or_else(|| MetaError::Infer("letToHave: fvar not declared".into()))?;
                (d.binder_name, d.ty, d.binder_info, d.value)
            };
            let t = abstract_fvars(self.scratch, base, t, &fvars[..i], &mut self.guard)?;
            match value {
                None => {
                    expr = self.scratch.expr_lam(base, name, t, expr, bi)?;
                    ty = match ty {
                        Some(ty) => Some(self.scratch.expr_forall(base, name, t, ty, bi)?),
                        None => None,
                    };
                }
                Some(v) => {
                    let decl_nondep = self.local_entry(fid).is_some_and(|e| e.nondep);
                    let nondep = decl_nondep || !self.zeta_delta_fvar_ids.contains(&fid);
                    let v = abstract_fvars(self.scratch, base, v, &fvars[..i], &mut self.guard)?;
                    expr = self.scratch.expr_let(base, name, t, v, expr, nondep)?;
                    ty = match ty {
                        Some(ty) if self.has_loose_bvar(ty, 0)? => {
                            Some(self.scratch.expr_let(base, name, t, v, ty, nondep)?)
                        }
                        Some(ty) => Some(lower_loose_bvars(self.scratch, base, ty, 1, 1, &mut self.guard)?),
                        None => None,
                    };
                }
            }
        }
        Ok(Res { expr, ty })
    }

    /// `visitProj` (`:370-396`); see the module doc for the `infer_type`
    /// deferral.
    fn lth_visit_proj(&mut self, st: &mut Lth, e: ExprId) -> Result<Res, MetaError> {
        let base = Some(self.view.store);
        let (type_name, idx, structure) = match self.node(e) {
            Node::Proj { type_name, idx, structure } => (type_name, Nat::from(idx as u64), structure),
            Node::ProjBig { type_name, idx, structure } => {
                (type_name, self.scratch.nat_at(base, idx).clone(), structure)
            }
            _ => return Err(MetaError::Infer("letToHave: not a projection".into())),
        };
        let s = self.lth_visit(st, structure)?;
        let e2 = if s.expr == structure { e } else { self.scratch.expr_proj(base, type_name, &idx, s.expr)? };
        if !st.check() {
            return Ok(Res { expr: e2, ty: None });
        }
        let sty = self.lth_type(st, s)?;
        let _ = self.whnf(sty)?; // `:375`
        Ok(Res { expr: e2, ty: Some(self.infer_type(e2)?) })
    }
}
```

> **Implementer:** this code was written against the APIs opened at plan time but has NOT been compiled. Expect to fix:
> - field and method names, e.g. `LocalCtxSnapshot::entries()`, `LocalEntry.id`, `ExprData::loose_bvar_range` (`expr.rs:246`), and the `level_succ`/`level_zero` signatures (`bank/mod.rs:374`);
> - visibility of `pending_lookup_seam` and `local_decl_kind`.
>
> Keep the oracle structure. A borrow conflict on `self.lctx.get(..)` (as in the `{ let d = …; (…) }` blocks) is solved by copying the fields out first. `push_let_decl` installs a local instance for a class-typed let. The oracle's `withLCtx lctx {}` has none. That matters only for instance synthesis, which this pass never runs, so keep `push_let_decl` and add a comment saying so.

- [ ] **Step 5: Run the tests.** Expected: PASS.

```bash
( ulimit -v 16000000; CARGO_BUILD_JOBS=6 timeout 1500 cargo test -p leanr_meta --lib let_to_have )
```

- [ ] **Step 6: Run the mutations, then record and revert each one.** (Rows are re-checked in Task 5.)

| # | mutation | expected killer |
|---|---|---|
| T4a | `finalize`: `nondep = true` always | `a_definitionally_used_let_stays_a_let`, `a_value_check_under_a_let_records_the_outer_let` |
| T4b | `finalize`: read the set inverted | `an_unused_value_becomes_a_have` |
| T4c | `Lth::check` always `false` | `a_definitionally_used_let_stays_a_let` |
| T4d | `Lth::check` always `true` | expected EQUIVALENT: records only arise from let-fvars, which only exist where check is already on. Run it and record. |
| T4e | skip the `:325-328` value check | `a_value_check_under_a_let_records_the_outer_let` |
| T4f | `lth_check_cache` re-visits on a hit | expected EQUIVALENT unless a discriminating cache test was built (Step 1 note) |
| T4g | `let_to_have` skips `lth_has_dep_let` | `no_dependent_let_is_the_identity` (the id changes only if the walk re-interns; if it survives, record it as equivalent) |
| T4h | drop `lth_visit_dep_expr` from `lth_check_mvar` | expected EQUIVALENT: `visitMVar` on the same head (`:196-199`) already marks every enclosing let through the `fvars.size > args.size` arm. Record it. |

- [ ] **Step 7: Commit**

```bash
cargo fmt --all
git add crates/leanr_meta/src/let_to_have.rs crates/leanr_meta/src/lib.rs crates/leanr_meta/src/metactx.rs
git commit   # "leanr_meta: port Meta.letToHave (LetToHave.lean)"
```

---

### Task 5: Wire it into `def.rs`; the rows go green

**Files:**
- Modify: `crates/leanr_elab/src/command/def.rs`:
  - module doc `:1-15`;
  - `:139-143`, `:166-184`, `:250-251`;
  - delete `reject_let` `:399-433` and the `HashSet` import `:17`.
- Modify: `crates/leanr_elab/tests/oracle_file.rs` (`PENDING` back to `&[]`)
- Modify: `crates/leanr_elab/tests/oracle_decl.rs:78-82`
- Modify: `crates/leanr_elab/tests/seam_audit.rs:1544`

**Interfaces:** Consumes `MetaCtx::let_to_have(&AuxLemmas, ExprId)` (Task 4).

- [ ] **Step 1: Write the failing tests.** In `oracle_decl.rs`, replace `let_and_have_in_a_value_are_the_let_to_have_seam` with:

```rust
#[test]
fn let_and_have_in_a_value_are_admitted() {
    assert!(decl_result("def sl : Nat := let x := Nat.zero; x").is_ok());
    assert!(decl_result("def sh : Nat := have x := Nat.zero; x").is_ok());
}

/// Plan-time finding 2: a proof abstracted under a genuine `let` is checked
/// by letToHave's `visitConst` (`LetToHave.lean:201-208`) while still
/// pending: the M4c-1 pending-constant seam. Oracle (probed 2026-10-07):
/// d28 → value `have`, d29 → `have`, d30 → `let`. Also the order pin: with
/// letToHave BEFORE abstractNestedProofs, d29 elaborates (no pending
/// lookup) instead of seaming.
#[test]
fn a_proof_abstracted_under_a_let_is_the_pending_constant_seam() {
    for src in [
        "def d28 : PProd Nat (Eq Nat.zero Nat.zero) := let x := Nat.zero; PProd.mk x (eq_of_heq (HEq.refl Nat.zero))",
        "def d29 : PProd Nat (Eq Nat.zero Nat.zero) := let x := Nat.zero; PProd.mk x (eq_of_heq (HEq.refl x))",
        "def d30 : PProd Nat Nat := let x := Nat.zero; PProd.mk Nat.zero (PProd.fst (PProd.mk x (eq_of_heq (HEq.refl x))))",
    ] {
        let m = seam_message(src);
        assert!(
            m.starts_with("letToHave: lookup of pending aux lemma") && m.contains("pending-constant overlay"),
            "{src}: {m}"
        );
    }
}
```

In `seam_audit.rs`, delete the `("def sl : Nat := let x := Nat.zero; x", "letToHave"),` case. In `oracle_file.rs`, set `const PENDING: &[&str] = &[];` and restore its doc comment ("Empty: …").

- [ ] **Step 2: Run them to see them fail.** Expected: `let_and_have_in_a_value_are_admitted` fails (seam), and the file gate fails on `lth/*`.

```bash
( ulimit -v 16000000; CARGO_BUILD_JOBS=6 timeout 1500 cargo test -p leanr_elab --test oracle_decl --test oracle_file )
```

- [ ] **Step 3: Implement** in `def.rs`.
  1. Delete `:139-143` (the comment and both `reject_let` calls).
  2. Replace `:250-251` with:

```rust
    // `Meta.letToHave type` (`:1293-1296`) is not run here: this function
    // returns only the signature's level params, which letToHave never
    // changes, and the committed theorem type is the main path's (whose
    // `letToHaveType` runs in `elab_def`). Unobservable in leanr.
```

  3. After the `abstract_nested_proofs` block (`:184`, `};`), insert:

```rust
    // `addNonRecAux` → `letToHaveType` then `letToHaveValue`
    // (`PreDefinition/Basic.lean:183-185`), AFTER `abstractNestedProofs`
    // (`:180`). `cleanup.letToHave` is not modelled (`set_option` seams
    // every other option), so it is on.
    let ty = let_to_have_type(elab, view.kind, &aux, ty)?;
    let value = let_to_have_value(elab, view.kind, &aux, ty, value)?;
```

  4. Add the gates in place of `reject_let`:

```rust
/// oracle: `letToHaveType` (`PreDefinition/Basic.lean:113-118`): every kind
/// but `example`.
fn let_to_have_type(
    elab: &mut TermElabM,
    kind: DefKind,
    aux: &AuxLemmas,
    ty: ExprId,
) -> Result<ExprId, ElabError> {
    if kind == DefKind::Example {
        return Ok(ty);
    }
    elab.mctx.let_to_have(aux, ty).map_err(meta_seam)
}

/// oracle: `letToHaveValue` (`PreDefinition/Basic.lean:99-108`): not for
/// `theorem`/`example`/`opaque`, an `unsafe` declaration (unreachable:
/// `view.rs` seams `unsafe`), or a Prop-typed one (`Meta.isProp`).
fn let_to_have_value(
    elab: &mut TermElabM,
    kind: DefKind,
    aux: &AuxLemmas,
    ty: ExprId,
    value: ExprId,
) -> Result<ExprId, ElabError> {
    if matches!(kind, DefKind::Theorem | DefKind::Example | DefKind::Opaque) {
        return Ok(value);
    }
    if is_prop_full(elab, ty)? {
        return Ok(value);
    }
    elab.mctx.let_to_have(aux, value).map_err(meta_seam)
}

/// A `MetaError::Unsupported` is a named seam (the pending-constant one).
fn meta_seam(e: MetaError) -> ElabError {
    match e {
        MetaError::Unsupported(m) => ElabError::UnsupportedSyntax(m),
        e => ElabError::Meta(e),
    }
}
```

  Also: use `meta_seam` in the existing `abstract_nested_proofs` `map_err` (same body). Delete `reject_let` and `use std::collections::HashSet;`. Update the module doc (`:7-15`): drop letToHave from "Not modelled" if it's listed, and add "then `letToHaveType`/`letToHaveValue`". `ty` must be the letToHave'd type before `build_decl`, which already takes `ty`. Check that `example` (`Built::Check`) keeps its un-transformed type.

- [ ] **Step 4: Run.** Expected: PASS, with all 42 `lth/*` rows green.

```bash
( ulimit -v 16000000; CARGO_BUILD_JOBS=6 timeout 1500 cargo test -p leanr_elab --test oracle_decl --test oracle_file --test seam_audit )
```

If a row fails, compare leanr's H/L pattern with `final_expected.txt` before changing anything. The expected patterns (value/type, H = have, L = let):

| rows | pattern |
|---|---|
| defVal, defHave, defDep, defLam, defLamDep, abbrev, letProofVal, unusedLet, letInArg, defLetTypeOnly, proofArgDep, proofArgNoDep, proofInLetVal, lamTypeDep, auxProofHave, auxProofOutsideLet, letUnderLamTypeOnly, auxProofInLetValue | val H |
| defNested, depAfterNondep, nonPropDepIdx, letInLetVal, haveDep, sameNameTwice | val HH |
| defNestedDep, letTypeAnn | val LH |
| defDepRfl, propDef, thmVal, thmValDep, opaque, nonPropDep, lamBinderDep | val L |
| defType, defTypeArrow, thmType, opaqueType, thmHeaderAsync | ty H |
| letInBinderType | ty H, val H |
| axiomType | ty L |
| example, exampleType | no constants |

- [ ] **Step 5: Run the mutations, then record and revert each one**

| # | mutation | expected killer |
|---|---|---|
| T5a (spec M2) | `let_to_have_value` returns `value` | defVal, abbrev, … (val H rows) |
| T5b (spec M3) | value pass on theorems | thmVal (L → H) |
| T5c (spec M4) | drop the `is_prop_full` gate | propDef, defDepRfl |
| T5d (spec M5) | value pass on opaque | opaque |
| T5e (spec M6) | skip `let_to_have_type` | defType, defTypeArrow, thmType, opaqueType, thmHeaderAsync, letInBinderType |
| T5f (spec M7) | add a type pass to `axiom.rs` | axiomType |
| T5g (spec M8) | type/value pass on `example` | expected EQUIVALENT: an example is only kernel-checked, with no constant emitted. Record it. |
| T5h | letToHave BEFORE `abstract_nested_proofs` | `a_proof_abstracted_under_a_let_is_the_pending_constant_seam` (d29 becomes Ok) |
| T5i | rerun T3c (phase 1 skips let values) | auxProofInLetValue |
| T5j | rerun T2a (no whnf record) | defNestedDep, letTypeAnn, nonPropDep, lamBinderDep, defDepRfl? (Prop gate: no), thmVal? (no) |
| T5k | rerun T3a (`mk_lambda` rebuild) | defHave, haveDep, auxProofHave |

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
git add crates/leanr_elab/src/command/def.rs crates/leanr_elab/tests/oracle_file.rs crates/leanr_elab/tests/oracle_decl.rs crates/leanr_elab/tests/seam_audit.rs
git commit   # "leanr_elab: letToHaveType/letToHaveValue after abstractNestedProofs (closes the letToHave seam)"
```

---

### Task 6: Close-out

**Files:**
- Modify: `docs/superpowers/specs/2026-10-07-let-to-have-design.md`: add § Plan amendments (Plan-time findings 1–7 in short form) and § Landed (commits, rows, floor, mutation table, surviving and equivalent mutations, open seams: pending-constant overlay ← d28/d29/d30, `cleanup.letToHave`, `zetaDeltaSet`/`isImplementationDetail`, the `instance` command).
- Modify: `crates/leanr_meta/src/abstract_proofs.rs` module doc (the `letE` seam bullet is gone; the pending seam now has two callers).
- Modify: `crates/leanr_elab/src/command/axiom.rs:2` only if its comment claims something false (it says "No `letToHave`", which is still true; leave it).
- Modify: `docs/superpowers/specs/2026-10-03-m4c1-single-decl-design.md` § Landed: one line marking "`letToHave` is a seam" CLOSED, with a pointer to this spec.

- [ ] **Step 1:** Write the doc changes above.
- [ ] **Step 2:** Grep for stale text: `grep -rn "letToHave" crates/ docs/ | grep -i "seam\|later M4"`. Every hit is either intended (the pending seam) or fixed.
- [ ] **Step 3: Full CI** (blocking, serialized; see Global Constraints). It must end in `CI_EXIT=0`.
- [ ] **Step 4: Commit** with the doc changes. Push the branch with the gh credential-helper override, and open the PR (summary, rows, floor, mutation table, seams). Do not merge: the controller merges after B.

```bash
git -c credential.https://github.com.helper= -c "credential.https://github.com.helper=!$(which gh) auth git-credential" push origin d-let-to-have
gh pr create --base main --head d-let-to-have --title "leanr: port Meta.letToHave (closes the letToHave seam)" --body-file /workspace/target/wt-d-pr.md
```

---

## Self-review

- **Spec coverage:**
  - Components 1 → Task 2 (tracking + audit), 2 → Task 4, 3 → Task 5.
  - The data flow order is pinned by T5h.
  - Error handling: the restore on Err is pinned by `tracking_scope_restores_on_err`, and there are no new `ElabError` variants.
  - Testing: the corpus is Task 1 and Task 5; spec unit tests 1–5 are in Task 2 and Task 4.
  - The spec's unit test 1, the warm cache, became `tracking_scope_restores_on_err`'s cache assertion plus the T2e equivalence record (finding 4).
  - Spec unit test 4 (`visitDepExpr`) is T4h, recorded as equivalent with its reason.
  - Seams → Task 6.
  - Gaps found and added: the `abstractNestedProofs` let arm (Task 3), the pending seam (Task 5), and snapshot backtracking (Task 2).
- **Placeholders:** none remain. Task 1's `CORPUS_FLOOR` is computed at run time by design, because it depends on the merge order. Tasks 4 and 3 carry uncompiled Rust that was written against the APIs opened at plan time. Each task's notes list what to verify at compile time.
- **Type consistency:**
  - `let_to_have(&mut self, &AuxLemmas, ExprId)` is used the same way in Tasks 4 and 5.
  - `pending_lookup_seam(aux, err, who)` is the same in Tasks 3 and 4.
  - `with_tracking_zeta_delta` returns `Result`, in both Task 2 and Task 4.
  - `push_local_decl_without_instance` takes four arguments (`metactx.rs:912-918`).
- **Review Focus:** all five lines have tests in Task 2 or Task 4.
