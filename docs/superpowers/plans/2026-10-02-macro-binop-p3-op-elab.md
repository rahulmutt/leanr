# Macro/binop% P3: the op elaborator. Implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `leanr_elab` elaborates the whole `binop%` family (`binop%`,
`binop_lazy%`, `unop%`, `leftact%`, `rightact%`, `binrel%`,
`binrel_no_prop%`), both as literal syntax and as P2's table expansions. It
transcribes `Lean/Elab/Extra.lean:154-566`, so `a + b`, `n + z` with
coercions, and `a < b` elaborate the way the oracle elaborates them.

**Architecture:** A new `builtin/op/` module ports the oracle's `Tree`. That
covers `toTree` (which recurses through nested notation by calling P2's
`macros::expand`), `analyze`, `applyCoe` and `toExpr`/`toExprCore`, plus
`elabBinRelCore`. The analysis runs `analyze`'s type comparison under P1's
`with_new_mctx_depth` + `with_def_eq_stuck_ex` + `is_def_eq_guarded`.
Operators are applied through the existing `app::elab_app_args`, with
`resultIsOutParamSupport := false`, which is a new `AppCall` field. Both
entry points come from one `OpView`: `elab.rs`'s `Expanded::Op` arm and
`dispatch`'s new arms for the seven literal kinds. The differential gate is
P2's ElabOp fixture with a hand-written test-support suffix: `Z`, `Arr`, `U`,
`V`, `F`.

**Tech Stack:** Rust (`leanr_elab`; one additive `pub fn` in `leanr_meta`),
Lean 4 dumpers (`lean --run`), mise tasks.

**Spec:** `docs/superpowers/specs/2026-10-01-macro-expansion-binop-design.md`
§ P3. It was amended on 2026-10-02 in commits 44ad43e and a12f1d3. Read
§ P3 › Testing, the test-support suffix, the helpers list, and § Errors.

## Global Constraints

- Pinned oracle `leanprover/lean4:v4.33.0-rc1`. The source is at
  `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/`. Open every
  line before you cite it, and print it with its real number
  (`awk 'NR>=a && NR<=b {print NR": "$0}' FILE`). Plan citations have been
  off by 1–2 lines before. The citations here were opened on 2026-10-02:
  `Extra.lean:154-566`, `Meta/Basic.lean:1157-1158` (`mkFunUnit`),
  `Meta/AppBuilder.lean:364-367` (`mkAppM`), `TermElabM.lean:2211-2224`
  (`resolveId?`).
- `lean-toolchain` is not bumped. No new external dependencies.
- `crates/leanr_kernel` and `crates/leanr_syntax` are untouched.
  `crates/leanr_meta` gets exactly one additive, behaviour-neutral change
  (Task 2): `MetaError::is_oracle_catchable`, extracted from
  `guard_def_eq_result`. This follows the precedent for additive
  TCB-neutral accessors.
- **Elab0 is frozen.** `Elab0.lean`, `Elab0.olean` and `elab-queries.jsonl`
  do not change. The Elab0 gate floor (345) stays green.
- `ElabOp.lean` is **generated**. Never hand-edit it. Edit
  `gen_elab_op.sh` or the new `elab_op_support.lean.in`, then run
  `mise run fixtures:regen-elab-op`. The regen must leave
  `op-expansions.jsonl` byte-identical, because the suffix declares no
  notation.
- CI has no Lean. Commit every regenerated fixture: `ElabOp.lean`,
  `ElabOp.olean` and `op-queries.jsonl`.
- **The dumper turns logged elaboration errors into `sorryAx`.** It only
  catches *thrown* errors. Task 1 adds a gate assertion against this. Never
  commit an op record whose `exp` mentions `sorryAx`. If one appears, the
  query is an oracle error: fix the query or move it to `opErrQueries`.
- Run `cargo fmt --all` before every commit. CI gates on
  `cargo fmt --check` and clippy `-D warnings`.
- Build under `/workspace` only, never `/tmp` (a 20 GiB EmptyDir).
- **Mutation discipline.** Every listed mutation is mandatory. Apply it,
  name the test that goes red, then revert. If it survives, add a killing
  test or record before committing. Record each result in the commit body.
  Treat this plan's "kills" claims as hypotheses until you have run them.
  Earlier plans here shipped many false ones.
- **Every corpus query below was oracle-checked on 2026-10-02** against a
  scratch ElabOp built with exactly the suffix in Task 1, and none yields
  `sorryAx`. They were *not* run through leanr. If one exposes an
  unrelated, pre-existing leanr gap, do not fix it in this slice. Drop the
  row, say so in the commit body, and lower the floor to match. **Exception:**
  every row named in the spec's § P3 › Testing table, plus `op/depth` and
  `op/stuck`, must stay. If one of those fails, stop and report to the
  controller.

## Review Focus

1. **A long left-nested chain** (`a + a + … + a`, 300 operands). `to_tree`,
   `analyze`, `apply_coe` and `to_expr_core` all recurse once per
   operator. Expect `Ok`, not a stack overflow on libtest's 2 MiB thread.
   (Task 3, `long_chain_elaborates`.)
2. **A literal `binop%` whose head is a local.**
   `fun (f : Nat → Nat → Nat) (a b : Nat) => binop% f a b`. `resolveId?`
   resolves locals first, so expect `f a b`. Pre-resolving like the
   expansion path, or looking up only globals, would break it. (Task 3,
   corpus `op/literal-local-head`.)
3. **A cdot paren operand.** `(· + 1) + a` must surface the existing cdot
   seam (`UnsupportedSyntax` naming `Lean.Parser.Term.cdot`), never a panic
   and never a silently different term. (Task 3,
   `cdot_paren_operand_is_the_cdot_seam`.)
4. **An operand that postpones.** `(fun x => x.1 + 0) (PProd.mk 1 2)`: a
   leaf postpones in `to_tree`, and `to_tree`'s
   `synthesize_synthetic_mvars(Yes)` must resume it. Expect the oracle's
   term. (Task 3, corpus `op/postponed-operand`.)
5. **A relation whose operands are relations.** `(a < b) = (b < a)`: each
   operand expands to `binrel%`, which `to_tree` must treat as a *leaf*
   (`go` only recognises the five non-rel kinds). Recursing into it would
   build a `binop` tree over `LT.lt`. (Task 4, corpus `op/rel-of-rels`.)

---

## File structure

| File | Change | Responsibility |
|---|---|---|
| `tests/fixtures/elab/elab_op_support.lean.in` | create | The hand-written test-support suffix |
| `tests/fixtures/elab/gen_elab_op.sh` | append the suffix | |
| `tests/fixtures/elab/ElabOp.lean` / `.olean` | regenerated | |
| `tests/fixtures/elab/dump_elab.lean` | `opQueries` rows + `opErrQueries` | The op corpus source |
| `tests/fixtures/elab/op-queries.jsonl` | regenerated | |
| `crates/leanr_meta/src/error.rs`, `metactx.rs` | `MetaError::is_oracle_catchable` | The `catch _` classification, shared |
| `crates/leanr_elab/src/error.rs` | `ElabError::UnknownConstant` + first line | `throwUnknownConstantAt` |
| `crates/leanr_elab/src/app/mod.rs` | `AppCall::result_is_out_param_support` | `elabAppArgs`' parameter |
| `crates/leanr_elab/src/elab.rs` | `mk_const_with_level_params`; `Expanded::Op` arm | |
| `crates/leanr_elab/src/macros/mod.rs` | `OpKind::ALL`, `OpKind::is_rel` | |
| `crates/leanr_elab/src/builtin/op/mod.rs` | create | `OpView`, `OpHead`, `elab_op_view`, `resolve_head` |
| `crates/leanr_elab/src/builtin/op/tree.rs` | create | `Tree`, `BinOpKind`, `to_tree`, `has_cdot` |
| `crates/leanr_elab/src/builtin/op/analyze.rs` | create | `AnalyzeResult`, `analyze`, `is_unknown`, `has_coe` |
| `crates/leanr_elab/src/builtin/op/to_expr.rs` | create | `apply_coe`, `to_expr`, `to_expr_core`, `mk_app_m`, the two instance predicates, `mk_fun_unit` |
| `crates/leanr_elab/src/builtin/op/rel.rs` | create | `elab_bin_rel_core`, `to_bool_if_necessary` |
| `crates/leanr_elab/src/dispatch.rs` | 7 literal arms + doc table | |
| `crates/leanr_elab/tests/support/mod.rs` | `sorryAx` assertion | |
| `crates/leanr_elab/tests/oracle_op.rs` | floors, seam test retired, new tests | |
| `crates/leanr_elab/tests/op_helpers.rs` | create | White-box tests of the helpers |

The spec names a single `builtin/op.rs`. The port is about 700 lines across
five oracle functions, so it is split by responsibility, following the
repo's `app/` layout. Record this in Task 5's spec § Landed.

---

### Task 1: The ElabOp test-support suffix and the `sorryAx` gate

**Files:**
- Create: `tests/fixtures/elab/elab_op_support.lean.in`
- Modify: `tests/fixtures/elab/gen_elab_op.sh` (append after the Core excerpts loop, at the end of the file)
- Regenerate: `tests/fixtures/elab/ElabOp.lean`, `ElabOp.olean`
- Modify: `crates/leanr_elab/tests/support/mod.rs` (`run_elab_corpus`, the `Ok(g)` arm)
- Modify: `crates/leanr_elab/tests/oracle_op.rs` (new test)

**Interfaces:**
- Produces: ElabOp constants `Z`, `Z.ofNat`, `Arr`, `U`, `V`, `V.mk`, `F`,
  `F.mk`, plus the instances below. Later tasks' corpus queries use them.

- [ ] **Step 1: Write the suffix file** `tests/fixtures/elab/elab_op_support.lean.in`
  verbatim. It was oracle-checked: it compiles appended to ElabOp, and the
  golden file and the existing 19 records stay byte-identical.

```lean
-- ===== op test support (hand-written; macro/binop% spec § P3 › Test-support suffix) =====
-- `Z` is the rows' `Int`: Prelude has no `Int` and no cross-type coercion.
structure Z where
  n : Nat
def Z.ofNat (n : Nat) : Z := ⟨n⟩
instance (n : Nat) : OfNat Z n := ⟨⟨n⟩⟩
instance : Coe Nat Z := ⟨Z.ofNat⟩
instance : Add Z := ⟨fun a b => ⟨a.n + b.n⟩⟩
instance : Sub Z := ⟨fun a b => ⟨a.n - b.n⟩⟩
instance : Mul Z := ⟨fun a b => ⟨a.n * b.n⟩⟩
instance : Div Z := ⟨fun a b => ⟨a.n / b.n⟩⟩
instance : Mod Z := ⟨fun a b => ⟨a.n % b.n⟩⟩
instance : Neg Z := ⟨fun a => a⟩
instance : AndOp Z := ⟨fun a _ => a⟩
instance : OrOp Z := ⟨fun a _ => a⟩
instance : XorOp Z := ⟨fun a _ => a⟩
instance : Append Z := ⟨fun a _ => a⟩
instance : HPow Z Nat Z := ⟨fun a _ => a⟩
instance : SMul Nat Z := ⟨fun _ a => a⟩
instance : OrElse Z := ⟨fun a _ => a⟩
instance : AndThen Z := ⟨fun a _ => a⟩
instance : LT Z := ⟨fun a b => a.n < b.n⟩
instance : LE Z := ⟨fun a b => a.n ≤ b.n⟩
instance : BEq Z := ⟨fun a b => a.n == b.n⟩
-- A second `HMul` default instance (Prelude's `instHMul` is the first):
-- `hasHeterogeneousDefaultInstances` needs more than one (Extra.lean:371).
structure Arr (α : Type) where
  x : α
@[default_instance high] instance [Mul α] : HMul α (Arr α) (Arr α) := ⟨fun a as => ⟨a * as.x⟩⟩
-- No coercion to or from `Nat`, so it is uncomparable with `Nat`. The
-- heterogeneous `HAdd` lets the fallback path elaborate rather than error.
structure U where
  n : Nat
instance : Add U := ⟨fun a _ => a⟩
instance : HAdd Nat U U := ⟨fun _ u => u⟩
-- Prelude has no `Decidable True/False` (they live in Init/Core); `==` on
-- `Prop` coerces through `decide`.
instance : Decidable True := .isTrue True.intro
instance : Decidable False := .isFalse fun h => h
-- The depth row: `V n =?= V ?m` with an outer `?m`.
structure V (n : Nat) where
  mk ::
instance : Add (V n) := ⟨fun a _ => a⟩
instance : Coe Nat (V n) := ⟨fun _ => V.mk⟩
instance : HAdd (V n) Nat (V n) := ⟨fun a _ => a⟩
-- The stuck row: `F n =?= F ?m` succeeds only by unfolding `F`, which
-- `isDefEqStuckEx` forbids.
def F (_ : Nat) : Type := Nat
def F.mk (n : Nat) : F n := (0 : Nat)
instance : Add (F n) := ⟨fun a _ => a⟩
instance : HAdd (F n) Z Z := ⟨fun _ z => z⟩
instance (x : F n) : CoeT (F n) x Z := ⟨⟨0⟩⟩
```

- [ ] **Step 2: Append it in the generator.** Add these lines at the end of
  `gen_elab_op.sh`:

```sh
# macro/binop% P3: hand-written test types (spec § P3 › Test-support
# suffix). Not copied from Init; real Lean elaborates it, so the oracle
# stays authoritative. It must declare no notation (the golden diff below
# would catch one).
cat "$(dirname "$0")/elab_op_support.lean.in"
```

  Also update the header comment's "Whole files, verbatim except…" sentence
  so that it says a hand-written suffix follows.

- [ ] **Step 3: Regenerate.** Run `mise run fixtures:regen-elab-op`. Then
  confirm the expansion golden and the corpus did not change, and that
  ElabOp did:

```bash
git diff --stat tests/fixtures/elab/
# expect: ElabOp.lean, ElabOp.olean, gen_elab_op.sh, elab_op_support.lean.in.
# NOT op-expansions.jsonl, NOT op-queries.jsonl.
```

- [ ] **Step 4: Write the failing gate test.** Add it to `crates/leanr_elab/tests/oracle_op.rs`:

```rust
/// macro/binop% P3 T1: the test-support suffix is in the fixture.
#[test]
fn elab_op_has_the_test_support_suffix() {
    let r = support::replay_fixture_in("elab", "ElabOp.olean");
    let snap = elab_op_grammar();
    for src in [
        "fun (n : Nat) (z : Z) (a : Arr Nat) (u : U) (x : V n) (y : F n) => z",
        "Z.ofNat",
        "V.mk",
        "F.mk",
    ] {
        support::elab_src_in(&r, src, &snap).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    }
}
```

  Run `cargo test -p leanr_elab --test oracle_op elab_op_has_the_test_support_suffix`.
  It should PASS after Step 3. Run the same command with Step 3's fixture
  stashed (`git stash push tests/fixtures/elab/ElabOp.olean`) and confirm it
  fails, then restore the stash.

- [ ] **Step 5: Add the `sorryAx` assertion.** In
  `support::run_elab_corpus`, in the `Ok(g)` arm, add this before the
  comparison with `q["exp"]`. It catches the dumper's errToSorry, which
  emits a logged error as a successful record:

```rust
                    // The dumper (`dump_elab.lean`) only catches THROWN
                    // errors; a LOGGED one becomes `sorryAx` in an
                    // apparently successful record (errToSorry). Such a
                    // record pins an oracle error as a term (macro/binop% P3).
                    assert!(
                        !q["exp"].to_string().contains("\"sorryAx\""),
                        "{id}: the oracle record contains sorryAx -- the \
                         query is an oracle ERROR; move it to the err queries"
                    );
```

- [ ] **Step 6: Run the mutation.** Temporarily append
  `("op/tmp-sorry", "fun (p q : Prop) => p == q")` to `opQueries` in
  `dump_elab.lean`, then regenerate the corpus only:
  `cd tests/fixtures/elab && LEAN_PATH=$PWD lean --run dump_elab.lean ElabOp > op-queries.jsonl`.
  `oracle_op_gate` must fail with "contains sorryAx". Revert both files.

- [ ] **Step 7: Full gates.** Run `cargo test -p leanr_elab --test oracle_op --test oracle_elab`.
  Both should PASS, with Elab0 at 345 and op at 19.

- [ ] **Step 8: Commit.**

```bash
cargo fmt --all
git add tests/fixtures/elab/ crates/leanr_elab/tests/
git commit -m "ElabOp: hand-written test-support suffix + sorryAx corpus gate (macro/binop% P3 T1)"
```

---

### Task 2: Plumbing: `UnknownConstant`, out-param flag, catchable errors, `OpKind` helpers, level-param constants

**Files:**
- Modify: `crates/leanr_meta/src/error.rs`, `crates/leanr_meta/src/metactx.rs:1996-2011` (`guard_def_eq_result`)
- Modify: `crates/leanr_elab/src/error.rs` (variant + `oracle_first_line` arm + unit test)
- Modify: `crates/leanr_elab/src/app/mod.rs:449-456` (`AppCall`), `:577` (`result_is_out_param_support`), and every `AppCall {` literal (8 sites: `grep -rn "AppCall {" crates/leanr_elab/src`)
- Modify: `crates/leanr_elab/src/elab.rs:165-198` (split `mk_const_with_fresh_mvar_levels_of`)
- Modify: `crates/leanr_elab/src/macros/mod.rs` (`OpKind::ALL`, `is_rel`)

**Interfaces:**
- Produces:
  - `leanr_meta::MetaError::is_oracle_catchable(&self) -> bool`
  - `ElabError::UnknownConstant(String)`, whose `oracle_first_line()` is ``Some(format!("Unknown constant `{name}`"))``
  - `AppCall { …, pub result_is_out_param_support: bool }`
  - `TermElabM::mk_const_with_level_params(&mut self, name: NameId) -> Result<ExprId, ElabError>`
  - `OpKind::ALL: [OpKind; 7]`, `OpKind::is_rel(self) -> bool`

- [ ] **Step 1: Write the failing tests.** In `crates/leanr_elab/src/error.rs`'s `mod tests`:

```rust
    #[test]
    fn unknown_constant_first_line_is_the_oracles() {
        // oracle: `throwUnknownConstantAt` (probed 2026-10-02 against
        // ElabOp: `binop% NoSuch a b` -> "Unknown constant `NoSuch`").
        assert_eq!(
            ElabError::UnknownConstant("NoSuch".into()).oracle_first_line().as_deref(),
            Some("Unknown constant `NoSuch`")
        );
    }
```

  In `crates/leanr_meta/src/error.rs` (add `#[cfg(test)] mod tests` if absent):

```rust
    #[test]
    fn runtime_and_seam_errors_are_not_catchable() {
        use leanr_kernel::KernelError;
        for e in [
            MetaError::DepthBudgetExhausted,
            MetaError::StepBudgetExhausted,
            MetaError::Unsupported("x".into()),
            MetaError::MVar("x".into()),
            MetaError::Kernel(KernelError::BankExhausted),
            MetaError::Kernel(KernelError::DeepRecursion),
        ] {
            assert!(!e.is_oracle_catchable(), "{e:?}");
        }
        assert!(MetaError::IsDefEqStuck.is_oracle_catchable());
    }
```

  (Check the exact variant names and payload types in `error.rs` before
  writing this. `IsDefEqStuck` is P1's variant; adjust the spelling to
  match.)

- [ ] **Step 2: Run the tests and watch them fail.**
  Run `cargo test -p leanr_elab --lib unknown_constant_first_line` and
  `cargo test -p leanr_meta --lib runtime_and_seam_errors`. Expect compile
  errors.

- [ ] **Step 3: Implement.**

  `leanr_meta/src/error.rs`:

```rust
impl MetaError {
    /// Whether the oracle's `try … catch _` catches this error. Runtime
    /// exceptions (maxRecDepth <-> `DepthBudgetExhausted`, heartbeats <->
    /// `StepBudgetExhausted`, kernel resource exhaustion) are not caught by
    /// `Core.tryCatch`. `Unsupported` (a named leanr seam) and `MVar` (a
    /// caller bug) are leanr gaps, not oracle exceptions. Shared by
    /// `MetaCtx::is_def_eq_guarded` and the elaborator's `catch _` ports
    /// (macro/binop% P3 `has_homogeneous_instance`).
    pub fn is_oracle_catchable(&self) -> bool {
        !matches!(
            self,
            MetaError::DepthBudgetExhausted
                | MetaError::StepBudgetExhausted
                | MetaError::Unsupported(_)
                | MetaError::MVar(_)
                | MetaError::Kernel(
                    leanr_kernel::KernelError::BankExhausted
                        | leanr_kernel::KernelError::DeepRecursion
                )
        )
    }
}
```

  Rewrite `guard_def_eq_result` (`metactx.rs`) on top of it, with no
  behaviour change:

```rust
    pub(crate) fn guard_def_eq_result(r: Result<bool, MetaError>) -> Result<bool, MetaError> {
        match r {
            Err(e) if e.is_oracle_catchable() => Ok(false),
            other => other,
        }
    }
```

  `leanr_elab/src/error.rs`: add this variant next to `UnknownIdent`:

```rust
    /// oracle: `throwUnknownConstantAt` — the `binop%` family's head did not
    /// resolve (`Extra.lean:216`, `:223`, `:554`).
    UnknownConstant(String),
```

  Add an arm to `ElabError::oracle_first_line`:
  ``Self::UnknownConstant(n) => Some(format!("Unknown constant `{n}`")),``.
  If `ElabError` has a `Display` impl with an exhaustive match, add the arm
  there too, with the same text.

  `app/mod.rs`: add a field to `AppCall` with this doc:

```rust
    /// oracle: `elabAppArgs`' `resultIsOutParamSupport` parameter (default
    /// `true`). Only the `binop%` family passes `false` (`Extra.lean:321`,
    /// `:324`, `:550`).
    pub result_is_out_param_support: bool,
```

  Set `result_is_out_param_support: true` in all 8 existing `AppCall {`
  literals. In `elab_app_args`, destructure the field and change `:577` to:

```rust
        result_is_out_param_support: result_is_out_param_support
            && env_contains_coe_m(elab)?
            && !explicit,
```

  (Keep the existing comment, extended with one sentence: "`&&` with the
  caller's flag, `App.lean:1355`".)

  `elab.rs`: split `mk_const_with_fresh_mvar_levels_of` in two. The first
  half becomes:

```rust
    /// oracle: `mkConstWithLevelParams` — `name` at its declared level
    /// PARAMS. The first half of [`Self::mk_const_with_fresh_mvar_levels_of`];
    /// `builtin::op`'s `mk_app_m` refreshes the levels itself, INSIDE a
    /// `with_new_mctx_depth` scope, so the fresh level mvars are assignable
    /// there.
    pub(crate) fn mk_const_with_level_params(&mut self, name: NameId) -> Result<ExprId, ElabError> {
        // (moved verbatim: params -> level_param list -> intern -> expr_const)
    }
```

  `mk_const_with_fresh_mvar_levels_of` then calls it and refreshes the
  levels.

  `macros/mod.rs`:

```rust
impl OpKind {
    pub const ALL: [OpKind; 7] = [
        OpKind::BinOp,
        OpKind::BinOpLazy,
        OpKind::BinRel,
        OpKind::BinRelNoProp,
        OpKind::UnOp,
        OpKind::LeftAct,
        OpKind::RightAct,
    ];

    /// `binrel%`/`binrel_no_prop%`: elaborated by `elabBinRelCore`, and a
    /// LEAF inside another op's tree (`toTree.go` matches only the other
    /// five, `Extra.lean:196-200`).
    pub fn is_rel(self) -> bool {
        matches!(self, OpKind::BinRel | OpKind::BinRelNoProp)
    }
}
```

- [ ] **Step 4: Run the tests and watch them pass.** Run
  `cargo test -p leanr_meta` and `cargo test -p leanr_elab`. Everything
  should PASS. The leanr_meta, synth and elab corpora are unchanged
  (`guard_def_eq_result` keeps its behaviour, and every existing call site
  passes `true`).

- [ ] **Step 5: Run the mutations.**
  (a) In `elab_app_args`, drop `result_is_out_param_support &&`. Nothing
  can see this until Task 3. Record it as "covered by T3 mutation (h)".
  (b) In `is_oracle_catchable`, drop the `MVar(_)` arm. Expect
  `runtime_and_seam_errors_are_not_catchable` to go red.
  (c) Change the `oracle_first_line` arm's text to "unknown constant".
  Expect `unknown_constant_first_line_is_the_oracles` to go red. Revert
  each one.

- [ ] **Step 6: Commit.**

```bash
cargo fmt --all
git add crates/leanr_meta/src crates/leanr_elab/src
git commit -m "leanr_elab: UnknownConstant, AppCall out-param flag, catchable MetaError, OpKind::ALL (macro/binop% P3 T2)"
```

---

### Task 3: The op elaborator for `binop%`, `binop_lazy%`, `unop%`, `leftact%` and `rightact%`

**Files:**
- Create: `crates/leanr_elab/src/builtin/op/{mod,tree,analyze,to_expr}.rs`
- Create: `crates/leanr_elab/src/builtin/op/rel.rs`. Task 3 makes it a stub that returns the named seam. Task 4 fills it in.
- Modify: `crates/leanr_elab/src/builtin/mod.rs` (`pub mod op;`)
- Modify: `crates/leanr_elab/src/elab.rs:672-682` (`Expanded::Op` arm)
- Modify: `crates/leanr_elab/src/dispatch.rs` (7 literal arms before the catch-all; deferral-table row)
- Modify: `tests/fixtures/elab/dump_elab.lean` (`opQueries`, `opErrQueries`, `main`)
- Regenerate: `tests/fixtures/elab/op-queries.jsonl`
- Modify: `crates/leanr_elab/tests/oracle_op.rs`
- Create: `crates/leanr_elab/tests/op_helpers.rs`

**Interfaces:**
- Consumes (T2): `ElabError::UnknownConstant`, `AppCall::result_is_out_param_support`,
  `TermElabM::mk_const_with_level_params`, `OpKind::{ALL, is_rel}`,
  `MetaError::is_oracle_catchable`.
- Consumes (existing): `macros::{expand, Expansion, OpKind}`;
  `elab::TermTarget::{Stx, Expanded}` and `TermElabM::elab_target`;
  `app::{elab_app_args, AppCall}`; `app::expand::Arg::Expr`;
  `app::head::{intern_dotted, intern_prefixes, mk_const}`;
  `resolve::{resolve_local_name, resolve_global_name}`;
  `app::lval::{node, app_fn}`; `builtin::binder::fun::cleanup_annotations`;
  `TermElabM::{mk_coe, ensure_has_type, synthesize_synthetic_mvars}`;
  `synthetic::PostponeBehavior`;
  `MetaCtx::{with_new_mctx_depth, with_def_eq_stuck_ex, is_def_eq_guarded,
  coerce_simple, try_synth_instance, default_instances_of, push_local_decl,
  lctx_checkpoint, lctx_restore, instantiate1, mk_const_with_fresh_mvar_levels}`.
- Produces:
  - `builtin::op::OpView { kind, head, args, r#ref }` with `from_expansion(&SynElem, &Expansion) -> Option<OpView>` and `from_literal(&SynElem, &KindInterner) -> Result<Option<OpView>, ElabError>`
  - `builtin::op::elab_op_view(&mut TermElabM, &OpView, &KindInterner, Option<ExprId>) -> Result<ExprId, ElabError>`
  - `pub` white-box helpers, used by `tests/op_helpers.rs` and marked `#[doc(hidden)]`:
    `analyze::is_unknown`, `analyze::has_coe`, `to_expr::mk_fun_unit`,
    `to_expr::mk_app_m`, `to_expr::has_homogeneous_instance`,
    `to_expr::has_heterogeneous_default_instances`, and
    `op::test_const(&mut TermElabM, &str) -> Result<ExprId, ElabError>` (a
    constant at fresh levels, for building test types)
  - `rel::elab_bin_rel_core(elab, view, no_prop: bool, kinds, expected)`. In T3 it returns
    `Err(ElabError::UnsupportedSyntax(view.kind.syntax_kind().into()))`.

- [ ] **Step 1: Add the corpus queries.** In `dump_elab.lean`, append the
  rows below to `opQueries` (before the closing `]`). Add a new `opErrQueries`,
  and change `main`'s ElabOp arm to
  ``| ["ElabOp"] => (`ElabOp, opQueries, opErrQueries)``.

```lean
  -- macro/binop% P3 T3: the `binop%` elaborator (Extra.lean:154-482).
  -- `a + b * c`: one tree through the nested expansion
  , ("op/add-mul",          "fun (a b c : Nat) => a + b * c")
  -- leaf coercion to the max type, both orders
  , ("op/coe-left",         "fun (n : Nat) (z : Z) => n + z")
  , ("op/coe-right",        "fun (n : Nat) (z : Z) => z + n")
  -- unknown `0` becomes `(0 : Z)`, not `↑(0 : Nat)` (Extra.lean:285-287)
  , ("op/unknown-numeral",  "fun (n : Nat) (z : Z) => (n + 0) + z")
  -- `has_heterogeneous_default_instances`: `2` stays uncoerced, then `Nat`
  , ("op/hetero-default",   "fun (a : Arr Nat) => 2 * a")
  -- `rightact%` leaves the exponent a leaf, outside the analysis
  , ("op/rightact-pow",     "fun (n : Nat) (z : Z) => z ^ n")
  , ("op/rightact-pow-lit", "fun (z : Z) => z ^ 2")
  -- uncomparable `Nat`/`U`: plain elaboration through `HAdd Nat U U`
  , ("op/uncomparable",     "fun (n : Nat) (u : U) => n + u")
  -- depth: `V n =?= V ?m` must NOT assign the outer `?m` -> uncomparable ->
  -- `k` stays `Nat` (instHAddVNat); without depth `k` is coerced to `V n`
  , ("op/depth",            "fun (n k : Nat) (x : V n) => x + (V.mk : V _) + k")
  , ("op/depth-mid",        "fun (n k : Nat) (x : V n) => x + k + (V.mk : V _)")
  -- isDefEqStuckEx: `F n =?= F ?m` would succeed by unfolding `F`; stuck
  -- -> uncomparable -> `x`, `F.mk _` stay `F n` (instHAddFZ)
  , ("op/stuck",            "fun (n : Nat) (x : F n) (z : Z) => x + F.mk _ + z")
  -- … and with no mvar the same types ARE comparable: `x` is coerced
  , ("op/coe-unfold",       "fun (n : Nat) (x : F n) (z : Z) => x + z")
  -- binop_lazy%: the rhs is `fun _ : Unit => b`
  , ("op/lazy-orelse",      "fun (a b : Z) => a <|> b")
  , ("op/lazy-andthen",     "fun (a b : Z) => a >> b")
  -- the remaining binop rows of the table
  , ("op/lor",              "fun (a b : Z) => a ||| b")
  , ("op/xor",              "fun (a b : Z) => a ^^^ b")
  , ("op/land",             "fun (a b : Z) => a &&& b")
  , ("op/sub",              "fun (a b : Z) => a - b")
  , ("op/div",              "fun (a b : Z) => a / b")
  , ("op/mod",              "fun (a b : Z) => a % b")
  , ("op/append",           "fun (a b : Z) => a ++ b")
  -- unop%, and a coerced operand under it
  , ("op/neg",              "fun (a : Z) => -a")
  , ("op/neg-coe",          "fun (n : Nat) (z : Z) => -n + z")
  -- leftact%: the lhs is a leaf
  , ("op/smul",             "fun (n : Nat) (a : Z) => n • a")
  -- the literal forms, and a literal head that is a LOCAL (resolveId?)
  , ("op/literal-binop",    "fun (a b : Nat) => binop% HAdd.hAdd a b")
  , ("op/literal-unop",     "fun (a : Z) => unop% Neg.neg a")
  , ("op/literal-local-head", "fun (f : Nat → Nat → Nat) (a b : Nat) => binop% f a b")
  -- the expected type seeds `max`
  , ("op/expected",         "fun (n : Nat) => (n + 1 : Z)")
  , ("op/nested-coe",       "fun (n : Nat) (z : Z) => n * n + z")
  -- hygiene: a local named like the head's namespace does not capture it
  , ("op/hygiene-op",       "fun (HAdd : Nat) (a b : Nat) => a + b")
  , ("op/numerals",         "2 + 3")
  -- an mvar expected type (the argument of `id`) and a beta-redex argument
  , ("op/id-arg",           "fun (a b : Nat) => id (a + b)")
  , ("op/beta-arg",         "fun (z : Z) => (fun x => x) (z + 1)")
  -- a leaf that postpones (lval on an mvar-typed local) and resumes in
  -- `toTree`'s `synthesizeSyntheticMVars (postpone := .yes)`
  , ("op/postponed-operand", "(fun x => x.1 + 0) (PProd.mk 1 2)")
```

```lean
/-- macro/binop% P3: op queries the ORACLE rejects (`{"id","src","err"}`). -/
def opErrQueries : List (String × String) :=
  [ ("op/unknown-binop",    "fun (a b : Nat) => binop% NoSuch a b") ]
```

  Regenerate the corpus:
  `cd tests/fixtures/elab && LEAN_PATH=$PWD lean --run dump_elab.lean ElabOp > op-queries.jsonl`.
  Expect no stderr. Then run `grep -c sorryAx op-queries.jsonl`, which must
  print `0`. `op/literal-local-head` and `op/postponed-operand` were not
  probed. If either errors or yields `sorryAx`, adjust it and note why in
  the commit body. `wc -l op-queries.jsonl` should print 54 (19 + 34 + 1).

- [ ] **Step 2: Raise the floor, retire the seam test, and add white-box
  tests (all failing).** In `oracle_op.rs`:
  - `CORPUS_FLOOR: 19 -> 54`. Extend the comment: "19 -> 54 (P3 T3): the
    binop/unop/act/lazy rows, the depth/stuck rows, and the unknown-head
    err row."
  - Replace `op_notations_stop_at_the_literal_kind_seam` with
    `rel_notations_stop_at_the_literal_kind_seam`. Keep the same body, but
    filter the golden file to `g["exp"]` ∈ {`Lean.Parser.Term.binrel`,
    `Lean.Parser.Term.binrel_no_prop`}, and push only the literal
    `"fun (a b : Nat) => binrel% LT.lt a b"` /
    `"Lean.Parser.Term.binrel"` case. (Task 4 deletes it.)
  - Add:

```rust
/// Every non-rel op notation reaches the elaborator: each golden source
/// elaborates over `Z` operands (the corpus pins the terms).
#[test]
fn non_rel_op_notations_elaborate() {
    let r = support::replay_fixture_in("elab", "ElabOp.olean");
    let snap = elab_op_grammar();
    for g in golden().iter().filter(|g| {
        let k = g["exp"].as_str().unwrap();
        k != "Lean.Parser.Term.app" && !k.contains("binrel")
    }) {
        let src = g["src"].as_str().unwrap();
        // `•` is `SMul Nat Z`; `^` is `HPow Z Nat Z`.
        let binders = match g["exp"].as_str().unwrap() {
            "Lean.Parser.Term.leftact" => "(a : Nat) (b : Z)",
            "Lean.Parser.Term.rightact" => "(a : Z) (b : Nat)",
            _ => "(a b : Z)",
        };
        let src = format!("fun {binders} => {src}");
        support::elab_src_in(&r, &src, &snap).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    }
}

/// Review Focus #1: a 300-operand left-nested chain. One recursion per
/// operator in `to_tree`, `analyze`, `apply_coe` and `to_expr_core`.
#[test]
fn long_chain_elaborates() {
    let r = support::replay_fixture_in("elab", "ElabOp.olean");
    let snap = elab_op_grammar();
    let src = format!("fun (a : Nat) => {}", vec!["a"; 300].join(" + "));
    support::elab_src_in(&r, &src, &snap).unwrap_or_else(|e| panic!("{e:?}"));
}

/// Review Focus #3: a cdot paren operand is a LEAF (Extra.lean:201-205), so
/// it reaches the existing cdot seam rather than being recursed into.
#[test]
fn cdot_paren_operand_is_the_cdot_seam() {
    let r = support::replay_fixture_in("elab", "ElabOp.olean");
    let snap = elab_op_grammar();
    match support::elab_src_in(&r, "fun (a : Nat) => (· + 1) + a", &snap) {
        Err(leanr_elab::ElabError::UnsupportedSyntax(k)) => {
            assert!(k.contains("cdot"), "{k}")
        }
        other => panic!("expected the cdot seam, got {other:?}"),
    }
}
```

  (If `(· + 1)` does not parse whole with ElabOp's grammar, use the spelling
  that does. `parse_whole` in this file shows how to check. The assertion is
  what matters.)

  Create `tests/op_helpers.rs`:

```rust
//! White-box tests of the `binop%` elaborator's helpers (macro/binop% P3),
//! over ElabOp's test-support types. The corpus pins whole terms; these pin
//! the predicates the corpus cannot isolate.

mod support;

use leanr_elab::builtin::op::{analyze, test_const, to_expr};

fn with_elab<R>(k: impl FnOnce(&mut leanr_elab::TermElabM) -> R) -> R {
    let r = support::replay_fixture_in("elab", "ElabOp.olean");
    let snap = support::elab_op_grammar_for_tests(); // see note below
    support::with_record_elab(&r, "Nat", &snap, |elab, _, _| k(elab))
}

#[test]
fn has_coe_follows_the_coercion_direction() {
    with_elab(|elab| {
        let nat = test_const(elab, "Nat").unwrap();
        let z = test_const(elab, "Z").unwrap();
        let u = test_const(elab, "U").unwrap();
        assert!(analyze::has_coe(elab, nat, z).unwrap());
        assert!(!analyze::has_coe(elab, z, nat).unwrap());
        assert!(!analyze::has_coe(elab, nat, u).unwrap());
        assert!(!analyze::has_coe(elab, u, nat).unwrap());
    })
}

#[test]
fn has_coe_restores_the_local_context() {
    with_elab(|elab| {
        let nat = test_const(elab, "Nat").unwrap();
        let z = test_const(elab, "Z").unwrap();
        let before = elab.mctx.lctx_checkpoint();
        analyze::has_coe(elab, nat, z).unwrap();
        assert_eq!(elab.mctx.lctx_checkpoint(), before);
    })
}

#[test]
fn homogeneous_instance_needs_cls_max_max_max() {
    with_elab(|elab| {
        let hadd = test_const(elab, "HAdd.hAdd").unwrap();
        let hpow = test_const(elab, "HPow.hPow").unwrap();
        let z = test_const(elab, "Z").unwrap();
        let u = test_const(elab, "U").unwrap();
        assert!(to_expr::has_homogeneous_instance(elab, hadd, z).unwrap());
        // `HPow Z Nat Z` exists, `HPow Z Z Z` does not.
        assert!(!to_expr::has_homogeneous_instance(elab, hpow, z).unwrap());
        // `Add U` exists, so `HAdd U U U` via `instHAdd`.
        assert!(to_expr::has_homogeneous_instance(elab, hadd, u).unwrap());
        // A non-constant head is `false` (Extra.lean:388).
        let nat = test_const(elab, "Nat").unwrap();
        assert!(!to_expr::has_homogeneous_instance(elab, nat, z).unwrap());
    })
}

#[test]
fn heterogeneous_default_instances_need_two_and_the_right_side() {
    with_elab(|elab| {
        let hmul = test_const(elab, "HMul.hMul").unwrap();
        let hadd = test_const(elab, "HAdd.hAdd").unwrap();
        let arr = test_const(elab, "Arr").unwrap();
        let nat = test_const(elab, "Nat").unwrap();
        let arr_nat = support::mk_app(elab, arr, nat);
        // `HMul α (Arr α) (Arr α)`: Arr is the RHS type, so lhs = true.
        assert!(to_expr::has_heterogeneous_default_instances(elab, hmul, arr_nat, true).unwrap());
        assert!(!to_expr::has_heterogeneous_default_instances(elab, hmul, arr_nat, false).unwrap());
        // `HAdd` has one default instance (`instHAdd`): never.
        assert!(!to_expr::has_heterogeneous_default_instances(elab, hadd, arr_nat, true).unwrap());
    })
}

#[test]
fn mk_app_m_fails_on_a_type_mismatch_and_leaves_no_assignment() {
    with_elab(|elab| {
        let z = test_const(elab, "Z").unwrap();
        let hadd = test_const(elab, "HAdd").unwrap();
        let zero = test_const(elab, "Nat.zero").unwrap(); // a term, not a type
        let hadd_name = support::const_name(elab, hadd);
        assert!(to_expr::mk_app_m(elab, hadd_name, &[z, z, z]).unwrap().is_some());
        assert!(to_expr::mk_app_m(elab, hadd_name, &[zero, z, z]).unwrap().is_none());
    })
}

#[test]
fn is_unknown_is_an_mvar_head() {
    with_elab(|elab| {
        let nat = test_const(elab, "Nat").unwrap();
        assert!(!analyze::is_unknown(elab, nat));
        let m = support::fresh_type_mvar(elab);
        assert!(analyze::is_unknown(elab, m));
        let app = support::mk_app(elab, m, nat);
        assert!(analyze::is_unknown(elab, app));
    })
}

#[test]
fn mk_fun_unit_is_a_unit_lambda() {
    with_elab(|elab| {
        let z = test_const(elab, "Nat.zero").unwrap();
        let f = to_expr::mk_fun_unit(elab, z).unwrap();
        let ty = elab.mctx.infer_type(f).unwrap();
        let want = support::parse_type(elab, "Unit → Nat");
        assert!(elab.mctx.is_def_eq(ty, want).unwrap());
    })
}
```

  `support/` helper notes. Add what is missing, and reuse what exists:
  - `elab_op_grammar_for_tests()` is the same body as `oracle_op.rs`'s
    `elab_op_grammar`. Move that function into `support/mod.rs` and call it
    from both.
  - `mk_app(elab, f, a)` is `elab.mctx.store_mut().expr_app(Some(base), f, a)`.
  - `const_name(elab, c)` returns the `NameId` of a `Node::Const`.
  - `fresh_type_mvar(elab)` is a natural mvar of type `Type`, built with the
    public `TermElabM` mvar API that the existing support helpers use
    (`grep -n "fn mk_fresh" crates/leanr_elab/src/elab.rs`).
  - `parse_type(elab, src)` elaborates `src` with this `elab` (the
    `elab_type_expr` pattern at `support/mod.rs:362`).

- [ ] **Step 3: Run the tests and watch them fail.** Run
  `cargo test -p leanr_elab --test oracle_op --test op_helpers`. Expect
  compile failure (`builtin::op` does not exist yet). Then expect
  `oracle_op_gate` to fail on 35 op records with
  `UnsupportedSyntax(Lean.Parser.Term.binop)` and the like.

- [ ] **Step 4: Implement `builtin/op/mod.rs`.**

```rust
//! The `binop%` family elaborator (macro/binop% P3; design spec § P3).
//! oracle: `Lean/Elab/Extra.lean:154-566`.
//!
//! The oracle's doc (`Extra.lean:80-152`) explains the protocol: a whole
//! tree of nested `binop%`/`unop%`/`leftact%`/`rightact%` notation is
//! elaborated at once. Its leaves are elaborated WITHOUT an expected type.
//! Their types are joined to a "maximal" type along coercions (`analyze`).
//! The leaves are then coerced up to it (`apply_coe`). Only then are the
//! operators applied (`to_expr_core`).
//!
//! Two entry points share [`OpView`]: P2's table expansions (`elab.rs`'s
//! `TermTarget::Expanded`, with a pre-resolved global head: hygiene) and
//! the literal syntax `binop% f a b` (`dispatch`, head resolved by
//! `resolveId?`).
//!
//! Not modelled: info trees (the oracle's `Tree.term` payload and
//! `withTermInfoContext'`), and the trace classes. `withRef` is not
//! modelled either: leanr's errors carry no positions yet.

pub mod analyze;
mod rel;
pub mod to_expr;
mod tree;

use leanr_kernel::bank::ExprId;
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::NodeOrToken;

use crate::dispatch::{non_trivia_children, SynElem};
use crate::elab::TermElabM;
use crate::error::ElabError;
use crate::macros::{Expansion, OpKind};

/// Where an op node's head comes from.
#[derive(Debug, Clone)]
pub(crate) enum OpHead {
    /// A table expansion: the quotation's pre-resolved global.
    Global(&'static str),
    /// Literal syntax: the identifier as written, for `resolveId?`.
    Ident(SynElem),
}

/// One `binop%`-family node, from either entry point.
#[derive(Debug, Clone)]
pub(crate) struct OpView {
    pub kind: OpKind,
    pub head: OpHead,
    /// Operand subtrees: two, or one for `unop%`.
    pub args: Vec<SynElem>,
    /// The original syntax: the notation node, or the literal node.
    pub r#ref: SynElem,
}

impl OpView {
    pub(crate) fn from_expansion(r#ref: &SynElem, exp: &Expansion) -> Option<OpView> {
        match exp {
            Expansion::Op { kind, f, args } => Some(OpView {
                kind: *kind,
                head: OpHead::Global(f),
                args: args.clone(),
                r#ref: r#ref.clone(),
            }),
            Expansion::App { .. } => None,
        }
    }

    /// A literal node: non-trivia children `[atom, f, a, b]`, or
    /// `[atom, f, a]` for `unop%` (`term_app.rs`'s
    /// `register_binop_family`). `Ok(None)`: not one of the seven kinds.
    pub(crate) fn from_literal(
        elem: &SynElem,
        kinds: &KindInterner,
    ) -> Result<Option<OpView>, ElabError> {
        let name = kinds.name(elem.kind());
        let Some(kind) = OpKind::ALL.into_iter().find(|k| k.syntax_kind() == name) else {
            return Ok(None);
        };
        let node = elem
            .as_node()
            .ok_or_else(|| ElabError::IllFormedSyntax(format!("{name}: a token")))?;
        let ch = non_trivia_children(node);
        let arity = if kind == OpKind::UnOp { 1 } else { 2 };
        if ch.len() != arity + 2 {
            return Err(ElabError::IllFormedSyntax(format!(
                "{name}: {} children, expected {}",
                ch.len(),
                arity + 2
            )));
        }
        Ok(Some(OpView {
            kind,
            head: OpHead::Ident(ch[1].clone()),
            args: ch[2..].to_vec(),
            r#ref: elem.clone(),
        }))
    }
}

/// oracle: `elabOp` (`Extra.lean:475-482`) and `elabBinRel{,NoProp}`
/// (`:564-566`).
pub(crate) fn elab_op_view(
    elab: &mut TermElabM,
    view: &OpView,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    match view.kind {
        OpKind::BinRel => rel::elab_bin_rel_core(elab, view, false, kinds, expected),
        OpKind::BinRelNoProp => rel::elab_bin_rel_core(elab, view, true, kinds, expected),
        _ => {
            let tree = tree::to_tree_view(elab, view, kinds)?;
            to_expr::to_expr(elab, &tree, expected, kinds)
        }
    }
}

/// `processBinOp`/`processUnOp`'s
/// `let some f ← resolveId? f | throwUnknownConstantAt f f.getId`
/// (`Extra.lean:216`, `:223`, `:554`). A table head is the quotation's
/// pre-resolved global: `mkConst` with fresh levels, never a local.
pub(crate) fn resolve_head(elab: &mut TermElabM, head: &OpHead) -> Result<ExprId, ElabError> {
    match head {
        OpHead::Global(f) => {
            let name = crate::app::head::intern_dotted(elab, f)?;
            if elab.view.get(name).is_none() {
                return Err(ElabError::UnknownConstant(f.to_string()));
            }
            crate::app::head::mk_const(elab, name, &[], f)
        }
        OpHead::Ident(elem) => {
            let raw = match elem {
                NodeOrToken::Token(t) => t.text().to_string(),
                NodeOrToken::Node(_) => {
                    return Err(ElabError::IllFormedSyntax("identifier expected".into()))
                }
            };
            resolve_id(elab, &raw)?.ok_or(ElabError::UnknownConstant(raw))
        }
    }
}

/// oracle: `resolveId?` (`TermElabM.lean:2211-2224`): `resolveName`, keep
/// the candidates with NO leftover field projections, `none` if there is
/// none. `resolveName` tries locals first (a local hit hides the globals
/// even when its projections are then filtered away). `catch _ => []` keeps
/// only the not-found case: leanr's resolver reports a miss as
/// `UnknownIdent`. Every other error propagates.
fn resolve_id(elab: &mut TermElabM, raw: &str) -> Result<Option<ExprId>, ElabError> {
    let parts: Vec<&str> = raw.split('.').collect();
    let prefixes = crate::app::head::intern_prefixes(elab, &parts)?;
    if let Some((fvar, n_fields)) = crate::resolve::resolve_local_name(&elab.mctx, &prefixes) {
        return Ok((n_fields == 0).then_some(fvar));
    }
    match crate::resolve::resolve_global_name(&elab.view, &prefixes, raw) {
        Ok((cname, 0)) => Ok(Some(crate::app::head::mk_const(elab, cname, &[], raw)?)),
        Ok(_) | Err(ElabError::UnknownIdent(_)) => Ok(None),
        Err(e) => Err(e),
    }
}

/// White-box test hook: the constant `name` at fresh level mvars.
#[doc(hidden)]
pub fn test_const(elab: &mut TermElabM, name: &str) -> Result<ExprId, ElabError> {
    let n = crate::app::head::intern_dotted(elab, name)?;
    crate::app::head::mk_const(elab, n, &[], name)
}
```

  (`resolve_global_name` returns `AmbiguousIdent` for an ambiguous name.
  The oracle throws "ambiguous term" there too, so propagating it is
  correct.)

- [ ] **Step 5: Implement `builtin/op/tree.rs`.**

```rust
//! oracle: `Tree` and `toTree` (`Extra.lean:154-230`).

use leanr_kernel::bank::ExprId;
use leanr_syntax::kind::KindInterner;

use super::{resolve_head, OpView};
use crate::dispatch::{non_trivia_children, SynElem};
use crate::elab::{TermElabM, TermTarget};
use crate::error::ElabError;
use crate::macros::OpKind;
use crate::synthetic::PostponeBehavior;

/// oracle: `BinOpKind` (`:154-158`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BinOpKind {
    Regular,
    Lazy,
    LeftAct,
    RightAct,
}

/// oracle: `Tree` (`:160-180`). The `infoTrees` payload and the macro name
/// are dropped (no info trees in leanr).
#[derive(Debug, Clone)]
pub(crate) enum Tree {
    Term { r#ref: SynElem, val: ExprId },
    BinOp { r#ref: SynElem, kind: BinOpKind, f: ExprId, lhs: Box<Tree>, rhs: Box<Tree> },
    UnOp { r#ref: SynElem, f: ExprId, arg: Box<Tree> },
    MacroExpansion { stx: SynElem, nested: Box<Tree> },
}

impl Tree {
    pub(crate) fn ref_elem(&self) -> &SynElem {
        match self {
            Tree::Term { r#ref, .. } | Tree::BinOp { r#ref, .. } | Tree::UnOp { r#ref, .. } => r#ref,
            Tree::MacroExpansion { stx, .. } => stx,
        }
    }
}

/// oracle: `toTree` (`:183-191`) on syntax already known to be an op node:
/// `go`, then `synthesizeSyntheticMVars (postpone := .yes)`.
pub(crate) fn to_tree_view(
    elab: &mut TermElabM,
    view: &OpView,
    kinds: &KindInterner,
) -> Result<Tree, ElabError> {
    let t = process_view(elab, view, kinds)?;
    elab.synthesize_synthetic_mvars(PostponeBehavior::Yes, kinds)?;
    Ok(t)
}

/// oracle: `toTree` on an arbitrary operand (`binrel%`'s two sides).
pub(crate) fn to_tree(elab: &mut TermElabM, s: &SynElem, kinds: &KindInterner) -> Result<Tree, ElabError> {
    let t = go(elab, s, kinds)?;
    elab.synthesize_synthetic_mvars(PostponeBehavior::Yes, kinds)?;
    Ok(t)
}

/// oracle: `toTree.go` (`:192-211`).
fn go(elab: &mut TermElabM, s: &SynElem, kinds: &KindInterner) -> Result<Tree, ElabError> {
    // The five literal kinds `go` matches; `binrel%` falls through to a leaf.
    if let Some(view) = OpView::from_literal(s, kinds)? {
        if !view.kind.is_rel() {
            return process_view(elab, &view, kinds);
        }
    }
    // `(($h:hygieneInfo $e))`: recurse unless `e` has a `·` (`:201-205`).
    if kinds.name(s.kind()) == "Lean.Parser.Term.paren" {
        let inner = paren_inner(s)?;
        return if has_cdot(&inner, kinds) {
            process_leaf(elab, TermTarget::Stx(s.clone()), s, kinds)
        } else {
            go(elab, &inner, kinds)
        };
    }
    // `expandMacroImpl?` (`:208-212`): an op expansion continues the tree;
    // anything else it expands to (an `App`, or `binrel%`) is a LEAF of the
    // expanded syntax, which is what `go s'` on it does in the oracle.
    match crate::macros::expand(s, kinds)? {
        Some(exp) => {
            let nested = match OpView::from_expansion(s, &exp) {
                Some(view) if !view.kind.is_rel() => process_view(elab, &view, kinds)?,
                _ => process_leaf(elab, TermTarget::Expanded { r#ref: s.clone(), exp }, s, kinds)?,
            };
            Ok(Tree::MacroExpansion { stx: s.clone(), nested: Box::new(nested) })
        }
        None => process_leaf(elab, TermTarget::Stx(s.clone()), s, kinds),
    }
}

/// oracle: `processBinOp` / `processUnOp` (`:212-222`).
fn process_view(elab: &mut TermElabM, view: &OpView, kinds: &KindInterner) -> Result<Tree, ElabError> {
    let f = resolve_head(elab, &view.head)?;
    let r#ref = view.r#ref.clone();
    let kind = match view.kind {
        OpKind::UnOp => {
            let arg = go(elab, &view.args[0], kinds)?;
            return Ok(Tree::UnOp { r#ref, f, arg: Box::new(arg) });
        }
        OpKind::BinOp => BinOpKind::Regular,
        OpKind::BinOpLazy => BinOpKind::Lazy,
        OpKind::LeftAct => BinOpKind::LeftAct,
        OpKind::RightAct => BinOpKind::RightAct,
        OpKind::BinRel | OpKind::BinRelNoProp => {
            return Err(ElabError::Internal("process_view on a binrel".into()))
        }
    };
    // `leftact`/`rightact`: that side is a leaf (`:217-219`).
    let lhs = if kind == BinOpKind::LeftAct {
        process_leaf(elab, TermTarget::Stx(view.args[0].clone()), &view.args[0], kinds)?
    } else {
        go(elab, &view.args[0], kinds)?
    };
    let rhs = if kind == BinOpKind::RightAct {
        process_leaf(elab, TermTarget::Stx(view.args[1].clone()), &view.args[1], kinds)?
    } else {
        go(elab, &view.args[1], kinds)?
    };
    Ok(Tree::BinOp { r#ref, kind, f, lhs: Box::new(lhs), rhs: Box::new(rhs) })
}

/// oracle: `processLeaf` (`:226-229`): `elabTerm s none`.
fn process_leaf(
    elab: &mut TermElabM,
    target: TermTarget,
    r#ref: &SynElem,
    kinds: &KindInterner,
) -> Result<Tree, ElabError> {
    let val = elab.elab_target(&target, kinds, None)?;
    Ok(Tree::Term { r#ref: r#ref.clone(), val })
}

fn paren_inner(s: &SynElem) -> Result<SynElem, ElabError> {
    s.as_node()
        .and_then(|n| non_trivia_children(n).into_iter().nth(1))
        .ok_or_else(|| ElabError::IllFormedSyntax("paren: no inner term".into()))
}

/// oracle: `hasCDot` (`Lean/Elab/BuiltinNotation.lean:306-311`) with
/// `isCDotBinderKind` (`:285-286`) and `isCDotForInfo` (`:292-299`). The
/// search stops at a cdot binder (`paren`, `typeAscription`, `tuple`): that
/// node owns its own `·`. `isCDotForInfo` compares the cdot's hygiene info
/// with the paren's. Every `·` that leanr parses from source carries the
/// same (empty) macro scopes as its enclosing paren, so any `cdot` node
/// matches.
fn has_cdot(e: &SynElem, kinds: &KindInterner) -> bool {
    match kinds.name(e.kind()) {
        "Lean.Parser.Term.paren" | "Lean.Parser.Term.typeAscription" | "Lean.Parser.Term.tuple" => false,
        "Lean.Parser.Term.cdot" => true,
        _ => e
            .as_node()
            .is_some_and(|n| non_trivia_children(n).iter().any(|c| has_cdot(c, kinds))),
    }
}
```

- [ ] **Step 6: Implement `builtin/op/analyze.rs`.**

```rust
//! oracle: `hasCoe`, `AnalyzeResult`, `isUnknown`, `analyze`
//! (`Extra.lean:232-314`).

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;
use leanr_kernel::BinderInfo;
use leanr_meta::LOption;

use super::tree::{BinOpKind, Tree};
use crate::app::lval::node;
use crate::builtin::binder::fun::cleanup_annotations;
use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `hasCoe` (`:232-240`): `coerceSimple?` on a fresh local of type
/// `from`. `.undef` counts as `false` (the oracle's own TODO). Assignments
/// made by the attempt are NOT rolled back, as in the oracle.
#[doc(hidden)]
pub fn has_coe(elab: &mut TermElabM, from: ExprId, to: ExprId) -> Result<bool, ElabError> {
    let coe_t = crate::app::head::intern_dotted(elab, "CoeT")?;
    if elab.view.get(coe_t).is_none() {
        return Ok(false);
    }
    let cp = elab.mctx.lctx_checkpoint();
    let r = elab
        .mctx
        .push_local_decl(None, from, BinderInfo::Default)
        .and_then(|x| elab.mctx.coerce_simple(x, to));
    elab.mctx.lctx_restore(cp);
    Ok(matches!(r?, LOption::Some(_)))
}

/// oracle: `AnalyzeResult` (`:242-247`).
#[derive(Debug, Default)]
pub(crate) struct AnalyzeResult {
    pub max: Option<ExprId>,
    pub has_uncomparable: bool,
    pub has_unknown: bool,
}

/// oracle: `isUnknown` (`:249-254`).
#[doc(hidden)]
pub fn is_unknown(elab: &TermElabM, e: ExprId) -> bool {
    match node(elab, e) {
        Node::MVar { .. } => true,
        Node::App { f, .. } => is_unknown(elab, f),
        Node::LetE { body, .. } => is_unknown(elab, body),
        Node::MData { expr, .. } => is_unknown(elab, expr),
        _ => false,
    }
}

/// `(← instantiateMVars (← inferType e)).cleanupAnnotations`.
pub(crate) fn leaf_type(elab: &mut TermElabM, e: ExprId) -> Result<ExprId, ElabError> {
    let ty = elab.mctx.infer_type(e)?;
    let ty = elab.mctx.instantiate_mvars(ty)?;
    Ok(cleanup_annotations(elab, ty))
}

/// oracle: `analyze` (`:256-314`).
pub(crate) fn analyze(
    elab: &mut TermElabM,
    t: &Tree,
    expected: Option<ExprId>,
) -> Result<AnalyzeResult, ElabError> {
    let max = match expected {
        None => None,
        Some(ty) => {
            let ty = elab.mctx.instantiate_mvars(ty)?;
            let ty = cleanup_annotations(elab, ty);
            (!is_unknown(elab, ty)).then_some(ty)
        }
    };
    let mut r = AnalyzeResult { max, ..Default::default() };
    go(elab, t, &mut r)?;
    Ok(r)
}

fn go(elab: &mut TermElabM, t: &Tree, r: &mut AnalyzeResult) -> Result<(), ElabError> {
    if r.has_uncomparable {
        return Ok(());
    }
    match t {
        Tree::MacroExpansion { nested, .. } => go(elab, nested, r),
        Tree::BinOp { kind: BinOpKind::LeftAct, rhs, .. } => go(elab, rhs, r),
        Tree::BinOp { kind: BinOpKind::RightAct, lhs, .. } => go(elab, lhs, r),
        Tree::BinOp { lhs, rhs, .. } => {
            go(elab, lhs, r)?;
            go(elab, rhs, r)
        }
        Tree::UnOp { arg, .. } => go(elab, arg, r),
        Tree::Term { val, .. } => {
            let ty = leaf_type(elab, *val)?;
            if is_unknown(elab, ty) {
                r.has_unknown = true;
                return Ok(());
            }
            let Some(max) = r.max else {
                r.max = Some(ty);
                return Ok(());
            };
            // `:309`: `withNewMCtxDepth <| withConfig (isDefEqStuckEx :=
            // true) <| isDefEqGuarded max type` — the P1 dependency.
            let same = elab.mctx.with_new_mctx_depth(false, |m| {
                m.with_def_eq_stuck_ex(|m| m.is_def_eq_guarded(max, ty))
            })?;
            if !same {
                if has_coe(elab, ty, max)? {
                } else if has_coe(elab, max, ty)? {
                    r.max = Some(ty);
                } else {
                    r.has_uncomparable = true;
                }
            }
            Ok(())
        }
    }
}
```

  (`push_local_decl(...).and_then(|x| elab.mctx.coerce_simple(x, to))`
  borrows `elab.mctx` twice. Write it as two statements in a closure that
  takes `&mut MetaCtx`, or as a `match`. The point is that `lctx_restore`
  runs on both paths. If `cleanup_annotations` takes `&TermElabM` while you
  hold `&mut`, bind first.)

- [ ] **Step 7: Implement `builtin/op/to_expr.rs`.**

```rust
//! oracle: `mkBinOp`, `mkUnOp`, `toExprCore`, `hasHeterogeneousDefaultInstances`,
//! `hasHomogeneousInstance`, `applyCoe`, `toExpr` (`Extra.lean:316-473`),
//! plus `mkFunUnit` (`Meta/Basic.lean:1157-1158`) and a restricted
//! `mkAppM` (`Meta/AppBuilder.lean:364-367`).

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::BinderInfo;
use leanr_meta::{LOption, MetaError};
use leanr_syntax::kind::KindInterner;

use super::analyze::{analyze, is_unknown, leaf_type};
use super::tree::{BinOpKind, Tree};
use crate::app::expand::Arg;
use crate::app::lval::{app_fn, node};
use crate::app::{elab_app_args, AppCall};
use crate::dispatch::SynElem;
use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `mkFunUnit`: `fun (_ : Unit) => a`. The binder name is a fresh
/// user name in the oracle; leanr's canonical encoder erases binder names.
#[doc(hidden)]
pub fn mk_fun_unit(elab: &mut TermElabM, a: ExprId) -> Result<ExprId, ElabError> {
    let base = elab.view.store;
    let unit = crate::app::head::intern_dotted(elab, "Unit")?;
    let no_levels = elab.mctx.store_mut().intern_level_list(None, &[]).map_err(MetaError::from)?;
    let unit = elab.mctx.store_mut().expr_const(Some(base), Some(unit), no_levels).map_err(MetaError::from)?;
    Ok(elab
        .mctx
        .store_mut()
        .expr_lam(Some(base), None, unit, a, BinderInfo::Default)
        .map_err(MetaError::from)?)
}

fn apply_op(
    elab: &mut TermElabM,
    f: ExprId,
    args: Vec<ExprId>,
    r#ref: &SynElem,
    expected: Option<ExprId>,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    elab_app_args(
        elab,
        f,
        AppCall {
            named_args: Vec::new(),
            args: args.into_iter().map(Arg::Expr).collect(),
            expected,
            explicit: false,
            ellipsis: false,
            stx: r#ref.clone(),
            result_is_out_param_support: false,
        },
        kinds,
    )
}

/// oracle: `mkBinOp` (`:316-321`).
fn mk_bin_op(
    elab: &mut TermElabM,
    lazy: bool,
    f: ExprId,
    lhs: ExprId,
    rhs: ExprId,
    r#ref: &SynElem,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let rhs = if lazy { mk_fun_unit(elab, rhs)? } else { rhs };
    apply_op(elab, f, vec![lhs, rhs], r#ref, None, kinds)
}

/// oracle: `toExprCore` (`:326-345`).
pub(crate) fn to_expr_core(elab: &mut TermElabM, t: &Tree, kinds: &KindInterner) -> Result<ExprId, ElabError> {
    match t {
        Tree::Term { val, .. } => Ok(*val),
        Tree::BinOp { r#ref, kind, f, lhs, rhs } => {
            let l = to_expr_core(elab, lhs, kinds)?;
            let r = to_expr_core(elab, rhs, kinds)?;
            mk_bin_op(elab, *kind == BinOpKind::Lazy, *f, l, r, r#ref, kinds)
        }
        Tree::UnOp { r#ref, f, arg } => {
            let a = to_expr_core(elab, arg, kinds)?;
            apply_op(elab, *f, vec![a], r#ref, None, kinds)
        }
        Tree::MacroExpansion { nested, .. } => to_expr_core(elab, nested, kinds),
    }
}

fn const_name(elab: &TermElabM, e: ExprId) -> Option<NameId> {
    match node(elab, e) {
        Node::Const { name, .. } => name,
        _ => None,
    }
}

/// `Name.getPrefix` of a `Str`/`Num` name; `None` for a root name.
fn name_prefix(elab: &TermElabM, n: NameId) -> Option<NameId> {
    use leanr_kernel::bank::names::NameRow;
    match *elab.mctx.store().name_row(Some(elab.view.store), n) {
        NameRow::Str { parent, .. } | NameRow::Num { parent, .. } => parent,
    }
}

/// oracle: `hasHeterogeneousDefaultInstances` (`:367-378`).
#[doc(hidden)]
pub fn has_heterogeneous_default_instances(
    elab: &mut TermElabM,
    f: ExprId,
    max: ExprId,
    lhs: bool,
) -> Result<bool, ElabError> {
    let Some(f_name) = const_name(elab, f) else { return Ok(false) };
    let max_fn = app_fn(elab, max);
    let Some(type_name) = const_name(elab, max_fn) else { return Ok(false) };
    let Some(class) = name_prefix(elab, f_name) else { return Ok(false) };
    let insts = elab.mctx.default_instances_of(class);
    if insts.len() <= 1 {
        return Ok(false);
    }
    for (inst, _) in insts {
        let Some(info) = elab.view.get(inst) else { continue };
        let mut ty = info.constant_val().ty; // check the field name in leanr_kernel
        // `getForallBody`: strip binders WITHOUT instantiating (loose bvars
        // are fine for the `isAppOf` tests below).
        while let Node::Forall { body, .. } = node(elab, ty) {
            ty = body;
        }
        // `.app (.app (.app _heteroClass lhsType) rhsType) _resultType`
        let Node::App { f: f1, .. } = node(elab, ty) else { continue };
        let Node::App { f: f2, arg: rhs_ty } = node(elab, f1) else { continue };
        let Node::App { arg: lhs_ty, .. } = node(elab, f2) else { continue };
        let is_app_of = |e: ExprId| const_name(elab, app_fn(elab, e)) == Some(type_name);
        if lhs && is_app_of(rhs_ty) {
            return Ok(true);
        }
        if !lhs && is_app_of(lhs_ty) {
            return Ok(true);
        }
    }
    Ok(false)
}

/// oracle: `mkAppM` (`AppBuilder.lean:364-367`), restricted to a telescope
/// of EXPLICIT binders — every `binop%` class (`HAdd α β γ` …) has one. An
/// implicit or instance binder (the oracle would mint an mvar or synthesize)
/// is a named seam (`Unsupported`), never a silent `None`. `Ok(None)` is
/// the oracle's `throwAppBuilderException`: an argument whose type does not
/// match, or a level mvar left unassigned (`mkAppMFinal`'s
/// `hasAssignableMVar`). Runs under `withNewMCtxDepth`, as the oracle does,
/// and instantiates INSIDE the scope, because the scope's exit discards
/// inner assignments.
#[doc(hidden)]
pub fn mk_app_m(elab: &mut TermElabM, cname: NameId, args: &[ExprId]) -> Result<Option<ExprId>, ElabError> {
    let raw = elab.mk_const_with_level_params(cname)?;
    let r = elab.mctx.with_new_mctx_depth(false, |m| -> Result<Option<ExprId>, MetaError> {
        let f = m.mk_const_with_fresh_mvar_levels(raw)?;
        let mut acc = f;
        let mut f_ty = m.infer_type(f)?;
        for &a in args {
            let f_whnf = m.whnf(f_ty)?;
            let Node::Forall { binder_type, body, binder_info, .. } = m.node(f_whnf) else {
                return Ok(None); // too many arguments: `throwAppBuilderException`
            };
            if binder_info != BinderInfo::Default {
                return Err(MetaError::Unsupported(
                    "mk_app_m: non-explicit binder (owner: the slice that needs a full mkAppM)".into(),
                ));
            }
            let a_ty = m.infer_type(a)?;
            if !m.is_def_eq(binder_type, a_ty)? {
                return Ok(None);
            }
            acc = m.mk_app(acc, a)?; // use the MetaCtx app builder `expr_app` wraps
            f_ty = m.instantiate1(body, a)?;
        }
        let r = m.instantiate_mvars(acc)?;
        // `hasAssignableMVar`: the only mvars minted in this scope are
        // `f`'s fresh level mvars, so a level mvar the inputs do not
        // already carry is an unassigned inner one.
        let inputs_have_lmvar = args.iter().any(|&a| m.has_level_mvar(a));
        if m.has_level_mvar(r) && !inputs_have_lmvar {
            return Ok(None);
        }
        Ok(Some(r))
    })?;
    Ok(r)
}

/// oracle: `hasHomogeneousInstance` (`:387-394`):
/// `try … trySynthInstance (Cls max max max) matches .some _ catch _ => false`.
#[doc(hidden)]
pub fn has_homogeneous_instance(elab: &mut TermElabM, f: ExprId, max: ExprId) -> Result<bool, ElabError> {
    let Some(f_name) = const_name(elab, f) else { return Ok(false) };
    let Some(class) = name_prefix(elab, f_name) else { return Ok(false) };
    let attempt = (|| -> Result<bool, ElabError> {
        let Some(inst) = mk_app_m(elab, class, &[max, max, max])? else { return Ok(false) };
        Ok(matches!(elab.mctx.try_synth_instance(inst)?, LOption::Some(_)))
    })();
    match attempt {
        Err(ElabError::Meta(e)) if e.is_oracle_catchable() => Ok(false),
        other => other,
    }
}

/// oracle: `applyCoe` (`:396-447`). `rel.rs` calls it with `is_pred = true`.
pub(crate) fn apply_coe(
    elab: &mut TermElabM,
    t: &Tree,
    max: ExprId,
    is_pred: bool,
    kinds: &KindInterner,
) -> Result<Tree, ElabError> {
    apply_coe_go(elab, t, None, false, is_pred, max, kinds)
}

fn apply_coe_go(
    elab: &mut TermElabM,
    t: &Tree,
    f: Option<ExprId>,
    lhs: bool,
    is_pred: bool,
    max: ExprId,
    kinds: &KindInterner,
) -> Result<Tree, ElabError> {
    match t {
        Tree::BinOp { r#ref, kind: BinOpKind::LeftAct, f: op, lhs: l, rhs: r } => Ok(Tree::BinOp {
            r#ref: r#ref.clone(),
            kind: BinOpKind::LeftAct,
            f: *op,
            lhs: l.clone(),
            rhs: Box::new(apply_coe_go(elab, r, None, false, false, max, kinds)?),
        }),
        Tree::BinOp { r#ref, kind: BinOpKind::RightAct, f: op, lhs: l, rhs: r } => Ok(Tree::BinOp {
            r#ref: r#ref.clone(),
            kind: BinOpKind::RightAct,
            f: *op,
            lhs: Box::new(apply_coe_go(elab, l, None, false, false, max, kinds)?),
            rhs: r.clone(),
        }),
        Tree::BinOp { r#ref, kind, f: op, lhs: l, rhs: r } => {
            // `:420`: `pure isPred <||> hasHomogeneousInstance f maxType`.
            if is_pred || has_homogeneous_instance(elab, *op, max)? {
                Ok(Tree::BinOp {
                    r#ref: r#ref.clone(),
                    kind: *kind,
                    f: *op,
                    lhs: Box::new(apply_coe_go(elab, l, Some(*op), true, false, max, kinds)?),
                    rhs: Box::new(apply_coe_go(elab, r, Some(*op), false, false, max, kinds)?),
                })
            } else {
                let le = to_expr(elab, l, None, kinds)?;
                let re = to_expr(elab, r, None, kinds)?;
                let val = mk_bin_op(elab, *kind == BinOpKind::Lazy, *op, le, re, r#ref, kinds)?;
                Ok(Tree::Term { r#ref: r#ref.clone(), val })
            }
        }
        Tree::UnOp { r#ref, f: op, arg } => Ok(Tree::UnOp {
            r#ref: r#ref.clone(),
            f: *op,
            arg: Box::new(apply_coe_go(elab, arg, None, false, false, max, kinds)?),
        }),
        Tree::Term { r#ref, val } => {
            let ty = leaf_type(elab, *val)?;
            if is_unknown(elab, ty) {
                if let Some(f) = f {
                    if has_heterogeneous_default_instances(elab, f, max, lhs)? {
                        return Ok(t.clone());
                    }
                }
            }
            if elab.mctx.is_def_eq_guarded(max, ty)? {
                Ok(t.clone())
            } else {
                let val = elab.mk_coe(r#ref, max, *val)?;
                Ok(Tree::Term { r#ref: r#ref.clone(), val })
            }
        }
        Tree::MacroExpansion { stx, nested } => Ok(Tree::MacroExpansion {
            stx: stx.clone(),
            nested: Box::new(apply_coe_go(elab, nested, f, lhs, is_pred, max, kinds)?),
        }),
    }
}

/// oracle: `toExpr` (`:449-473`).
pub(crate) fn to_expr(
    elab: &mut TermElabM,
    t: &Tree,
    expected: Option<ExprId>,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let r = analyze(elab, t, expected)?;
    let result = match r.max {
        Some(max) if !r.has_uncomparable => {
            let coerced = apply_coe(elab, t, max, false, kinds)?;
            let result = to_expr_core(elab, &coerced, kinds)?;
            if !r.has_unknown {
                // `:465-468`: record the max-type calculation.
                let ty = elab.mctx.infer_type(result)?;
                elab.mctx.is_def_eq_guarded(ty, max)?;
            }
            result
        }
        _ => to_expr_core(elab, t, kinds)?,
    };
    elab.ensure_has_type(t.ref_elem(), expected, result)
}

```

  Verify each API name against the code before compiling. Candidates to
  check: `info.constant_val().ty`, `m.node`, `m.mk_app` / `mk_app_spine`,
  `m.has_level_mvar` (otherwise use `expr_data(..).has_level_mvar()` via
  the store), and `name_row`'s module path. Each one names a real
  capability. The spelling is what may differ.

- [ ] **Step 8: Wire both entry points.** In `elab.rs`, the
  `Expanded { .. }` arm of `dispatch_target`:

```rust
                crate::macros::Expansion::Op { .. } => {
                    let view = crate::builtin::op::OpView::from_expansion(r#ref, exp)
                        .expect("an Op expansion has an op view");
                    crate::builtin::op::elab_op_view(self, &view, kinds, expected)
                }
```

  In `dispatch.rs`, add this before the catch-all:

```rust
        // oracle: `@[builtin_term_elab binop|binop_lazy|unop|leftact|rightact]
        // elabOp` and `binrel|binrel_no_prop` (`Extra.lean:478-482`,
        // `:564-566`) — macro/binop% P3, `builtin::op`.
        (k, NodeOrToken::Node(_)) if crate::macros::OpKind::ALL.iter().any(|o| o.syntax_kind() == k) => {
            let view = crate::builtin::op::OpView::from_literal(elem, kinds)?
                .expect("an op kind has an op view");
            crate::builtin::op::elab_op_view(elab, &view, kinds, expected)
        }
```

  In the deferral table, change the `binop% family` row to
  `binop% family (literal and expanded) ....... macro/binop% P3 SHIPPED — builtin/op/`.
  Until Task 4 lands, add the line
  `binrel% / binrel_no_prop% ................... P3 T4 — rel.rs seam`.

  `rel.rs` for this task:

```rust
//! oracle: `elabBinRelCore` (`Extra.lean:497-562`). Task 4.

use leanr_kernel::bank::ExprId;
use leanr_syntax::kind::KindInterner;

use super::OpView;
use crate::elab::TermElabM;
use crate::error::ElabError;

pub(crate) fn elab_bin_rel_core(
    _elab: &mut TermElabM,
    view: &OpView,
    _no_prop: bool,
    _kinds: &KindInterner,
    _expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    Err(ElabError::UnsupportedSyntax(view.kind.syntax_kind().to_string()))
}
```

- [ ] **Step 9: Run the tests and watch them pass.** Run
  `cargo test -p leanr_elab --test oracle_op --test op_helpers`.
  Everything should PASS, with the op corpus at 54. Then run the full
  `cargo test -p leanr_elab`, where Elab0 stays at 345.

  If a corpus record diverges, diagnose it with
  `superpowers:systematic-debugging`, comparing leanr's term to the
  oracle's. The likely causes are a leaf elaborated with an expected type,
  the wrong `has_coe` direction, or `elab_app_args` propagating something
  the oracle's `expectedType? := none` does not.

- [ ] **Step 10: Run the mutations.** Each must turn a named test red. The
  predictions are hypotheses.
  - (a) Drop `with_new_mctx_depth` in `analyze` (call
    `with_def_eq_stuck_ex` directly). Expect `op/depth` and `op/depth-mid`.
  - (b) Drop `with_def_eq_stuck_ex` in `analyze`. Expect `op/stuck`.
  - (c) Make `has_heterogeneous_default_instances` always return false.
    Expect `op/hetero-default` (`2` coerced or forced to `Arr Nat`).
  - (d) Drop the final `is_def_eq_guarded(ty, max)` record. Prediction:
    possibly SURVIVES. If it does, try `fun (n : Nat) (z : Z) => id (n + z)`
    and other rows where the result type is still an mvar. If nothing kills
    it, record the survival with the reason (the binop's result type is
    already `max` through the homogeneous instance's out-param).
  - (e) Swap the two `has_coe` directions. Expect `op/coe-left` and
    `op/coe-right`, plus `has_coe_follows_the_coercion_direction`.
  - (f) Make `has_homogeneous_instance` always true. Expect `op/rightact-pow`
    to stay green, since `rightact` skips it, and look for a row that goes
    red. If none does, add `fun (n : Nat) (z : Z) => z ^ n + n` (the `+`
    tree with a `^` subtree whose max is `Z`). Oracle-check it via the
    dumper, add it to `opQueries`, and raise the floor.
  - (g) Drop `mk_fun_unit` in `mk_bin_op`. Expect `op/lazy-orelse` and
    `op/lazy-andthen`.
  - (h) Pass `result_is_out_param_support: true` in `apply_op`. Expect a
    corpus row to go red. If none does, record the survival: no ElabOp class
    has an out-param result that `coeM` would rewrite.
  - (i) Treat the `leftact` lhs with `go` instead of `process_leaf`. Expect
    `op/smul`.
  - (j) In `resolve_id`, skip the local lookup. Expect
    `op/literal-local-head`.
  - (k) In `go`, recurse into a paren even when it has a cdot. Expect
    `cdot_paren_operand_is_the_cdot_seam` to stay green (both paths reach
    the seam), and record that the two paths are observably equal today.
  - (l) In `go`, recurse into a `binrel%` literal or expansion as a tree.
    This is unreachable until T4, so record it as covered by T4 (m).

- [ ] **Step 11: Commit.**

```bash
cargo fmt --all
git add crates/leanr_elab tests/fixtures/elab/dump_elab.lean tests/fixtures/elab/op-queries.jsonl
git commit -m "leanr_elab: the binop% elaborator (toTree/analyze/applyCoe/toExpr) (macro/binop% P3 T3)"
```

  Put the mutation results (a)–(l) in the commit body.

---

### Task 4: `binrel%` and `binrel_no_prop%`

**Files:**
- Modify: `crates/leanr_elab/src/builtin/op/rel.rs`
- Modify: `crates/leanr_elab/src/dispatch.rs` (remove the T4 deferral line)
- Modify: `tests/fixtures/elab/dump_elab.lean`, regenerate `op-queries.jsonl`
- Modify: `crates/leanr_elab/tests/oracle_op.rs`

**Interfaces:**
- Consumes (T3): `tree::{to_tree, Tree, BinOpKind}`, `analyze::analyze`,
  `to_expr::{to_expr_core, apply_coe}`, `resolve_head`, `OpView`.
- Produces: `rel::elab_bin_rel_core` (replacing the T3 stub).

- [ ] **Step 1: Add the corpus queries.** Append to `opQueries`:

```lean
  -- macro/binop% P3 T4: `binrel%`/`binrel_no_prop%` (Extra.lean:497-566)
  -- coercion at the relation, `isPred := true`
  , ("op/eq-coe",           "fun (n : Nat) (z : Z) => n = z")
  , ("op/lt-coe",           "fun (n : Nat) (z : Z) => n < z")
  -- the rest of the relation rows of the table
  , ("op/ge",               "fun (a b : Z) => a ≥ b")
  , ("op/ge-ascii",         "fun (a b : Z) => a >= b")
  , ("op/le",               "fun (a b : Z) => a ≤ b")
  , ("op/le-ascii",         "fun (a b : Z) => a <= b")
  , ("op/gt",               "fun (a b : Z) => a > b")
  , ("op/beq-coe",          "fun (n : Nat) (z : Z) => n == z")
  , ("op/bne-coe",          "fun (n : Nat) (z : Z) => n != z")
  , ("op/ne-coe",           "fun (n : Nat) (z : Z) => n ≠ z")
  -- binrel_no_prop%: a `Prop` max type becomes `Bool` (decide)
  , ("op/beq-prop",         "True == False")
  , ("op/bne-prop",         "True != False")
  , ("op/beq-prop-bool",    "fun (b : Bool) => True == b")
  -- uncomparable operands: plain elaboration + `ensureHasType`
  , ("op/rel-uncomparable", "fun (n : Nat) (u : U) => (n + u) = u")
  -- an op tree under a relation, and an unknown numeral side
  , ("op/rel-nested",       "fun (n : Nat) (z : Z) => n + n < z")
  , ("op/rel-numeral",      "fun (z : Z) => 2 < z")
  , ("op/rel-id-arg",       "fun (a b : Nat) => id (a < b)")
  -- Review Focus #5: relation operands are LEAVES of the outer tree
  , ("op/rel-of-rels",      "fun (a b : Nat) => (a < b) = (b < a)")
```

  Append `("op/unknown-binrel", "fun (a b : Nat) => binrel% NoSuch a b")`
  to `opErrQueries`. Regenerate as in Task 3 Step 1. `grep -c sorryAx`
  must print 0, and `wc -l` should print 73. (`op/rel-of-rels` was not
  probed. If it yields `sorryAx`, replace it with
  `fun (a b : Nat) => (a < b) = (a < b)` and re-check.)

- [ ] **Step 2: Raise the floor and delete the seam test.** Set the floor to
  73, with the comment "54 -> 73 (P3 T4): the binrel rows". Delete
  `rel_notations_stop_at_the_literal_kind_seam`. Extend
  `non_rel_op_notations_elaborate` into `op_notations_elaborate` by
  dropping the `binrel` filter. Rel rows use `(a b : Z)` binders, except
  `==`/`!=`, which also work on `Z` via `BEq Z`. Run
  `cargo test -p leanr_elab --test oracle_op` and expect FAIL: 19 records
  hit the stub.

- [ ] **Step 3: Implement `rel.rs`.**

```rust
//! oracle: `elabBinRelCore` (`Extra.lean:497-562`). `binrel% R a b`
//! elaborates `R a b` through the `binop%` tree machinery, but WITHOUT the
//! expected type in the analysis, and under `withSynthesizeLight` (no
//! default instances; the oracle's doc at `:504-530` gives the reason).

use leanr_kernel::bank::ExprId;
use leanr_syntax::kind::KindInterner;

use super::analyze::analyze;
use super::to_expr::{apply_coe, to_expr_core};
use super::tree::{to_tree, BinOpKind, Tree};
use super::{resolve_head, OpView};
use crate::app::expand::Arg;
use crate::app::{elab_app_args, AppCall};
use crate::elab::TermElabM;
use crate::error::ElabError;

pub(crate) fn elab_bin_rel_core(
    elab: &mut TermElabM,
    view: &OpView,
    no_prop: bool,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    // `resolveId? stx[1]` FIRST, outside `withSynthesizeLight` (`:498`, `:562`).
    let f = resolve_head(elab, &view.head)?;
    elab.with_synthesize_light(kinds, |elab| {
        let (lhs_stx, rhs_stx) = (&view.args[0], &view.args[1]);
        let lhs = to_tree(elab, lhs_stx, kinds)?;
        let rhs = to_tree(elab, rhs_stx, kinds)?;
        let tree = Tree::BinOp {
            r#ref: view.r#ref.clone(),
            kind: BinOpKind::Regular,
            f,
            lhs: Box::new(lhs.clone()),
            rhs: Box::new(rhs.clone()),
        };
        let r = analyze(elab, &tree, None)?;
        match r.max {
            Some(max) if !r.has_uncomparable => {
                let mut max = max;
                // `:552-554`: `noProp` turns a `Prop` max type into `Bool`.
                // NOT guarded: an error propagates, as in the oracle.
                if no_prop && is_prop(elab, max)? {
                    max = bool_type(elab)?;
                }
                let coerced = apply_coe(elab, &tree, max, true, kinds)?;
                to_expr_core(elab, &coerced, kinds)
            }
            _ => {
                // `:539-548`: default strategy + `toBoolIfNecessary`.
                let l = to_expr_core(elab, &lhs, kinds)?;
                let r = to_expr_core(elab, &rhs, kinds)?;
                let l = to_bool_if_necessary(elab, no_prop, lhs_stx, l)?;
                let r = to_bool_if_necessary(elab, no_prop, rhs_stx, r)?;
                let l_ty = elab.mctx.infer_type(l)?;
                let r = elab.ensure_has_type(rhs_stx, Some(l_ty), r)?;
                elab_app_args(
                    elab,
                    f,
                    AppCall {
                        named_args: Vec::new(),
                        args: vec![Arg::Expr(l), Arg::Expr(r)],
                        expected,
                        explicit: false,
                        ellipsis: false,
                        stx: view.r#ref.clone(),
                        result_is_out_param_support: false,
                    },
                    kinds,
                )
            }
        }
    })
}

/// `withNewMCtxDepth <| isDefEq e (mkSort Level.zero)`. Unguarded: the
/// oracle uses `isDefEq` here, not `isDefEqGuarded`.
fn is_prop(elab: &mut TermElabM, e: ExprId) -> Result<bool, ElabError> {
    let prop = crate::builtin::sort::mk_prop(elab)?; // the `Sort 0` builder `elab_prop` uses; extract it if it has no name
    Ok(elab.mctx.with_new_mctx_depth(false, |m| m.is_def_eq(e, prop))?)
}

fn bool_type(elab: &mut TermElabM) -> Result<ExprId, ElabError> {
    super::test_const(elab, "Bool") // `Bool` has no level params: plain `mkConst`
}

/// oracle: `toBoolIfNecessary` (`:556-561`).
fn to_bool_if_necessary(
    elab: &mut TermElabM,
    no_prop: bool,
    stx: &crate::dispatch::SynElem,
    e: ExprId,
) -> Result<ExprId, ElabError> {
    if no_prop {
        let ty = elab.mctx.infer_type(e)?;
        if is_prop(elab, ty)? {
            let b = bool_type(elab)?;
            return elab.ensure_has_type(stx, Some(b), e);
        }
    }
    Ok(e)
}
```

  (`builtin::sort::elab_prop` builds `Sort 0` inline, at
  `builtin/sort.rs:70-80`. Extract that body into
  `pub(crate) fn mk_prop(elab) -> Result<ExprId, ElabError>` and call it
  from both places. Rename `test_const` to `mk_const_named` once it has a
  non-test caller, and keep the `#[doc(hidden)] pub`. Check whether
  `with_synthesize_light`'s closure takes `&mut Self`: it is
  `impl FnOnce(&mut Self) -> Result<R, ElabError>`, which is what the code
  above assumes.)

  Remove the T4 deferral line in `dispatch.rs`.

- [ ] **Step 4: Run the tests and watch them pass.** Run
  `cargo test -p leanr_elab`. Everything should PASS, with op at 73 and
  Elab0 at 345.

- [ ] **Step 5: Run the mutations.**
  - (a) `is_pred = false` in the rel call to `apply_coe`. Expect
    `op/eq-coe` and `op/lt-coe`: `Eq`/`LT` has no `HAdd`-style homogeneous
    class, so without `is_pred` the leaves are not coerced.
  - (b) Drop `to_bool_if_necessary`, both calls. Expect `op/beq-prop-bool`
    or `op/beq-prop`. Find out which path each takes. If both take the max
    path, construct an uncomparable `binrel_no_prop` row (e.g.
    `fun (u : U) => u == u`?), oracle-check it, and add it.
  - (c) Drop the `no_prop` `Prop -> Bool` switch. Expect `op/beq-prop`.
  - (d) Pass `expected` into `analyze` instead of `None`. Look for a row
    that goes red. Expected: likely survives, since every corpus query
    elaborates with no expected type at the top. Then add
    `fun (n : Nat) (z : Z) => (n = z : Prop)`, oracle-check it, and record
    whether it kills.
  - (e) Run the rel without `with_synthesize_light`. Expect
    `op/rel-numeral` to stay green (the numeral is pinned by `Z`). Look for
    a row where default instances change the outcome, such as
    `fun (b : Nat → Prop) => b (2 < 3)`. Oracle-check it. If nothing kills
    the mutation, record that.
  - (f) Resolve `f` inside `with_synthesize_light`. This is unobservable.
    Record it.
  - (m) From T3 (l): in `tree::go`, process a rel view as a tree. Expect
    `op/rel-of-rels`.

- [ ] **Step 6: Commit.**

```bash
cargo fmt --all
git add crates/leanr_elab tests/fixtures/elab/dump_elab.lean tests/fixtures/elab/op-queries.jsonl
git commit -m "leanr_elab: binrel%/binrel_no_prop% (elabBinRelCore) (macro/binop% P3 T4)"
```

---

### Task 5: Docs, spec § Landed, and the whole-branch gate

**Files:**
- Modify: `crates/leanr_elab/src/lib.rs` (crate doc: the slice list / seam index; find the P2 entry and add P3)
- Modify: `crates/leanr_elab/src/macros/mod.rs` (`Expansion::Op` doc: "Elaborated by P3; until then a named seam" -> `builtin::op`)
- Modify: `docs/superpowers/specs/2026-10-01-macro-expansion-binop-design.md` (§ Landed › P3)

- [ ] **Step 1: Update the docs.** Any comment that says the op family is a
  seam or "P3 owns" it must now point at `builtin::op`. Find them with
  `grep -rn "P3 owns\|P3 removes\|until P3\|Until P3" crates/leanr_elab`.

- [ ] **Step 2: Write § Landed › P3.** Use the same shape as P1 and P2:
  commits, mutations run (all of T2–T4 with outcomes), spec corrections
  (the `op/` directory split; the `UnknownConstant` variant; whole-expansion
  postponement unreachable; `mk_app_m`'s explicit-only restriction; the
  `sorryAx` gate; the spec's `(p == q)`, `p q : Prop` row is an oracle
  ERROR, because there is no `Decidable p`, so the rows use `True == False`
  with the suffix's `Decidable True/False`; the depth row uses the suffix's
  `V`, not `BitVec`, which has no `Add` in Prelude), and open follow-ups (info trees; `withRef` positions;
  `mk_app_m` implicit/instance binders; survived mutations with reasons).

- [ ] **Step 3: The whole-branch gate.** Run it **blocking**, in this turn.
  Do not background it.

```bash
mise run ci; echo "CI_EXIT=$?"
```

  It must print `CI_EXIT=0`. This covers fmt, clippy `-D warnings`, and
  every test, including `parse:mathlib:fast`.

- [ ] **Step 4: Commit.**

```bash
git add crates/leanr_elab/src docs/superpowers/specs
git commit -m "docs: macro/binop% P3 landed (spec § Landed, crate docs)"
```
