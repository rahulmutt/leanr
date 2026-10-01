# Macro expansion in dispatch + the `binop%` family — design spec

## Where this sits

M4b-4 is complete (#49–#58). Every earlier M4b spec routes "macro
expansion in the dispatch path" and `binop%` to "the first slice with a
macro-defined term form" (m4b1 § Out of scope; m4b4 § deferral table).
This is that slice. It is the largest remaining gap between leanr and
real Mathlib terms: `a + b`, `a = b`, `a ≤ b` and `¬ p` elaborate only
through macro expansion.

Pinned oracle: `leanprover/lean4:v4.33.0-rc1`. The pin is not bumped.
Every citation below was opened against that toolchain's
`src/lean/` while writing this spec.

### Current state (verified while brainstorming)

- There is no VM. `leanr_vm` exists only in the architecture spec
  (`2026-07-04-leanr-architecture-design.md:62-64`, `:116-124`).
- `leanr_elab` never expands macros. Unknown kinds fall to
  `ElabError::UnsupportedSyntax` (`crates/leanr_elab/src/dispatch.rs:323`).
  The oracle `builtin_macro`s `paren`, `typeAscription`, `fun`,
  `forall` and `explicit` are hand-ported as elaborators.
- Infix notation parses: `a + b` is the node `«term_+_»`, built from the
  imported `ParserDescr` (`crates/leanr_grammar/src/descr.rs:122-136`).
  Only the parser half is imported. The `macro_rules` that rewrite it
  are compiled Lean code, and no olean decoding reads `macroAttribute`
  (`crates/leanr_olean/src/interp_id.rs:1019-1037`).
- `binop%`, `binop_lazy%`, `binrel%`, `binrel_no_prop%`, `unop%`,
  `leftact%` and `rightact%` have parsed since M3a
  (`crates/leanr_syntax/src/builtin/term/term_app.rs:191-244`). The
  m4b4 spec's "`binop%` is not parsed" (`:16`, `:347`) is stale. No
  elaborator handles them.
- leanr_meta has **no mctx-depth model**. `assign.rs`'s module doc
  (§ "Depth / read-only seam") collapses every `isReadOnly` /
  `isMVarWithGreaterDepth` check to "all mvars assignable", and
  checkpoint/rollback stands in for `withNewMCtxDepth`
  (`synth.rs:1600`). There is no `isDefEqStuckEx`.
- The elab oracle corpus (`tests/fixtures/elab/Elab0.lean`, prelude
  mode) declares no notation, and `oracle_elab.rs` parses with
  `builtin::snapshot()`. `a + b` cannot parse there today.

## Decisions (made with the user, 2026-10-01)

1. **Expansion source: a hand-ported table.** Without a VM, the
   compiled `macro_rules` cannot run. A Rust table keyed by syntax kind
   reproduces Init's expansions. Mathlib's own notations stay
   unsupported until the VM (or a later table) arrives. The VM later
   replaces the table behind the same hook.
2. **Scope: the hook plus the whole op family.** That means `binop%`,
   `binop_lazy%`, `binrel%`, `binrel_no_prop%`, `unop%`, `leftact%`
   and `rightact%`. `show`, `suffices`, `by` and cdot functions are out
   of scope.
3. **Harness: Init declarations copied verbatim into Elab0.** The
   corpus stays hermetic. A kind-guard test ties the table to the real
   Init olean.
4. **Approach A: three plans, with real mctx depth.** The op
   elaborator's `analyze` runs its type comparison under
   `withNewMCtxDepth` + `isDefEqStuckEx`. A rollback stand-in would
   assign an outer `?m` in `BitVec n =?= BitVec ?m` and change the
   coercion decision without any visible failure. Depth is therefore a
   prerequisite, built first and isolated.

Plans, one PR each, in this order: **P1** depth (leanr_meta) → **P2**
hook + table + harness (leanr_elab) → **P3** op elaborator
(leanr_elab). P2 does not depend on P1. P3 needs both.

## P1 — mctx depth + `isDefEqStuckEx` (leanr_meta)

### The oracle model

- `MetavarContext` has `depth : Nat := 0` and
  `levelAssignDepth : Nat := 0` (`Lean/MetavarContext.lean:352-355`).
  Expression and level mvar decls record the `depth` they were created
  at (`:251-256`, `:313-319`, set at `:813`, `:834`).
- `incDepth (allowLevelAssignments := false)` (`:932-936`) bumps
  `depth`. It sets `levelAssignDepth := depth` unless
  `allowLevelAssignments` is true.
- `withNewMCtxDepthImp` (`Lean/Meta/Basic.lean:1974`) runs `incDepth`,
  clears `postponed`, runs the body and restores. `withNewMCtxDepth`
  (`:1999-2000`) wraps it.
- The predicates:
  - `MVarId.isAssignable`: `decl.depth == mctx.depth`
    (`MetavarContext.lean:484-487`)
  - `MVarId.isReadOnly`: `decl.depth != mctx.depth`
    (`Basic.lean:971-972`)
  - `isReadOnlyOrSyntheticOpaque` (`Basic.lean:979-985`)
  - `isLevelMVarAssignable`: `decl.depth >= mctx.levelAssignDepth`
    (`MetavarContext.lean:471-474`)
  - `isMVarWithGreaterDepth` (`Lean/Meta/LevelDefEq.lean:93`)
- `isDefEqStuckEx : Bool := false` (`Basic.lean:134`), thrown via
  `Meta.throwIsDefEqStuck` (`Basic.lean:622-623`) at three sites:
  - `ExprDefEq.lean:1954-1956`: an undecided `isDefEqQuick` result
  - `ExprDefEq.lean:1993-2018`: a stuck mvar created at a lower depth
  - `LevelDefEq.lean:169-171`: a stuck level mvar
- `isExprDefEqGuarded` / `isDefEqGuarded` (`Basic.lean:2513-2518`):
  `try isExprDefEq a b catch _ => return false`.

### Design

- `MetaCtx` gains `depth` and `level_assign_depth`. Expression and
  level `MVarDecl`s gain `depth`, recorded at creation.
- `MetaCtx::with_new_mctx_depth(allow_level_assignments, f)` transcribes
  `withNewMCtxDepthImp`, restoring both fields on every exit path,
  error paths included.
- `is_read_only`, `is_read_only_or_synthetic_opaque` and
  `is_level_mvar_assignable` are ported. Every site that `assign.rs`'s
  and `level.rs`'s module docs name as the tier-1 depth seam now calls
  them. The "Depth / read-only seam" paragraphs are replaced by oracle
  citations.
- `Config::is_def_eq_stuck_ex` (default `false`) and an internal
  `MetaError::IsDefEqStuck` are thrown at the three oracle sites.
  `MetaCtx::is_def_eq_guarded` maps any error to `false`.

**Invariant: no behaviour change at depth 0.** With `depth == 0`
everywhere and the stuck flag off, every predicate gives its old
answer. Nothing outside the new scope enters depth > 0 in P1. The
`leanr_meta`, synth and elab oracle corpora must stay byte-identical,
and that is P1's gate.

### Not in P1 (each changes existing behaviour, so each is its own slice)

- moving `synth.rs` from its rollback stand-in onto real depth
  (`SynthInstance.lean:978`), together with synthesis's
  `isDefEqStuckEx := true` (`SynthInstance.lean:963`)
- `discr_path.rs`'s read-only key arm (m4b3 spec § P3 row)
- nondep R9: `elim_mvar`'s `newMVarKind`
  (`2026-09-29-nondep-local-decls-design.md:457`)

### Testing

Unit tests inside a `with_new_mctx_depth` scope:

- an outer `?m` is not assigned by `is_def_eq`, but an inner `?n` is
- a level mvar is assignable when `allow_level_assignments` is true,
  and not when it is false
- each of the three stuck sites throws when the flag is on, and
  `is_def_eq_guarded` returns `false`
- `BitVec n =?= BitVec ?m` with an outer `?m` returns `false` inside
  the scope and `true` outside it (the fixture may use any
  `Nat`-indexed inductive)
- every depth field is restored after an `Err` from the body

Mutations to run (from the brief; never trust the brief's own claims):

- delete the depth comparison at each wired seam site
- delete each of the three stuck throws
- skip the restore on the error path

A surviving mutation gets a killing test.

## P2 — expansion hook, Init table, harness (leanr_elab)

### Where the hook sits

The oracle's `elabTermAux` (`Lean/Elab/Term/TermElabM.lean:1823-1837`)
calls `expandMacroImpl?` **first**, before the implicit-lambda check
(`:1839`) and before any elaborator. On success it recurses on the new
syntax. Each recursion step runs under `withIncRecDepth` (`:1825`).

leanr's `Elab::elab_target` (`crates/leanr_elab/src/elab.rs:457`)
gets the same step, at the same point, before `use_implicit_lambda`
(`:528`):

```
expand_macro(&TermTarget, kinds) -> Result<Option<Expansion>, ElabError>
```

On `Some`, it recurses on `TermTarget::Expanded { ref, exp }` and
counts one recursion-guard step. Kinds that leanr already runs as
elaborators (`paren`, `typeAscription`, `fun`, `forall`, `explicit`)
are **not** table entries, so shipped behaviour does not change order.

### Synthesized syntax

leanr cannot build real nodes inside an existing rowan tree. Following
the `AnonCtorTail` precedent (m4b4b spec § The tail form; `elab.rs:18-32`
names `TermTarget` as the place this grows):

```rust
pub(crate) enum TermTarget {
    Stx(SynElem),
    AnonCtorTail { node: SyntaxNode, from: usize },
    Expanded { r#ref: SynElem, exp: Expansion },
}
pub(crate) enum Expansion {
    Op { kind: OpKind, f: Name, args: Vec<SynElem> },
    App { f: Name, args: Vec<SynElem> },
}
pub(crate) enum OpKind { BinOp, BinOpLazy, BinRel, BinRelNoProp, UnOp, LeftAct, RightAct }
```

- **Hygiene.** `f` is a pre-resolved global `Name`, modelling the
  quotation's hygienic identifier, so a local can never capture it
  (`fun (HAdd.hAdd : Nat) => a + b` still means the global).
- **Refs.** `args` are the original operand subtrees, so error
  positions land on real source. `ref` is the original notation node,
  matching the expanded syntax's `SourceInfo.fromRef`.
- **Literal `binop%` in source.** It reaches the same P3 elaborator. A
  shared `OpView` reads either an `Expanded` target or a literal node.
  Only the literal form resolves `f` (P3's `resolveId?`).
- **Postponement.** A postponed mvar stores the **original** ref, and
  `TermTarget::from_parts` re-runs `expand_macro` on resume. Table
  expansion is pure and deterministic, so this is observably equal to
  the oracle storing the expanded syntax, and no `Expansion` is ever
  serialized.

### The table (`crates/leanr_elab/src/macros/init.rs`)

The table maps a kind to its expansion. Each row cites its
`macro_rules` line:

| Kinds (notation) | Expansion | Oracle |
|---|---|---|
| `\|\|\|` `^^^` `&&&` `+` `-` `*` `/` `%` | `binop%` `HOr.hOr` `HXor.hXor` `HAnd.hAnd` `HAdd.hAdd` `HSub.hSub` `HMul.hMul` `HDiv.hDiv` `HMod.hMod` | `Init/Notation.lean:302-309` |
| `^` | `rightact% HPow.hPow` | `:311` |
| `++` | `binop% HAppend.hAppend` | `:312` |
| prefix `-` | `unop% Neg.neg` | `:313` |
| `•` | `leftact% HSMul.hSMul` | `:347` |
| `>=` `<=` `≤` `<` `>` `≥` `=` | `binrel%` `GE.ge` `LE.le` `LE.le` `LT.lt` `GT.gt` `GE.ge` `Eq` | `:372-373`, `:389-393` |
| `==` | `binrel_no_prop% BEq.beq` | `:394` |
| `<\|>` `>>` | `binop_lazy%` `HOrElse.hOrElse` `HAndThen.hAndThen` | `:436-437` |
| `!=` | `binrel_no_prop% bne` | `Init/Core.lean:777` |
| `≠` | `binrel% Ne` | `Init/Core.lean:880` |
| `∧` `∨` `¬` `↔` | `App` `And` `Or` `Not` `Iff` | their `infixr`/`notation` lines (the plan cites each) |

The table rows are the 24 op-family `macro_rules` plus the four logic
notations. Where a kind has more than one macro (the `infixl`-generated
one and a later `macro_rules`), the row encodes the one
`expandMacroImpl?` picks: the most recently declared. Exact kind names
come from the kind-guard test, not from this table.

### Harness

- `Elab0.lean` gains the `Init/Prelude` and `Init/Notation`/`Init/Core`
  declarations the corpus needs, copied verbatim in the scaffold's
  existing style:
  - the `H*`/homogeneous operator classes and the `instH*` default
    instances
  - `LE`, `LT`, `BEq`, `Ne`, `bne`, `Not`, `And`, `Or` and `Iff`,
    where they are not already present
  - the `infixl`/`notation` **and** `macro_rules` lines

  The oracle side therefore really expands to `binop%`.
- `oracle_elab.rs` parses with the snapshot plus Elab0's imported
  parser overlay, using the M3b2a machinery. Existing records must
  parse identically under the overlay, and that is checked.
- **Kind-guard test.** It decodes only `Init/Notation.olean` and
  `Init/Core.olean` from the pinned toolchain (their own
  `parserExtension` entries, not the import closure). It asserts that
  every table kind exists there under the same name. This guards
  against the table and Elab0's copy drifting from real Init.

### Testing

- One corpus record per `App` row (`∧ ∨ ¬ ↔`), plus a seam-assertion
  test per op kind. The op rows' corpus records land in P3.
- Rows that pin hook order: a notation in an implicit-lambda position.
- A local-shadowing row for hygiene.
- A literal `binop% HAdd.hAdd a b` row.
- A postponed operand that resumes through re-expansion.

Mutations to run:

- delete a table row (must diverge with `UnsupportedSyntax`)
- swap a row's `f`
- move the hook after `use_implicit_lambda`
- resolve `f` lexically instead of pre-resolving it
- store the expanded target instead of the original on postpone, if
  that is observable; otherwise record that it is not

Until P3 lands, an op-kind expansion reaches a named `UnsupportedSyntax`
seam (`binop%` and the rest), so the order, hygiene, literal and
postponement rows above are spelled with `App` notations where possible,
and the rest move to P3.

## P3 — the op elaborator (`crates/leanr_elab/src/builtin/op.rs`)

This transcribes `Lean/Elab/Extra.lean:154-566`.

### Tree

```rust
enum Tree {
    Term { r#ref: SynElem, val: ExprId },
    BinOp { r#ref: SynElem, kind: BinOpKind, f: ExprId, lhs: Box<Tree>, rhs: Box<Tree> },
    UnOp { r#ref: SynElem, f: ExprId, arg: Box<Tree> },
    MacroExpansion { stx: SynElem, nested: Box<Tree> },
}
enum BinOpKind { Regular, Lazy, LeftAct, RightAct }   // Extra.lean:154-158
```

The oracle's `infoTrees` payload and the macro name are dropped,
because leanr has no info trees. `MacroExpansion` stays, because
`analyze` and `apply_coe` traverse it and it carries the
macro-expansion stack used for error positions.

### `to_tree` (`:183-230`)

`go` handles each form as follows:

- An `Op` view: `process_bin_op` / `process_un_op`.
  - `f` is resolved, throwing `UnknownConstant` if it does not resolve
    (`:213`, `:220`).
  - `leftact` forces the left operand to a leaf, and `rightact` forces
    the right one (`:215-216`).
- A `paren` whose body has no `·`: recurse into the body. A `paren`
  whose body has a `·`: a leaf (`:201-205`). That reaches leanr's
  existing cdot seam, so there is no new behaviour.
- Anything else: try the P2 hook. An expansion yields
  `MacroExpansion { nested: go(expanded) }` (`:207-211`). This is what
  makes `a + b * c` one tree.
- Otherwise a leaf: `elab_term(s, None)` (`:224-227`).

`to_tree` ends with `synthesize_synthetic_mvars(postpone = yes)`
(`:191`).

### `analyze` (`:256-314`)

- `max?` starts from the expected type, after `instantiate_mvars` and
  `cleanup_annotations`, unless `is_unknown`.
- Each leaf type is compared under:

  ```
  with_new_mctx_depth(false, ||
      with_config(is_def_eq_stuck_ex = true, ||
          is_def_eq_guarded(max, ty)))
  ```

  This is the P1 dependency.
- On failure: `has_coe(ty, max)`, otherwise `has_coe(max, ty)` (which
  updates `max`), otherwise `has_uncomparable`.
- `has_coe` (`:232-240`) runs `coerce_simple` under a `with_local_decl`
  and treats `.undef` as false.
- `is_unknown` is ported verbatim (`:249-254`).

### `apply_coe` / `to_expr` / `to_expr_core` (`:316-473`)

These are verbatim ports.

- `has_homogeneous_instance` (`:387-394`) needs a minimal `mk_app_m`
  for `Cls max max max`, built with the existing application builder,
  with any error treated as false. It then calls `try_synth_instance`.
- `has_heterogeneous_default_instances` (`:367-378`) uses the existing
  `default_instances_of` and walks each instance type's `forall` body.
- Leaves are coerced with `crate::coe::mk_coe`.
- Nodes are built with
  `elab_app_args(f, [], [lhs, rhs], expected = None, explicit = false, ellipsis = false, result_is_out_param_support = false)`
  (`:316-323`).
- `binop_lazy%` wraps its right operand in a new `mk_fun_unit`.
- When there are no unknowns, `to_expr` records the max type with
  `is_def_eq_guarded(type(result), max)` (`:465-468`), then calls
  `ensure_has_type(expected)`.

### `elab_bin_rel_core(no_prop)` (`:497-562`)

- It runs under `with_synthesize_light`. Trees are built with
  `expected = None`, and `analyze(tree, None)` is called.
- If the types are uncomparable or there is no max type: elaborate both
  sides, apply `to_bool_if_necessary` (a depth-scoped `is_def_eq`
  against `Prop`), then `ensure_has_type(lhs_type, rhs)`, then
  `elab_app_args` with the expected type.
- Otherwise: `apply_coe(is_pred = true)`, with `no_prop` turning a
  `Prop` max type into `Bool`.
- An unresolved `f` throws `UnknownConstant`.

### Errors

No new `ElabError` variants are added. The existing `UnknownConstant`,
`TypeMismatch` and coercion errors are reused.

### Testing

One oracle record per row below. Rows are chosen so that each path is
distinguishable:

| Row | Path |
|---|---|
| `a + b * c : Nat` | homogeneous, one tree |
| `n + i`, `i + n` (`n : Nat`, `i : Int`) | leaf coercion to the max type, both orders |
| `(n + 0) + i` | unknown `0` resolves to `Int`, not `↑(0 : Nat)` (oracle comment `:281-284`) |
| heterogeneous default instance (`HMul α (Arr α) (Arr α)` style) | `has_heterogeneous_default_instances` |
| `x ^ n` (`x : Int`, `n : Nat`) | `rightact` leaves the exponent alone |
| uncomparable types | fallback to plain elaboration |
| `n = i`, `n < i` | binrel coercion, `is_pred` |
| `(p == q)`, `p q : Prop` | `binrel_no_prop` → `Bool` |
| `a <\|> b` | lazy `fun _ => b` |
| `BitVec n` vs `BitVec ?m`-shaped row | output depends on P1's depth |
| `binop% NoSuch a b` | err row |

Mutations to run:

- drop `with_new_mctx_depth` from `analyze` (must diverge on the depth
  row)
- drop `is_def_eq_stuck_ex` from `analyze`
- make `has_heterogeneous_default_instances` always false
- force `is_pred = false` in binrel
- drop the final max-type record
- drop `to_bool_if_necessary`
- swap the two `has_coe` directions

A surviving mutation gets a killing row.

## Out of scope (each names its owner)

- cdot functions `(· + 1)`: the cdot slice (`expandCDot?`)
- `show`, `suffices`, `by`: the follow-on slice that reuses this hook
  (`show` needs `by` for one arm)
- Mathlib-defined notations: the VM, or an explicitly extended table
- `defaultOrOfNonempty` and `forIn` (`Extra.lean:19-78`, `:568-593`):
  their owning slices (`do` for `forIn`)
- moving synthesis onto real depth, the `discr_path` read-only arm, and
  nondep R9: depth follow-up slices (see § P1)
- info trees: no leanr consumer exists yet
- `lean-toolchain` pin bump: milestone boundaries only

## Landed

(Filled in as each plan merges: corrections, mutations run, seams left.)

### P1 (PR #59): mctx depth + isDefEqStuckEx

Commits: 9169b3f (T1 depth bookkeeping + `with_new_mctx_depth`), e10c074
(T2 expr read-only arm at three sites), 0e7e64a (T3 level read-only +
`isMVarWithGreaterDepth`), 9363a7c (T4 `isDefEqStuckEx`, proof irrelevance,
`is_def_eq_guarded`), aa24e35 (T4 fix: `is_def_eq` rollback, guard rethrow).

Mutations run (all killed unless noted):
- T1: (a) drop rollback; (b) drop set_depths; (c) always set
  level_assign_depth; (d) stamp 0 in declare; (e) drop postponed.clear().
- T2: (a) delete assign.rs read-only arm; (b) delete lazy_delta.rs
  read-only half; (c) delete check.rs read-only half; (d) delete the two
  `defeq_cache_transient.clear()` in `with_new_mctx_depth` -- SURVIVES
  (the transient cache is already cleared per top-level `is_def_eq`,
  defeq.rs:97; kept as insurance for nested callers).
- T3: (a) solve read-only -> false; (b) remove greater-depth block;
  (c) `>` -> `>=`; (d) dec_level read-only -> false; (e)
  has_assignable back to `is_some`.
- T4: (a) drop expr stuck throw; (b) drop level throw; (c) drop rhs
  `is_mvar`; (d) drop proof-irrel call; (e) guard rethrow arm -> Ok(false);
  (f) no cfg restore; (g) cache_key ignoring the field.
- T4 fix: remove the rollback on the `process_postponed` Err path.

Spec corrections:
- Only **two** of the three stuck sites are ported. `unstuckMVar`
  (ExprDefEq.lean:1985-2020) sits inside the unported `isDefEqOnFailure`.
- The expression depth sites are `unassigned_mvar_id`,
  `is_def_eq_singleton` and `ensure_type`. `isAbstractedUnassignedMVar` /
  `isEtaUnassignedMVar` are not ported (`config.rs:128-129`); the slow
  `checkAssignment` mvar arm (ExprDefEq.lean:901) is not ported.
- The oracle's `withNewMCtxDepthImp` restores the whole mctx
  (Basic.lean:1974-1980), which the spec text did not state.
- Proof irrelevance is ported in the both-unassignable (`None, None`) arm
  of `assign.rs` (ExprDefEq.lean:1949-1956); oracle-faithful false -> true
  only.
- `is_def_eq_guarded` rethrows resource exhaustion (`DepthBudgetExhausted`,
  `StepBudgetExhausted`, `Kernel(BankExhausted)`, `Kernel(DeepRecursion)`)
  instead of mapping every error to `false` as the spec said: the oracle's
  `catch _` does not catch runtime exceptions.
- Final-review fixes: the `(None, None)` arm in `assign.rs` returns `false`
  before proof irrelevance when either head mvar is undeclared (else
  `infer_type` errs "unknown metavariable", order-dependent vs depth 0);
  `is_def_eq_guarded` also rethrows `Unsupported` (named seam) and `MVar`
  (caller bug), since leanr gaps/bugs are not oracle exceptions.
- `is_def_eq` now rolls back when `process_postponed` errs (defeq.rs); the
  new level stuck throw plus the swallowing guard made the previous
  skip-rollback path routinely reachable.
- Depth is stored as side maps in `mvar_ctx.rs`, not as an `MVarDecl`
  field (semantics identical; avoids touching every `MVarDecl` literal).

Open follow-ups:
- Synthesis onto real depth + `isDefEqStuckEx` (`synth_instance` still on
  rollback; `SynthInstance.lean:958-978`).
- `discr_path` read-only arm.
- Nondep R9 (`MetavarContext.lean:1187`, `:1195`).
- `unstuckMVar` (with `isDefEqOnFailure`).
- Declarations made inside a scope persist after rollback with their inner
  depth stamp (the oracle drops them); unreachable unless an inner mvar
  leaks.
- Minor: no test where neither level side is an mvar under the stuck flag;
  the `with_new_mctx_depth` Err-path test does not cover level assignment
  discard.
