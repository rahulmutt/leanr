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
3. **Harness: a separate `ElabOp` fixture generated from real Init.**
   *(Amended 2026-10-02, while writing the P2 plan; the user chose this
   option.)* The original decision was to copy Init declarations
   verbatim into Elab0, and it does not work. In prelude mode, `infixl`
   and `macro_rules` need the whole quotation/macro machinery
   (`ParserDescr`, `Syntax`, `MacroM`, and the `TSyntax`/
   `SyntaxNodeKinds` coercions in `Init/Notation.lean:105-108`). The
   corpus stays hermetic, and the ElabOp fixture and its golden file
   tie the table to real Init (§ Harness).
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

*(Added 2026-10-02, from probing.)* `Iff` has a second notation,
`<->` (`Init/Core.lean:196`), with its own kind `«term_<->_»`, so the
App rows number five and the table has 29 kinds. The oracle parses
`a >= b`/`a <= b` as `«term_≥_»`/`«term_≤_»`, because the ASCII forms are
`(priority := low)`. leanr's parser picks `«term_>=_»`/`«term_<=_»`.
Both rows of each pair expand to the same head, so elaboration cannot
observe the difference. The parser divergence is a `leanr_syntax`
follow-up.

### Harness

*(Rewritten 2026-10-02 per amended Decision 3. Every claim below was
probed against v4.33.0-rc1 while writing the P2 plan.)*

- **`tests/fixtures/elab/ElabOp.lean`** is a new prelude-mode, import-free
  fixture. Elab0 and its records are untouched. A committed script,
  `gen_elab_op.sh`, generates ElabOp from the pinned toolchain's own
  sources:
  - whole-file `Init/Prelude.lean`, `Init/Coe.lean` and
    `Init/Notation.lean`, with only the `module`/`prelude`/`import`
    lines removed and the `public`/`meta` modifiers dropped;
  - an `end Lean` line, because `Init/Notation.lean:592` opens
    `namespace Lean` and never closes it. Without it, the appended
    `Iff` becomes `Lean.Iff` and its notation kind becomes
    `Lean.«term_↔_»`;
  - the `Iff`, `bne` and `Ne` excerpts from `Init/Core.lean`
    (`:188-197`, `:772-777`, `:875-880`).

  The oracle side therefore expands with Init's real `macro_rules`. The
  olean is ~7.8 MB. leanr replays it in ~5.4 s (debug build), and
  `leanr_grammar::assemble` folds its grammar with 7 skips, none of them
  a term operator.
- **Its own corpus.** `dump_elab.lean ElabOp` writes `op-queries.jsonl`.
  A gate in `oracle_op.rs` parses with ElabOp's assembled grammar and
  shares the replay loop with `oracle_elab.rs`. Both gates assert that
  the parsed term covers the whole source: `parse_term` silently stops at
  an unknown token, so for example `a ⊕⊕ b` yields `<ident>` with no error.
- **Kind and expansion guard.** `dump_op_expansions.lean` runs every
  table notation through `expandMacroImpl?`. It records the source
  kind, the expansion kind, the pre-resolved head and the arity in
  `op-expansions.jsonl`. The regen task runs it against ElabOp and
  against the real `Init` and diffs the two. A Rust test then holds
  the table to the golden file in both directions. This replaces the
  toolchain-olean decode: CI has no Lean, and the regen-time diff
  catches the same drift.

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

**Superseded: P3 landed (see § Landed › P3).** Until P3 landed, an op-kind expansion reached a named `UnsupportedSyntax`
seam (`binop%` and the rest), so the order, hygiene, literal and
postponement rows above are spelled with `App` notations where possible,
and the rest move to P3.

## P3 — the op elaborator (`crates/leanr_elab/src/builtin/op/`)

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
    (`:216`, `:223`).
  - `leftact` forces the left operand to a leaf, and `rightact` forces
    the right one (`:217-219`).
- A `paren` whose body has no `·`: recurse into the body. A `paren`
  whose body has a `·`: a leaf (`:201-205`). That reaches leanr's
  existing cdot seam, so there is no new behaviour.
- Anything else: try the P2 hook. An expansion yields
  `MacroExpansion { nested: go(expanded) }` (`:208-212`). This is what
  makes `a + b * c` one tree.
- Otherwise a leaf: `elab_term(s, None)` (`:226-229`).

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

One new `ElabError` variant, `UnknownConstant(String)`, is added for
`throwUnknownConstantAt` (oracle first line ``Unknown constant `f` ``).
*(Corrected 2026-10-02: leanr's only `UnknownConstant` is a reason inside
`InvalidDottedIdent`, not a top-level variant.)* `TypeMismatch` and the
coercion errors are reused.

### Testing

One oracle record per row below. Rows are chosen so that each path is
distinguishable:

| Row | Path |
|---|---|
| `a + b * c : Nat` | homogeneous, one tree |
| `n + z`, `z + n` (`n : Nat`, `z : Z`) | leaf coercion to the max type, both orders |
| `(n + 0) + z` | unknown `0` resolves to `Z`, not `↑(0 : Nat)` (oracle comment `:285-287`) |
| `2 * a` (`a : Arr Nat`) | uncoerced `2`, reaching `has_homogeneous_instance = false` *(corrected: `op/hetero-default-homog`, over `MArr`, is the row that exercises `has_heterogeneous_default_instances`)* |
| `z ^ n` (`z : Z`, `n : Nat`) | `rightact` leaves the exponent alone |
| `n + u` (`u : U`, no coercion either way) | uncomparable: fallback to plain elaboration |
| `n = z`, `n < z` | binrel coercion, `is_pred` |
| `True == False` | `binrel_no_prop` → `Bool` *(corrected: `(p == q)` with `p q : Prop` is an oracle ERROR, there is no `Decidable p`)* |
| `a <\|> b` | lazy `fun _ => b` |
| `V 3` vs `V ?m`-shaped row (`op/depth`) | output depends on P1's depth *(corrected: suffix `V`, not `BitVec`, which has no `Add` in Prelude)* |
| `binop% NoSuch a b` | err row |

Every one of the 24 op table rows also gets at least one corpus record
(P2 § Landed › Open follow-ups); the rows above double as some of them.

*(Corrected 2026-10-02, while writing the P3 plan.)* No `binop%` row can
postpone a WHOLE expansion, in the oracle or in leanr. `useImplicitLambda`
postpones only a bare local identifier (`TermElabM.lean:1753-1778`),
`elabOp` never throws `postpone`, and its leaves catch their own
(`elabTerm` with `catchExPostpone := true`). P2's white-box test therefore
stays the only coverage of an `Expanded` target being postponed. Notation
in an mvar-expected argument position (`id (a + b)`) is covered instead.

#### Test-support suffix in ElabOp *(added 2026-10-02; the user chose this option)*

ElabOp is Prelude + Coe + Notation only. It has `Nat`, `Fin`, `UInt8`
and `BitVec`, but no `Int` and no cross-type coercion, so the rows above
need their own types. `gen_elab_op.sh` appends a short, hand-written,
clearly delimited section after the Core excerpts:

- `structure Z` with `OfNat Z n`, `Add`/`Mul`/`LT`/`BEq` instances,
  `HPow Z Nat Z`, and `instance : Coe Nat Z`. This is the "`Int`" of the
  rows above.
- `structure Arr (α : Type)` with
  `@[default_instance high] instance [Mul α] : HMul α (Arr α) (Arr α)`.
  Prelude's `instHMul` is already a default instance, so `HMul` has two,
  which is what `hasHeterogeneousDefaultInstances` requires (`:367-378`,
  `defInstances.length ≤ 1 → false`). This is the oracle docstring's own
  `Array` example.
- `structure U` with no coercion to or from `Nat`, for the uncomparable row.

The real Lean elaborates this suffix, so the oracle stays
authoritative. It is not copied from Init; the rejected alternatives were
verbatim `Int`/`NatCast` excerpts (a large closure that is fragile across
Init reshuffles) and Prelude-only types (too few coercions to
discriminate). Exact instance spellings are settled in the plan by
probing, and they must keep `oracle_op.rs`'s whole-source span check and
the `op-expansions.jsonl` golden unchanged. The suffix declares no
notation.

#### Helpers P3 adds (verified absent 2026-10-02)

`coerce_simple`, `mk_coe`, `elab_app_args`, `default_instances_of`,
`with_synthesize_light`, `ensure_has_type`, `cleanup_annotations`,
`try_synth_instance` and P1's depth API already exist. Three do not, and
P3 adds them minimally:

- a `with_local_decl` scope for `has_coe` (`:232-240`)
- `mk_fun_unit` for `binop_lazy%`
- a guarded `mk_app_m` for `has_homogeneous_instance`'s
  `Cls max max max` (`:387-394`), where any error means false

Mutations to run:

- drop `with_new_mctx_depth` from `analyze` (must diverge on the depth
  row)
- drop `is_def_eq_stuck_ex` from `analyze`
- make `has_heterogeneous_default_instances` always false
- force `is_pred = false` in binrel
- drop the final max-type record
- drop `to_bool_if_necessary`
- swap the two `has_coe` directions
- make `has_homogeneous_instance` always true

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

### P2 (PR #60): expansion hook, Init table, ElabOp harness

Commits: 496f202 (ElabOp + golden), 169c1c5 (table + expand), 68c62a6
(hook + App + gate), 1b308e3 (op seam + postponement contract tests,
docs, spec Landed; T4), c80dc69 (`with_record_elab` dedupe), and the
commit titled "leanr_elab: final-review fixes (macro/binop% P2)".

Mutations run (all reverted):
- T1: (a) the `parse_whole` span assertion, KILLED (a scratch test on
  `a ⊕⊕ b` fails with it, passes without). (b) delete `end Lean` from
  `gen_elab_op.sh`: the golden becomes `Lean.Iff`; the regen's own Init
  diff caught it (the plan predicted it would not); `oracle_op.rs` stays
  green. (c) empty `KNOWN_PARSE_DIVERGENCES`: KILLED by
  `golden_sources_parse_to_the_oracle_kind`.
- T2: (a) delete the `∧` row, (b) swap a head to `HSub`, (c) `^`
  `RightAct`->`BinOp`, (d) bogus `+++` row: all KILLED by
  `table_matches_oracle_expansions`. (e) swapped operands, (f) prefix
  reads `[operand,_]`: KILLED by `expand_reads_operands_in_order`.
- T3: (a) delete the hook, (b) no paren-strip recursion, (d) resolve `f`
  lexically first, (e) reversed args, (g) span assertion removed: all
  KILLED by `oracle_op_gate`. (c) hook only in the `No` arm SURVIVED the
  plan's 18 records; added `op/implicit-lambda-bare` (corpus is 19, floor
  19), then KILLED. (f) not expressible: an `Expansion` is not a `SynElem`.
- T4: (a) `"binop%"` in the Op arm: KILLED by
  `op_notations_stop_at_the_literal_kind_seam`. (b) `BinRel`'s
  `syntax_kind` mapped to `binop`: KILLED (`table_matches_oracle_expansions`,
  `expand_reads_operands_in_order`, the seam test). (c) `tail_from` returns
  `Some(0)` for `Expanded`: KILLED. (d) `ref_elem` returns the first arg:
  KILLED. "Store the expanded target instead of the original on
  postpone" cannot be written, since the postponed record has no field for
  an `Expansion`.

Spec corrections:
- Harness: separate generated `ElabOp` fixture (Decision 3 amended
  2026-10-02); expansion golden file + regen-time diff against real
  Init instead of decoding toolchain oleans in CI.
- The hook needs no recursion guard: an `Expansion` is never re-expanded.
  The VM slice owns `withIncRecDepth`.
- The hook also runs on the `implicitLambda := false` path, after paren
  stripping (`@(t)`).
- `f` is carried as the global's name and resolved at elaboration
  (`elab_app_expanded`), not at expansion, which keeps `expand` pure.
- 29 kinds, not 28: `<->` is its own `Iff` kind.
- Both corpus gates assert the parsed term spans the whole source.

Open follow-ups:
- leanr_syntax parses `a >= b` / `a <= b` as the low-priority
  `«term_>=_»`/`«term_<=_»`; the oracle gives `«term_≥_»`/`«term_≤_»`.
  This is unobservable after expansion (`KNOWN_PARSE_DIVERGENCES` in
  `oracle_op.rs`).
- Remaining Init notations (`×`, `×'`, `∘`, `∣`, `<<<`, `>>>`, `~~~`,
  `⁻¹`, `≍`, `&&`, `||`, `!`, `∈`, `::`, `<$>`, `>>=`) have no table row;
  shapes `Expansion` cannot express (`∉` nested notation, `<*>`/`<*`/`*>`
  synthesizing `fun`, `<|`, `|>`, `$`, `{x // p}`, `without_expected_type`,
  `max_prec`) need a new shape. All raise `UnsupportedSyntax(kind)`.
- ~~P3: the op elaborator, plus corpus records for the 24 op rows.~~ DONE:
  see § Landed › P3.
- ~~Whole-notation postponement of an `Expanded` target is unreachable in
  P2 (App heads are consts with known types; no record postpones the
  notation), so only the white-box bookkeeping test covers it. P3's
  `binop%` elaborator should add a corpus record that postpones a whole
  expansion.~~ SUPERSEDED: unreachable, so no such record; see § Landed › P3
  (spec corrections).

### P3: the op elaborator (`builtin/op/`)

Commits: 0e6e5e1 (T1 test-support suffix + `sorryAx` corpus gate), 0b2dafd
(T2 `UnknownConstant`, `AppCall` out-param flag, catchable `MetaError`,
`OpKind::ALL`), 09cf8fc (T3 `binop%` elaborator: toTree/analyze/applyCoe/
toExpr), b1741f2 (T4 `binrel%`/`binrel_no_prop%`), plus the T5 docs commit.
Corpus 19 -> 81 rows (`CORPUS_FLOOR` 81; Elab0 floor 345 unchanged).

Mutations run (all reverted):
- T1: record-edit mutation (the plan's `Err`-arm mutation was unreachable),
  KILLED. Re-run in T4 with the original `p == q` row: it first failed as an
  ordinary divergence because the assert sat in the `Ok` arm; after moving
  it ahead of leanr's result (R6) it panics "oracle record contains
  sorryAx". KILLED.
- T2: (b), (c) KILLED. (a) deferred to T3 (h).
- T3: (a) drop `with_new_mctx_depth`: KILLED (`op/depth`, `op/depth-mid`,
  `op/stuck`). (b) drop `with_def_eq_stuck_ex`: KILLED (`op/stuck`). (c)
  heterogeneous-default always false: KILLED by `op/hetero-default-homog`
  (new; `op/hetero-default` does not reach the leaves). (d) drop the final
  `is_def_eq_guarded(ty, max)` record: SURVIVES (with no unknown leaf every
  leaf type is already `max`, so the instance's out-param equals `max`).
  (e) swap `has_coe` directions: KILLED (7 rows). (f) `has_homogeneous_
  instance` always true: KILLED by `op/homog-literal-pow` (new). (g) drop
  `mk_fun_unit`: KILLED (`op/lazy-*`). (h) `result_is_out_param_support:
  true`: SURVIVES, unkillable by closed rows after R2 (below). (i) `leftact`
  lhs via `go`: KILLED by `op/smul-op-lhs` (new). (j) `resolve_id` skips
  locals: KILLED (`op/literal-local-head`). (k) recurse into a `·` paren:
  SURVIVES (both paths reach `UnsupportedSyntax(cdot)`). (l) `binrel%` as a
  tree: unreachable in T3, killed by T4 (m).
- T4: (a) `is_pred = false`: KILLED. (b) drop `to_bool_if_necessary`:
  survived the brief's rows (all take the max path); KILLED by
  `op/beq-uncomparable-prop` (new). (c) drop the noProp switch: KILLED. (d)
  `expected` into `analyze`: survived; KILLED by `op/rel-expected` (new).
  (e2) full `with_synthesize(Yes)`: KILLED by `op/rel-no-default` (new).
  (e1) no scope at all: SURVIVES (every goal the light scope could solve was
  already tried by `to_tree`'s own synthesis). (f) resolve `f` inside the
  scope: SURVIVES (`resolve_head` registers no synthetic mvars). (m)/(T3 l)
  `binrel%` operand as a tree: `op/rel-of-rels` does NOT kill; KILLED by
  `op/rel-of-coe-rels` (new). (m2) same for the literal arm: KILLED by
  `op/rel-of-literal-rels` (new).

Spec corrections:
- The elaborator is the directory `builtin/op/` (`mod`, `tree`, `analyze`,
  `to_expr`, `rel`), not `builtin/op.rs`.
- `ElabError::UnknownConstant(String)` is a new top-level variant (the
  nested `InvalidDottedIdentReason` one is unrelated).
- Whole-expansion postponement is unreachable (see the correction under
  Testing); P2's follow-up asking P3 for such a record is void.
- `mk_app_m` is restricted to explicit binders: a non-explicit binder is an
  `Unsupported` seam (see follow-ups).
- The `sorryAx` gate: the dumper turns logged elaboration errors into
  `sorryAx`, so `run_elab_corpus` asserts no oracle record mentions it. The
  assert now runs ahead of leanr's result (R6), so an erroring leanr cannot
  mask an oracle error.
- Testing-table corrections (also in place above): `(p == q)`, `p q : Prop`
  is an oracle ERROR, so the rows use `True == False` with the suffix's
  `Decidable True/False`; the depth row uses suffix `V`, not `BitVec`; the
  `2 * a` row's path is `has_homogeneous_instance = false`, and
  `op/hetero-default-homog` is what exercises
  `has_heterogeneous_default_instances`. The comment above `op/hetero-default`
  in `dump_elab.lean` was corrected to match (comment only; fixtures not
  regenerated).
- ~~R2: `op/depth`, `op/depth-mid`, `op/stuck` are respelled over closed suffix
  constants (`vx`, `k0`, `fx`, `z0`) instead of `fun` binders, because of the
  elimMVarDeps gap below. Same ids and discriminated paths.~~ Restored; closed spellings kept as `-closed` [checkAssignment slice: `2026-10-02-check-assignment-ctx-approx-design.md` § Landed].
- R5: the suffix declares `instance : BEq Bool`, so the oracle records for
  `op/beq-prop`, `op/bne-prop`, `op/beq-prop-bool` pin `instBEqBool`, not
  Prelude's `instBEqOfDecidableEq`. Fidelity caveat: those rows no longer
  exercise the Prelude route.
- Row `op/postponed-operand` became `op/postponed-binop-operand` (id clash
  with a P2 row).

Open follow-ups (owner suggestion in brackets):
- ~~**TOP PRIORITY, reachable from plain `+` notation (final-review probe,
  2026-10-02).** The elimMVarDeps gap below is NOT confined to explicit `@`:
  ordinary `binop%` notation hits it. Against ElabOp,
  `fun (n : Nat) (x : F n) => x + F.mk _` returns a SILENTLY WRONG `Ok` in
  leanr: `F.mk (?m n x)` with an unassigned mvar, and `instHAdd Nat
  instAddNat` as the instance, where the oracle gives `F.mk n` with
  `@instHAdd (F n) (instAddF n)`. And
  `fun (n : Nat) (x : F n) (z : Z) => x + F.mk _ + z` is
  `Err(InstanceSynthesisFailed)` in leanr where the oracle elaborates it
  (`@HAdd.hAdd (F n) Z Z (instHAddFZ n) (x + F.mk n) z`).~~ CLOSED [checkAssignment slice: `2026-10-02-check-assignment-ctx-approx-design.md` § Landed].
- ~~leanr_meta elimMVarDeps gap [a leanr_meta slice]: `assign.rs`
  `mk_lambda_fvars_with_let_deps` -> `mk_lambda_over_fvars` uses raw
  `abstract_fvars` with no `elimMVarDeps` (oracle `mkLambdaFVars`,
  `ExprDefEq.lean:549-554`). Op-free repros (explicit `@` also passes
  `resultIsOutParamSupport = false`; oracle accepts all):
  `fun (n : Nat) => @HAdd.hAdd _ _ _ _ (V.mk : V n) (V.mk : V _)`
  (StuckSyntheticMVar); `fun (n : Nat) (x : F n) (z : Z) => @HAdd.hAdd _ _ _ _
  (@HAdd.hAdd _ _ _ _ x (F.mk _)) z` (InstanceSynthesisFailed);
  `fun (n : Nat) (x : F n) => @HAdd.hAdd _ _ _ _ x (F.mk _)` returns a
  SILENTLY WRONG `Ok` keeping `F.mk (?m n x)` where the oracle has `F.mk n`.
  Reverted experiment: routing through `MetaCtx::mk_lambda` fixes the three
  binder forms but regresses `op/postponed-binop-operand` with
  `DepthBudgetExhausted`. Whoever fixes it restores the binder forms of
  `op/depth`, `op/depth-mid`, `op/stuck` and re-runs T3 mutations (d), (h).~~ CLOSED; binder forms restored, T3 (d)/(h) re-run [checkAssignment slice: `2026-10-02-check-assignment-ctx-approx-design.md` § Landed].
- synth pi-goal gap [synthesis slice]: `synth_instance` has no pi-shaped
  goal support (`SynthInstance.lean:740-742`), so `(inferInstance : BEq Bool)`
  and `BEq Nat` fail. Fixing it drops the suffix `BEq Bool` and re-checks the
  three rows against `instBEqOfDecidableEq`.
- ~~`(fun a => LT.lt a 2) z0` (also `a + 2`, `BEq.beq a 2`) gives
  `DepthBudgetExhausted` op-free; the oracle accepts [likely the same
  leanr_meta slice, not bisected]. `op/rel-no-default` uses `x.1 < 2` to
  avoid it.~~ CLOSED; corpus rows `meta/beta-{lt,add,beq}`, `op/rel-lt-beta` [checkAssignment slice: `2026-10-02-check-assignment-ctx-approx-design.md` § Landed].
- Info trees: no consumer yet [info-tree slice].
- `withRef` positions: error positions only; `rel.rs` omits the oracle's
  `withRef lhsStx/rhsStx` (`Extra.lean:531-532`) [error-position pass].
- `mk_app_m` implicit/instance binders [op follow-up]: the `Unsupported`
  seam propagates out of `has_homogeneous_instance` where the oracle's
  `catch _` yields false, e.g. a literal `binop% Subtype.mk a b`.
- `resolve_id` maps only `UnknownIdent` to `None` (the oracle catches all
  `resolveName` errors) and `raw.split('.')` mis-splits `«a.b»` heads.
- Minor: `OpKind::ALL`/`is_rel` lack a direct unit test;
  `mk_const_with_level_params` doc omits the missing-name caveat;
  `has_heterogeneous_default_instances` takes `&mut` but only reads;
  `paren_inner` is a third copy of paren-inner navigation; `rel.rs` deep-
  copies operand trees; the suffix comment at `elab_op_support.lean.in:69`
  is over-long.
- Survived mutations (T3 d, k; T4 e1, f) are unobservable today, see
  reasons above. T3 (h) is now KILLED by `meta/beta-add`; T3 (d) still
  survives the restored binder rows (checkAssignment slice § Landed).
