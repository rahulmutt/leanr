# M4c-2c-i — `universe`, `variable`, `include`, `omit` Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Port the scope universe names and section variables (`universe`, `variable`, `include`, `omit`) and the oracle's three section-variable inclusion regimes, gated by 76 oracle-probed file-corpus records.

**Architecture:** `Scope` stores level names and variable binder SYNTAX. Every declaration (and `variable`/`omit`) re-elaborates the variables in its own scratch `TermElabM` (the oracle's `runTermElabM`), then each declaration kind picks the kept variables (theorem: `withHeaderSecVars`; def/abbrev/opaque/example: `withUsed`; axiom: `usedOnly`) and abstracts over them. A theorem's body is elaborated in a local context with the non-kept variables erased.

**Tech Stack:** Rust (`leanr_elab`, one additive `leanr_meta` accessor), Lean 4 oracle `leanprover/lean4:v4.33.0-rc1` via `tests/fixtures/elab/dump_decls.lean files`.

**Spec:** `docs/superpowers/specs/2026-10-05-m4c2c-i-universe-variable-design.md` (read it first; this plan argues from it). § Plan amendments below records where this plan departs from it.

## Global Constraints

- Oracle discipline: correctness = the oracle's output. Every corpus record below was probed on 2026-10-05 (scratch: `target/m4c2cprobe/`, `final.lean` / `final.jsonl` / `expected.txt`). Never build or probe under `/tmp` (20Gi EmptyDir; pod eviction).
- Oracle cites: open the line before you copy a citation into code. Cites drift by 1-2 lines.
- `leanr_kernel` is untouched. `leanr_meta` gets ONE additive, TCB-neutral `pub` accessor (Task 4); no behaviour change there.
- No new dependencies.
- Every `UnsupportedSyntax` ends in a slice label (`— M4c-2c-ii`, `— later M4`); `label_seam` adds `— later M4` to unlabelled ones.
- Each task records its mutation in the commit BODY: the mutation, the command run, and which test FAILED. A mutation that makes nothing fail is reported, not hidden; strengthen the test.
- Before every push: `mise run ci` (fmt + clippy + tests). Block in-turn on it; never background it and end the turn.

## Review Focus

1. **A theorem whose proof mentions a non-included variable** must fail with the oracle's ``Unknown identifier `y` `` (the body runs in the RESTRICTED lctx), not succeed by abstracting it. Pinned by `varThm/bodyOnly` and `varThm/instUsedInProofOnly` (Task 4).
2. **`include`/`omit` must not affect definitions or axioms.** `include/def`, `omit/def`, `omit/axiom` and `varAxiom/include` pin this (Task 5).
3. **Instance-variable closure order:** an inst var is added only when ALL fvars of its type are already kept, scanned in variable order, and skipped when omitted. Pinned by `varThm/instNotCovered`, `varThm/instCoveredByBinder`, `include/instClosure`, `omit/inst*` (Tasks 4/5).
4. **Scope universe names in level-param order and the unused check:** a scope name is never "unused" but an explicit `.{w}` is. Pinned by `universe/order`, `universe/unusedScope`, `universe/unusedExplicit`, `universe/axiomUnusedScope` (Task 2).
5. **A section variable shadowed by a header binder** (`variable (n : Nat)` + `def f (n : Nat) := n`) must not be included. Pinned by `var/shadowBinder` (Task 3).

---

## Plan amendments (plan-time probes, 2026-10-05)

1. **`AlreadyDeclaredUniverseLevel` already exists** as `ElabError::UniverseAlreadyDeclared` (`error.rs:292`, rendering at `:555-557` matches the oracle). Reuse it; no new variant.
2. **`OmitUnmatched` renders the omit item's syntax**: the oracle prints `` `[Wrap Nat]` did not match any variables in the current scope `` (probe `omit/unmatchedInst`). leanr renders the item's source text with runs of whitespace collapsed to one space. An unusual spelling (comments inside the brackets) would differ; that is a known limitation recorded in the module doc.
3. **The omit "has not been declared in the current scope" branch is dropped**: every runner variable has a uid by construction (`elab_section_vars` asserts `fvars.len() == uids.len()`), so the branch is unreachable. No variant.
4. **Abstraction happens BEFORE `abstractNestedProofs`**: probe `var/auxProof` admits `vf8._proof_1 : ∀ (n : Nat), Nat.succ n = Nat.succ n` and value `fun n => PProd.mk n (vf8._proof_1 n)`.
5. **`u_N` ordering risk resolved** (spec § Inclusion): probes `varLevel/*` show the `Type _` level mvar of a variable becomes `u_1` at the first `levelMVarToParam` that sees the abstracted type (def: `levelMVarToParamTypesPreDecls`; theorem: the async signature). Abstract the kept vars before those calls and the existing code yields the oracle's names.
6. **No sync-theorem row**: a theorem header with a leftover expression mvar always errors at the header (`header.rs:280-283` logs it), so the sync `finishElab` theorem path is only reachable through errors. The theorem regime is pinned through the async path; the sync call uses the same helper with `check = false`.
7. **Unknown identifiers in variable binders** are the auto-bound seam, worded ``unbound `x` in a `variable` binder (auto-bound implicit) — M4c-2c-ii``. The header seam is relabelled `— M4c-2c-ii`.

## File structure

- `crates/leanr_elab/src/command/scope.rs` — `Scope` gains `level_names`, `var_decls`, `var_uids`, `included_vars`, `omitted_vars` (Task 2/3); `elab_universe` (Task 2).
- `crates/leanr_elab/src/command/vars.rs` (NEW) — the runner (`elab_section_vars`, `SecVars`), `variable`/`include`/`omit` command elaborators, binder-id extraction, inclusion helpers (`used_vars`, `header_sec_vars`, `remove_unused`), `collect_fvars`.
- `crates/leanr_elab/src/command/mod.rs` — dispatch arms; `CommandElab::next_var_uid`; `with_term_elab` (one scratch `TermElabM` per run); `command_seam` shrinks.
- `crates/leanr_elab/src/command/header.rs` — `expand_decl_id` seeds from the scope names; seam relabel.
- `crates/leanr_elab/src/command/def.rs` — scope names into `fix_level_params` / async signature; per-kind inclusion + abstraction; theorem body under erased lctx.
- `crates/leanr_elab/src/command/axiom.rs` — scope names; `used_vars` abstraction.
- `crates/leanr_elab/src/error.rs` — `IncludeUndeclared`, `OmitUnmatched`, `OmitReferenced`.
- `crates/leanr_meta/src/metactx.rs` — `pub fn erase_locals` (Task 4).
- `tests/fixtures/elab/dump_decls.lean`, `tests/fixtures/elab/file-queries.jsonl` — 76 rows (Task 1).
- `crates/leanr_elab/tests/oracle_file.rs`, `oracle_decl.rs` — `PENDING` filter, seam tests.

---

### Task 1: Corpus rows + pending gate filter

**Files:**
- Modify: `tests/fixtures/elab/dump_decls.lean` (the `fileQueries` list, `:290-422`)
- Modify: `tests/fixtures/elab/file-queries.jsonl` (regenerated)
- Modify: `crates/leanr_elab/tests/oracle_file.rs:127-135`

**Interfaces:**
- Produces: `const PENDING: &[&str]` in `oracle_file.rs`, the id-prefix list later tasks shrink. Prefixes: `"universe/"`, `"var/"`, `"varThm/"`, `"varAxiom/"`, `"varLevel/"`, `"include/"`, `"omit/"`.

- [ ] **Step 1: Append the 76 rows**

In `dump_decls.lean`, add a `,` after the current last `fileQueries` element and paste Appendix A's block before the closing `]` (the block's last line has no trailing comma). Do not reorder existing rows.

- [ ] **Step 2: Regenerate**

Run: `mise run fixtures:regen-decls`
Expected: exit 0, nothing on stderr for the new ids, `wc -l tests/fixtures/elab/file-queries.jsonl` = 207. `git diff --stat tests/fixtures/elab/decl-queries.jsonl` shows NO change (if it changes, stop: oracle drift, report it).
Check: `python3 target/m4c2cprobe/show.py tests/fixtures/elab/file-queries.jsonl | sed -n '/== universe\/def/,$p'` matches Appendix B line for line.

- [ ] **Step 3: Gate the new records off**

```rust
/// Id prefixes of corpus records whose feature is not ported yet. Each
/// M4c-2c-i task removes its prefixes; Task 6 deletes this list.
const PENDING: &[&str] = &[
    "universe/", "var/", "varThm/", "varAxiom/", "varLevel/", "include/", "omit/",
];

fn enabled(id: &str) -> bool {
    !PENDING.iter().any(|p| id.starts_with(p))
}
```

and in `oracle_file_gate`: `support::run_file_corpus("file-queries.jsonl", enabled)`. Leave `CORPUS_FLOOR` at 131.

- [ ] **Step 4: Run**

Run: `cargo test -p leanr_elab --test oracle_file`
Expected: PASS (`file_corpus_sources_parse_into_the_oracle_commands` parses all 207 sources: leanr's parser already has `universe`, `variable`, `include`, `omit`, `… in`).
If the parse test FAILS on a new row, report the row; do not drop it.

- [ ] **Step 5: Mutation**

Temporarily make `enabled` return `true`: `oracle_file_gate` must FAIL (on the `universe/` rows with the `— M4c-2c` seam). Revert.

- [ ] **Step 6: Commit**

```bash
git add tests/fixtures/elab/dump_decls.lean tests/fixtures/elab/file-queries.jsonl crates/leanr_elab/tests/oracle_file.rs
git commit -m "M4c-2c-i: 76 universe/variable/include/omit file-corpus rows (pending)"
```
(body: the mutation record.)

---

### Task 2: Scope universe names

**Files:**
- Modify: `crates/leanr_elab/src/command/scope.rs` (`Scope`, `Scope::root`, new `elab_universe`)
- Modify: `crates/leanr_elab/src/command/mod.rs` (dispatch arm; seed `elab.level_names`; `command_seam`)
- Modify: `crates/leanr_elab/src/command/header.rs:47-67` (`expand_decl_id`)
- Modify: `crates/leanr_elab/src/command/def.rs` (`fix_level_params`, `check_async_signature`)
- Modify: `crates/leanr_elab/src/command/axiom.rs`
- Test: `crates/leanr_elab/tests/oracle_file.rs`

**Interfaces:**
- Produces: `Scope::level_names: Vec<NameId>` (persistent-store ids, NEWEST FIRST); `fix_level_params(elab, exprs, scope: &[NameId], all_user: &[NameId])`.

- [ ] **Step 1: Enable the rows (failing test)**

Remove `"universe/"` from `PENDING`.
Run: `cargo test -p leanr_elab --test oracle_file oracle_file_gate`
Expected: FAIL: every `universe/*` record stops at `command `Lean.Parser.Command.universe` — M4c-2c`.

- [ ] **Step 2: `Scope::level_names`**

```rust
    /// oracle `Scope.levelNames` (`Command/Scope.lean:42`), NEWEST FIRST;
    /// persistent-store ids. Cloned into nested scopes, dropped at `end`.
    pub level_names: Vec<NameId>,
```
`Scope::root()` sets `level_names: Vec::new()`.

- [ ] **Step 3: `elab_universe`**

In `scope.rs` (`impl CommandElab`), next to `elab_open`:

```rust
    /// oracle: `elabUniverse` (`BuiltinCommand.lean:283-284`) →
    /// `addUnivLevel` (`Command.lean:831-837`): per name, the
    /// already-declared error, else cons onto the head scope's names.
    pub(crate) fn elab_universe(
        &mut self,
        cmd: &SyntaxNode,
        kinds: &KindInterner,
    ) -> Result<(), ElabError> {
        let ch = non_trivia_children(cmd);
        for comps in idents(ch.get(1), kinds)? {
            let id = intern_onto(self.env.store_mut(), None, None, &comps)?
                .ok_or_else(|| ill("empty universe name"))?;
            let head = self.scopes.last_mut().expect("the root scope is never popped");
            if head.level_names.contains(&id) {
                return Err(ElabError::UniverseAlreadyDeclared(comps.join(".")));
            }
            head.level_names.insert(0, id);
        }
        Ok(())
    }
```
Verify the `universe` node layout (`["universe", null-node(ident+)]`) in `leanr_syntax/src/builtin/command/` before relying on `ch.get(1)`; `universe u u` must reach the second `u` (`universe/dupSame`).

Dispatch arm in `elab_command_unlabelled`: `"Lean.Parser.Command.universe" => none(self.elab_universe(cmd, kinds)),`. In `command_seam`, drop `universe` from the `M4c-2c` arm (variable stays until Task 3).

- [ ] **Step 4: Seed term-level names**

In `elab_declaration_in_scope`, after `TermElabM::new`: `elab.level_names = head.level_names.clone();` (oracle `liftTermElabM`, `Command.lean`: the scope's `levelNames` become `Term.Context.levelNames`; `getLevelNames` then IS `scopeLevelNames`).

`expand_decl_id` (`DeclModifiers.lean:326-343`): `let mut level_names: Vec<NameId> = elab.level_names.clone();` — the existing `contains` check now also rejects `def uc.{u}` under `universe u`.

- [ ] **Step 5: Scope names into the sort**

`fix_level_params` gains `scope: &[NameId]` passed to `sort_decl_level_params(…, scope, all_user, …)` (`DeclUtil.lean:79-88`: scope names are exempt from "unused"). Callers:
- `elab_def`: `let scope = elab.level_names.clone();` at the top (before any `with_level_names`), then `fix_level_params(elab, &[ty, value], &scope, &header.level_names)`.
- `elab_axiom`: same, with `&id.level_names`.
- `check_async_signature`: its `sort_decl_level_params(…, &[], …)` becomes `&scope` (`MutualDef.lean:1290-1291`); thread `scope: &[NameId]` in.

- [ ] **Step 6: Run**

Run: `cargo test -p leanr_elab --test oracle_file --test oracle_decl`
Expected: PASS (all 15 `universe/*` and every older record).

- [ ] **Step 7: Mutations (run each, record, revert)**

1. `fix_level_params` passes `&[]` again: `universe/unusedScope` FAILS (`unused universe parameter 'v'`).
2. `expand_decl_id` starts from `Vec::new()` again: `universe/declClash` FAILS.
3. `elab_universe` appends (`push`) instead of consing: `universe/order` FAILS (levelParams order).

- [ ] **Step 8: Commit** — `M4c-2c-i: scope universe names (universe command, level-param threading)` with the mutation record.

---

### Task 3: Section-variable runner, `variable`, `withUsed` (def/abbrev/opaque/example)

**Files:**
- Create: `crates/leanr_elab/src/command/vars.rs`
- Modify: `crates/leanr_elab/src/command/scope.rs` (`Scope` fields)
- Modify: `crates/leanr_elab/src/command/mod.rs` (`mod vars;`, `next_var_uid`, `with_term_elab`, dispatch, `command_seam`)
- Modify: `crates/leanr_elab/src/command/def.rs`, `axiom.rs`, `header.rs`
- Modify: `crates/leanr_elab/src/app/elim_info.rs` (move `collect_fvars` out)
- Test: `crates/leanr_elab/tests/oracle_file.rs`, `oracle_decl.rs`

**Interfaces:**
- Consumes: Task 2's `Scope::level_names`, `fix_level_params(…, scope, …)`.
- Produces (all `pub(super)` in `command::vars` unless noted):
  - `struct SecVars { pub fvars: Vec<ExprId>, pub uids: Vec<u32>, pub included: Vec<u32>, pub omitted: Vec<u32> }`
  - `fn elab_section_vars(elab: &mut TermElabM, var_decls: &[SyntaxNode], kinds: &KindInterner) -> Result<Vec<ExprId>, ElabError>`
  - `fn used_vars(elab: &mut TermElabM, vars: &[ExprId], exprs: &[ExprId]) -> Result<Vec<ExprId>, ElabError>` (`withUsed` / `usedOnly`)
  - `fn remove_unused(elab: &mut TermElabM, vars: &[ExprId], used: &mut HashSet<ExprId>) -> Result<Vec<ExprId>, ElabError>`
  - `fn bracketed_binder_ids(binder: &SyntaxNode, kinds: &KindInterner) -> Result<Vec<Option<Vec<String>>>, ElabError>`
  - `pub(crate) fn collect_fvars(elab: &TermElabM<'_>, e: ExprId, set: &mut HashSet<ExprId>)` (moved from `elim_info.rs:211`, unchanged)
  - `CommandElab::with_term_elab<R>(&mut self, kinds, f: impl FnOnce(&mut TermElabM, &SecVars) -> Result<R, ElabError>) -> Result<R, ElabError>`
  - `Scope::{var_decls: Vec<SyntaxNode>, var_uids: Vec<u32>, included_vars: Vec<u32>, omitted_vars: Vec<u32>}`

- [ ] **Step 1: Enable the rows; update seam tests (failing)**

Remove `"var/"` from `PENDING`. In `oracle_file.rs` replace `universe_and_variable_are_m4c2c_seams` with:

```rust
#[test]
fn variable_seams_carry_their_slice() {
    // Oracle: `variable {α}` with no prior `α` declares a hole-typed
    // variable (`replaceBinderAnnotation`, `BuiltinCommand.lean:343`).
    let (at, m) = stop_seam("variable {α}");
    assert_eq!(at, 0);
    assert!(m.contains("binder-annotation update") && m.ends_with(" — later M4"), "{m}");
    // Oracle auto-binds `β` (`runTermElabM`'s `withAutoBoundImplicit`).
    let (at, m) = stop_seam("variable (x : β)");
    assert_eq!(at, 0);
    assert!(m.contains("`variable` binder") && m.ends_with(" — M4c-2c-ii"), "{m}");
}

#[test]
fn section_variables_in_a_theorem_or_axiom_wait_for_task_4() {
    // Deleted by Task 4.
    for src in [
        "variable (n : Nat)\ntheorem t : Eq n n := rfl",
        "variable (n : Nat)\naxiom a : Eq n n",
    ] {
        let (at, m) = stop_seam(src);
        assert_eq!(at, 1, "{src:?}");
        assert!(m.ends_with(" — M4c-2c-i Task 4"), "{src:?}: {m}");
    }
}
```
In `oracle_decl.rs:61` change `" — M4c-2c"` to `" — M4c-2c-ii"`.
Run: `cargo test -p leanr_elab --test oracle_file --test oracle_decl`
Expected: FAIL (gate on `var/*`, the new seam tests, the relabel).

- [ ] **Step 2: Scope fields + uid counter**

`Scope` gains (doc each with its oracle field, `Command/Scope.lean`):
```rust
    /// `varDecls`: bracketed-binder syntax, re-elaborated per run.
    pub var_decls: Vec<SyntaxNode>,
    /// `varUIds`: one id per binder id of `var_decls`, flattened, in order.
    pub var_uids: Vec<u32>,
    /// `includedVars` / `omittedVars` (`:63-65`): uids.
    pub included_vars: Vec<u32>,
    pub omitted_vars: Vec<u32>,
```
`CommandElab` gains `next_var_uid: u32` (starts at 0). The oracle's uids are macro-scoped names used only as map keys, so a counter is enough.

- [ ] **Step 3: `vars.rs` — binder ids and runner**

```rust
//! Section variables: oracle `runTermElabM` (`Elab/Command.lean:774-800`),
//! `variable` / `include` / `omit` (`Elab/BuiltinCommand.lean:415-430,
//! 551-606`) and the inclusion regimes (`MutualDef.lean:455-492,
//! 595-611`; `Declaration.lean:118`).
//!
//! Not modelled: the `unusedSectionVars` lint (a warning; the gate keeps
//! errors only), `deprecated.oldSectionVars`, auto-bound implicits
//! (`— M4c-2c-ii`), the mvar-rebuild branch of `runTermElabM` (auto-bound
//! only), `variable {α}` binder-annotation updates (`— later M4`).

/// oracle `getBracketedBinderIds` (`Command.lean:688-693`): the ids of
/// one binder, `None` for `_` and for an anonymous `[C α]`.
pub(super) fn bracketed_binder_ids(
    binder: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<Vec<Option<Vec<String>>>, ElabError>
```
Implement from the binder layouts `extract_binder_group` already reads (`builtin/binder/mod.rs:80-190`; `extract_inst_binder_layout` `:394-420` for `[x : T]`/`[T]`): an `<ident>` token decodes with `ident_components`, a `Lean.Parser.Term.hole` node is `None`.

`typeless_binder(binder, kinds) -> bool`: an explicit/implicit/strict-implicit binder whose type slot (the null node holding `[":", T]`) is empty — oracle `typelessBinder?` (`BuiltinCommand.lean:320`).

```rust
/// oracle `runTermElabM`'s `elabBinders scope.varDecls` +
/// `synthesizeSyntheticMVarsNoPostponing` (`Command.lean:777-780`): one
/// fvar per binder id, local instances registered.
pub(super) fn elab_section_vars(
    elab: &mut TermElabM,
    var_decls: &[SyntaxNode],
    kinds: &KindInterner,
) -> Result<Vec<ExprId>, ElabError> {
    let mut xs = Vec::new();
    for b in var_decls {
        let g = extract_binder_group(elab, b, kinds).map_err(variable_auto_bound_seam)?;
        xs.extend(push_binder_group(elab, &g, kinds).map_err(variable_auto_bound_seam)?);
    }
    elab.synthesize_synthetic_mvars_no_postponing(kinds)
        .map_err(variable_auto_bound_seam)?;
    Ok(xs)
}

/// The variable-binder twin of `header::unknown_ident_to_auto_bound_seam`.
fn variable_auto_bound_seam(e: ElabError) -> ElabError {
    match e {
        ElabError::UnknownIdent(s) => ElabError::UnsupportedSyntax(format!(
            "unbound `{s}` in a `variable` binder (auto-bound implicit) — M4c-2c-ii"
        )),
        e => e,
    }
}
```
`extract_binder_group` / `push_binder_group` become `pub(crate)` if they are not already (they are, `binder/mod.rs:80,195`).

- [ ] **Step 4: `with_term_elab`**

Refactor `elab_declaration_in_scope` (`mod.rs:199-230`) so the scratch/MetaCtx/TermElabM/resolve setup lives in one helper both it and Tasks 3/5's commands use:

```rust
    /// One scratch `TermElabM` over the environment with the head scope's
    /// resolution context, level names and section variables (oracle
    /// `runTermElabM`); `f` runs with the variables in the local context.
    /// Returns `f`'s result and the scratch store (for `commit`).
    fn with_term_elab<R>(
        &mut self,
        kinds: &KindInterner,
        f: impl FnOnce(&mut TermElabM, &SecVars) -> Result<R, ElabError>,
    ) -> Result<(R, Store), ElabError> {
        let mut scratch = Store::scratch();
        let out = {
            let env_view = self.env.view();
            let mctx = MetaCtx::new(env_view, &mut scratch, Config::default(), self.exts);
            let mut elab = TermElabM::new(mctx, env_view);
            let head = self.scopes.last().expect("the root scope is never popped");
            elab.resolve = ResolveCtx { ns: head.curr_namespace, open_decls: &head.open_decls,
                                        tables: &self.tables, aux_decl: None };
            elab.level_names = head.level_names.clone();
            let fvars = vars::elab_section_vars(&mut elab, &head.var_decls, kinds)?;
            if fvars.len() != head.var_uids.len() {
                return Err(ElabError::Internal("section variables: one uid per binder id".into()));
            }
            let sv = SecVars { fvars, uids: head.var_uids.clone(),
                               included: head.included_vars.clone(), omitted: head.omitted_vars.clone() };
            f(&mut elab, &sv)
        }?;
        Ok((out, scratch))
    }
```
`elab_declaration_in_scope` becomes `let (built, mut scratch) = self.with_term_elab(kinds, |elab, sv| match view.kind { DefKind::Axiom => axiom::elab_axiom(elab, view, kinds, sv), _ => def::elab_def(elab, view, kinds, &aux_cache, sv) })?;` then `commit`. (Clone `self.aux_cache` into a local first if the borrow checker requires.) The Task 2 seeding line moves into this helper.

- [ ] **Step 5: `variable` command**

```rust
    /// oracle `elabVariable` (`BuiltinCommand.lean:415-430`).
    pub(crate) fn elab_variable(&mut self, cmd: &SyntaxNode, kinds: &KindInterner) -> Result<(), ElabError> {
        let binders: Vec<SyntaxNode> = /* the bracketedBinder children of cmd[1] */;
        if binders.iter().any(|b| vars::typeless_binder(b, kinds)) {
            return Err(ElabError::UnsupportedSyntax(
                "variable binder-annotation update (`replaceBinderAnnotation`) — later M4".into()));
        }
        // Sanity elaboration (`:418-424`): the scope's variables, then these.
        self.with_term_elab(kinds, |elab, _| {
            vars::elab_section_vars(elab, &binders, kinds).map(|_| ())
        })?;
        let mut ids = 0usize;
        for b in &binders { ids += vars::bracketed_binder_ids(b, kinds)?.len(); }
        let uids: Vec<u32> = (0..ids).map(|_| { let u = self.next_var_uid; self.next_var_uid += 1; u }).collect();
        let head = self.scopes.last_mut().expect("the root scope is never popped");
        head.var_decls.extend(binders);
        head.var_uids.extend(uids);
        Ok(())
    }
```
Dispatch `"Lean.Parser.Command.variable" => none(self.elab_variable(cmd, kinds)),`; `command_seam` loses its `M4c-2c` arm entirely (`include`/`omit` keep `later M4` until Task 5).

- [ ] **Step 6: `withUsed` for def/abbrev/opaque/example**

In `vars.rs`:
```rust
/// oracle `removeUnused` (`Meta/CollectFVars.lean:53-65`): scan `vars`
/// newest first; a used var is kept and its (instantiated) type's fvars
/// join `used`.
pub(super) fn remove_unused(elab: &mut TermElabM, vars: &[ExprId], used: &mut HashSet<ExprId>)
    -> Result<Vec<ExprId>, ElabError> {
    let mut kept = Vec::new();
    for &x in vars.iter().rev() {
        if used.contains(&x) {
            let ty = elab.mctx.infer_type(x)?;
            let ty = elab.mctx.instantiate_mvars(ty)?;
            collect_fvars(elab, ty, used);
            kept.push(x);
        }
    }
    kept.reverse();
    Ok(kept)
}

/// oracle `withUsed` (`MutualDef.lean:595-611`; `Expr.collectFVars`
/// instantiates first, `Meta/CollectFVars.lean:17-19`), also the axiom's
/// `mkForallFVars vars type (usedOnly := true)` (`Declaration.lean:118`).
pub(super) fn used_vars(elab: &mut TermElabM, vars: &[ExprId], exprs: &[ExprId])
    -> Result<Vec<ExprId>, ElabError> {
    let mut used = HashSet::new();
    for &e in exprs {
        let e = elab.mctx.instantiate_mvars(e)?;
        collect_fvars(elab, e, &mut used);
    }
    remove_unused(elab, vars, &mut used)
}
```
`elab_def` gains `sv: &SecVars`. Right after `let ty = elab.mctx.instantiate_mvars(header.ty)?;` and the `TheoremTypeNotProp` check (`MutualDef.lean:1394-1401`, then `:1421-1426` `MutualClosure.main`):
```rust
    let (ty, value) = if view.kind == DefKind::Theorem {
        if !sv.fvars.is_empty() {
            return Err(ElabError::UnsupportedSyntax("section variables in a theorem — M4c-2c-i Task 4".into()));
        }
        (ty, value)
    } else {
        let kept = vars::used_vars(elab, &sv.fvars, &[ty, value])?;
        (elab.mctx.mk_forall(&kept, ty)?, elab.mctx.mk_lambda(&kept, value)?)
    };
```
This MUST come before `levelMVarToParamTypesPreDecls`, `fix_level_params` and `abstract_nested_proofs` (amendments 4, 5). `elab_axiom` gains `sv` and returns the same `— M4c-2c-i Task 4` seam when `sv.fvars` is non-empty.

Move `collect_fvars` from `app/elim_info.rs:208-220` to `vars.rs` as `pub(crate)`; `elim_info.rs` imports it.

- [ ] **Step 7: Relabel the header seam**

`header.rs:270`: `— M4c-2c` → `— M4c-2c-ii` (doc line `:266` too).

- [ ] **Step 8: Run**

Run: `cargo test -p leanr_elab --test oracle_file --test oracle_decl`
Expected: PASS, including all 20 `var/*` records.

- [ ] **Step 9: Mutations (run each, record, revert)**

1. `remove_unused` skips the type-fvar collection: no `var/` row needs it — confirm, then check `var/typeVarOnlyViaHeader` still passes and record the mutation as SURVIVING for Task 4 (`include/transitive` kills it after Task 5). Do NOT weaken; report.
2. `used_vars` ignores `value` (header only): `var/defBody` FAILS.
3. `kept` not reversed: `var/order` FAILS.
4. Abstract AFTER `abstract_nested_proofs`: `var/auxProof` FAILS.

- [ ] **Step 10: Commit** — `M4c-2c-i: section-variable runner, variable command, withUsed` (+ mutation record).

---

### Task 4: Theorem and axiom regimes; theorem body in the restricted lctx

**Files:**
- Modify: `crates/leanr_meta/src/metactx.rs` (one additive `pub fn`)
- Modify: `crates/leanr_elab/src/command/vars.rs`, `def.rs`, `axiom.rs`
- Test: `crates/leanr_elab/tests/oracle_file.rs`, `crates/leanr_meta` unit test

**Interfaces:**
- Consumes: Task 3's `SecVars`, `remove_unused`, `used_vars`, `collect_fvars`.
- Produces:
  - `MetaCtx::erase_locals(&mut self, xs: &[ExprId]) -> Result<Arc<LocalCtxSnapshot>, MetaError>` (installs the reduced context, returns the previous one for `install_lctx`).
  - `vars::header_sec_vars(elab: &mut TermElabM, sv: &SecVars, header_tys: &[ExprId], check: bool) -> Result<Vec<ExprId>, ElabError>`
  - `ElabError::OmitReferenced(String)`.

- [ ] **Step 1: Enable the rows (failing)**

Remove `"varThm/"`, `"varLevel/"` from `PENDING`, and delete `section_variables_in_a_theorem_or_axiom_wait_for_task_4`. `varAxiom/` stays pending (its `include` row needs Task 5) — instead add a narrower filter: `"varAxiom/include"` stays in `PENDING`, so replace the `"varAxiom/"` entry with `"varAxiom/include"`.
Run: `cargo test -p leanr_elab --test oracle_file oracle_file_gate`
Expected: FAIL on `varThm/*`, `varLevel/*`, `varAxiom/{inst,used}` with the Task-4 seam.

- [ ] **Step 2: `erase_locals` (leanr_meta, additive)**

```rust
    /// The current local context with every fvar in `xs` erased, installed
    /// as the ambient one (oracle `withLCtx lctx localInsts` after
    /// `removeUnused`, `MutualDef.lean:461-462`). Returns the context it
    /// replaced; the caller reinstalls it with `install_lctx`. Built on
    /// `reduce_local_context`, so local instances are filtered and
    /// renumbered with the decls.
    pub fn erase_locals(&mut self, xs: &[ExprId]) -> Result<Arc<LocalCtxSnapshot>, MetaError> {
        let cur = self.current_lctx();
        let reduced = self.reduce_local_context(&cur, xs)?;
        Ok(self.install_lctx(reduced))
    }
```
Unit test next to `install_lctx`'s tests: push `a`, an inst-implicit `i : C a` (reuse the existing local-instance fixture class in that test module), `b`; `erase_locals(&[i])` → `lctx_lookup_by_name(i's name)` is `None`, `local_instances` empty, `b` still found; reinstalling the returned snapshot restores all three and the instance.

- [ ] **Step 3: `header_sec_vars`**

```rust
/// oracle `withHeaderSecVars` (`MutualDef.lean:455-492`).
pub(super) fn header_sec_vars(elab: &mut TermElabM, sv: &SecVars, header_tys: &[ExprId], check: bool)
    -> Result<Vec<ExprId>, ElabError> {
    let mut used = HashSet::new();
    // directly referenced in headers
    for &t in header_tys {
        let t = elab.mctx.instantiate_mvars(t)?;
        collect_fvars(elab, t, &mut used);
    }
    // included by `include`
    for (&x, uid) in sv.fvars.iter().zip(&sv.uids) {
        if sv.included.contains(uid) { used.insert(x); }
    }
    // transitively referenced (`addDependencies`, `Meta/CollectFVars.lean:28-46`):
    // close over the types of everything in `used`.
    add_dependencies(elab, &mut used)?;
    if check {
        for (&x, uid) in sv.fvars.iter().zip(&sv.uids) {
            if used.contains(&x) && sv.omitted.contains(uid) {
                return Err(ElabError::OmitReferenced(user_name(elab, x)));
            }
        }
    }
    // instances whose type's fvars are all kept, in variable order
    for (&x, uid) in sv.fvars.iter().zip(&sv.uids) {
        if sv.omitted.contains(uid) { continue; }
        let (bi, ty) = local_bi_and_type(elab, x)?;
        if bi == BinderInfo::InstImplicit {
            let mut fs = HashSet::new();
            let ty = elab.mctx.instantiate_mvars(ty)?;
            collect_fvars(elab, ty, &mut fs);
            if fs.iter().all(|f| used.contains(f)) { used.insert(x); }
        }
    }
    remove_unused(elab, &sv.fvars, &mut used)
}
```
`add_dependencies`: worklist over `used` (in insertion order is not observable; a set fixpoint is equivalent): for each fvar, its lctx decl's type (instantiated) fvars join `used`; skip fvars not in the current lctx (oracle `find?` → `return ()`). `local_bi_and_type` / `user_name`: decode `Node::FVar { id: Some(id) }` from `elab.mctx.store().expr_node(Some(elab.view.store), x)`, then `elab.mctx.current_lctx().lctx().get(id)` → `LocalDecl { binder_name, ty, binder_info, .. }`. `user_name` renders `binder_name` with `crate::names::render`.

`ElabError::OmitReferenced(x)` → ``cannot omit referenced section variable `{x}` `` (error.rs: variant + `oracle_first_line` arm + the exhaustive-rendering unit test the file keeps at `:720`).

- [ ] **Step 4: Theorem path in `elab_def`**

Replace Task 3's theorem seam:
1. At the top of `elab_def`, after `level_mvar_to_param_headers`: if theorem, `let kept = vars::header_sec_vars(elab, sv, &[header.ty], true)?;` (oracle `:534`, check on; also `:1279`).
2. Async signature: `check_async_signature(elab, &header, &kept, &scope)`: first `let ty0 = elab.mctx.mk_forall(kept, header.ty)?;` then the existing `with_level_names(header.level_names) level_mvar_to_param` → instantiate → collect → sort (`:1279-1291`).
3. Body: when theorem, wrap `elab_value`:
```rust
    let erase: Vec<ExprId> = sv.fvars.iter().copied().filter(|x| !kept.contains(x)).collect();
    let prev = elab.mctx.erase_locals(&erase)?;
    let value = elab_value(elab, view, &id, &header, kinds);
    elab.mctx.install_lctx(prev);
    let value = value?;
```
4. Finish: theorem → `vars::header_sec_vars(elab, sv, &[ty], false)?` (`:1421-1423`); abstract with `mk_forall`/`mk_lambda` exactly where Task 3 abstracts defs.

- [ ] **Step 5: Axiom**

In `elab_axiom`'s closure, after `let ty = elab.mctx.mk_forall(&xs, ty)?;` and before `level_mvar_to_param`: `let kept = vars::used_vars(elab, &sv.fvars, &[ty])?; let ty = elab.mctx.mk_forall(&kept, ty)?;` (`Declaration.lean:117-119`). Remove the Task-3 seam.

- [ ] **Step 6: Run**

Run: `cargo test -p leanr_meta erase_locals && cargo test -p leanr_elab --test oracle_file --test oracle_decl`
Expected: PASS.

- [ ] **Step 7: Mutations (run each, record, revert)**

1. Don't erase for the theorem body (`erase = vec![]`): `varThm/bodyOnly` FAILS (oracle ``Unknown identifier `n` ``; leanr would admit).
2. Skip the inst-implicit loop: `varThm/inst` FAILS.
3. Inst loop ignores the "all fvars kept" test: `varThm/instNotCovered` FAILS.
4. Axiom uses `header_sec_vars` instead of `used_vars`: `varAxiom/inst` FAILS (inst kept).
5. Async signature sorts before abstracting (`mk_forall` after the sort): `varLevel/thmHole` FAILS.

- [ ] **Step 8: Commit** — `M4c-2c-i: theorem/axiom section-variable regimes; restricted theorem body` (+ mutation record).

---

### Task 5: `include` and `omit`

**Files:**
- Modify: `crates/leanr_elab/src/command/vars.rs`, `mod.rs`, `error.rs`
- Test: `crates/leanr_elab/tests/oracle_file.rs`

**Interfaces:**
- Consumes: `bracketed_binder_ids`, `with_term_elab`, `SecVars`, `header_sec_vars`.
- Produces: `CommandElab::{elab_include, elab_omit}`; `ElabError::{IncludeUndeclared(String), OmitUnmatched(String)}`.

- [ ] **Step 1: Enable the rows (failing)**

Remove `"include/"`, `"omit/"`, `"varAxiom/include"` from `PENDING` (it is now empty; keep the list for Task 6 to delete).
Run: `cargo test -p leanr_elab --test oracle_file oracle_file_gate`
Expected: FAIL (`command `Lean.Parser.Command.include` — later M4`).

- [ ] **Step 2: `include`**

```rust
    /// oracle `elabInclude` (`BuiltinCommand.lean:551-563`).
    pub(crate) fn elab_include(&mut self, cmd: &SyntaxNode, kinds: &KindInterner) -> Result<(), ElabError> {
        let ch = non_trivia_children(cmd);
        let ids = /* the <ident> tokens under ch[1], decoded with ident_components */;
        let head = self.scopes.last().expect("root");
        let mut names = Vec::new();
        for b in &head.var_decls { names.extend(vars::bracketed_binder_ids(b, kinds)?); }
        let mut uids = Vec::new();
        for id in ids {
            // `findIdx?`: the FIRST binder id with this name.
            match names.iter().position(|n| n.as_ref() == Some(&id)) {
                Some(i) => uids.push(head.var_uids[i]),
                None => return Err(ElabError::IncludeUndeclared(id.join("."))),
            }
        }
        let head = self.scopes.last_mut().expect("root");
        head.included_vars.extend(&uids);
        head.omitted_vars.retain(|u| !uids.contains(u));
        Ok(())
    }
```
Error text: ``invalid 'include', variable `{x}` has not been declared in the current scope``.

- [ ] **Step 3: `omit`**

```rust
    /// oracle `elabOmit` (`BuiltinCommand.lean:565-606`).
    pub(crate) fn elab_omit(&mut self, cmd: &SyntaxNode, kinds: &KindInterner) -> Result<(), ElabError>
```
1. Items: children of `cmd[1]`: an `<ident>` token → `Name(comps)`; an `instBinder` node with a name (`[h : T]`) → `Name`; without (`[T]`) → `Type(T syntax)`. Keep each item's rendered text: `item.text()` with whitespace runs collapsed (amendment 2).
2. `let (omitted, _) = self.with_term_elab(kinds, |elab, sv| { … })?;` inside:
   - `elab.synthesize_synthetic_mvars_no_postponing(kinds)?;`
   - elaborate each `Type(T)` with `elab.elab_term_and_synthesize(&T, kinds, None)?` (oracle `withoutErrToSorry (elabTermAndSynthesize ty none)`), in item order, BEFORE matching.
   - for each var `x` (with uid) in order: the FIRST item that matches — `Name(n)`: `x`'s user name equals `n` (render the binder name and compare to `n.join(".")`); `Type(t)`: `let cp = elab.mctx.checkpoint(); let ok = elab.mctx.is_def_eq(t, x_ty)?; elab.mctx.rollback(cp);` (`setMCtx mctx`). On a match push the uid and mark the item used.
   - the first unused item (item order) → `Err(OmitUnmatched(text))`.
3. `omitted_vars.extend(&omitted)`, `included_vars.retain(|u| !omitted.contains(u))`.

Error text: `` `{o}` did not match any variables in the current scope ``. Dispatch arms for `"Lean.Parser.Command.include"` / `"Lean.Parser.Command.omit"`. Verify both node layouts against `leanr_syntax/src/builtin/command/command_open.rs:355-370`.

- [ ] **Step 4: Run**

Run: `cargo test -p leanr_elab --test oracle_file --test oracle_decl`
Expected: PASS (all 207 records: `PENDING` is empty).

- [ ] **Step 5: Mutations (run each, record, revert)**

1. Restore Task 3 mutation 1 (`remove_unused` skips type fvars): `include/transitive` FAILS now.
2. `include` does not clear `omitted_vars`: `omit/thenInclude` FAILS.
3. `omit` does not clear `included_vars`: `omit/includeThenOmit` FAILS.
4. `[T]` matching uses syntactic equality instead of `is_def_eq`: `omit/instDefeq` FAILS.
5. A matched var stops the scan for other vars (break after first match): `omit/twoMatch` FAILS.
6. `used_vars` (def) consults `included`: `include/def` FAILS.

- [ ] **Step 6: Commit** — `M4c-2c-i: include and omit` (+ mutation record).

---

### Task 6: Gate floor, docs, ledger

**Files:**
- Modify: `crates/leanr_elab/tests/oracle_file.rs` (delete `PENDING`, `CORPUS_FLOOR` 131 → 207)
- Modify: `crates/leanr_elab/src/lib.rs` (the slice ledger), `crates/leanr_elab/src/command/mod.rs` (module doc / `command_seam` doc), `docs/superpowers/specs/2026-10-05-m4c2c-i-universe-variable-design.md` (§ Landed)

- [ ] **Step 1:** delete `PENDING`/`enabled`, pass `|_| true`; `CORPUS_FLOOR = 207`; the doc comment says "M4c-2c-i: 207".
- [ ] **Step 2:** `rg -n "M4c-2c\b|M4c-2c\"| — M4c-2c$" crates docs/superpowers/specs/2026-10-05*` — no stale `— M4c-2c` label remains (only `M4c-2c-ii`); `rg -n "Task 4\"" crates` — the temporary seam is gone.
- [ ] **Step 3:** ledger entry in `lib.rs` next to the M4c-2b-ii entry: what landed, the open seams (`— M4c-2c-ii` auto-bound; `variable {α}` update; `OmitUnmatched` source-text rendering).
- [ ] **Step 4:** spec § Landed: commits, corpus 131 → 207, deviations (the amendments above), every mutation record.
- [ ] **Step 5:** Run: `mise run ci` (block until it exits). Expected: exit 0.
- [ ] **Step 6: Commit** — `M4c-2c-i: corpus floor 207, docs, ledger`.

---

## Appendix A — corpus rows (paste into `fileQueries`)

```lean
  ("universe/def", "universe u\ndef uf1 (α : Sort u) (a : α) : α := a"),
  ("universe/thm", "universe u\ntheorem ut1 (α : Sort u) (a : α) : Eq a a := rfl"),
  ("universe/axiom", "universe u\naxiom ua1 (α : Sort u) : α"),
  ("universe/order", "universe u v\ndef uo.{w} (a : Sort w) (b : Sort v) (c : Sort u) : Sort u := c"),
  ("universe/thmOrder", "universe u v\ntheorem uto (α : Sort v) (β : Sort u) (a : α) (b : β) : Eq a a := rfl"),
  ("universe/unusedScope", "universe u v\ndef uu (α : Sort u) : Sort u := α"),
  ("universe/unusedExplicit", "universe u\ndef ue.{w} (α : Sort u) : Sort u := α"),
  ("universe/dup", "universe u\nuniverse u"),
  ("universe/dupSame", "universe u u"),
  ("universe/declClash", "universe u\ndef uc.{u} (α : Sort u) : Sort u := α"),
  ("universe/sectionDrop", "section\nuniverse u\nend\nuniverse u\ndef us (α : Sort u) : Sort u := α"),
  ("universe/withHole", "universe u\ndef uh (α : Sort u) (β : Sort _) : Sort u := α"),
  ("universe/thmWithHole", "universe u\ntheorem uth (α : Sort u) (β : Sort _) (b : β) : Eq b b := rfl"),
  ("universe/axiomUnusedScope", "universe u v\naxiom aus (α : Sort v) : α"),
  ("universe/inNamespace", "namespace A\nuniverse u\ndef un (α : Sort u) : Sort u := α\nend A"),
  ("var/defBody", "variable (n : Nat)\ndef vf1 : Nat := n"),
  ("var/defUnused", "variable (n : Nat)\ndef vf2 : Nat := Nat.zero"),
  ("var/defHeader", "variable (n : Nat)\ndef vf3 (m : Nat) (h : Eq n m) : Nat := m"),
  ("var/order", "variable (m : Nat) (n : Nat)\ndef vf4 : Nat := pick n m"),
  ("var/instDefUnref", "variable {a : Type} [Dflt a] (x : a)\ndef vf5 : a := x"),
  ("var/instDefRef", "variable {a : Type} [Dflt a] (x : a)\ndef vf6 : a := dpair x"),
  ("var/abbrev", "variable (n : Nat)\nabbrev vf7 : Nat := n"),
  ("var/example", "variable (n : Nat)\nexample : Nat := n"),
  ("var/auxProof", "variable (n : Nat)\ndef vf8 : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl"),
  ("var/multiCmd", "variable (m : Nat)\nvariable (n : Nat)\ndef vf9 : Nat := pick n m"),
  ("var/shadowBinder", "variable (n : Nat)\ndef vf10 (n : Nat) : Nat := n"),
  ("var/redeclare", "variable (n : Nat)\nvariable (n : Nat)\ndef vf11 : Nat := n"),
  ("var/sectionDrop", "section\nvariable (n : Nat)\nend\ndef vf12 : Nat := n"),
  ("var/namespace", "namespace A\nvariable (n : Nat)\ndef vf13 : Nat := n\nend A\ndef vf14 : Nat := A.vf13 Nat.zero"),
  ("var/implicitBody", "variable {n : Nat}\ndef vf15 : Nat := n"),
  ("var/strictImplicit", "variable ⦃n : Nat⦄\ndef vf16 : Nat := n"),
  ("var/typeVarOnlyViaHeader", "variable {a : Type} (x : a)\ndef vf17 (y : a) : a := y"),
  ("var/errType", "variable (n : Nat)\nvariable (x : Nat.zero)"),
  ("var/errLaterDecl", "variable (n : Nat)\ndef vf18 : Nat := m"),
  ("var/noType", "variable (n : Nat)\ndef vf19 := n"),
  ("varThm/header", "variable (n : Nat)\ntheorem vt1 : Eq n n := rfl"),
  ("varThm/unused", "variable (n : Nat)\ntheorem vt2 : Eq Nat.zero Nat.zero := rfl"),
  ("varThm/bodyOnly", "variable (n : Nat)\ntheorem vt3 : Eq Nat.zero Nat.zero := (fun (_ : Nat) => rfl) n"),
  ("varThm/inst", "variable {a : Type} [Dflt a] (x : a)\ntheorem vt4 : Eq x x := rfl"),
  ("varThm/instNotCovered", "variable {a : Type} {b : Type} [Pair a b] (x : a)\ntheorem vt5 : Eq x x := rfl"),
  ("varThm/instInProof", "variable {a : Type} [Wrap a] (x : a)\ntheorem vt6 : Eq (useWrap x) (useWrap x) := rfl"),
  ("varThm/instUsedInProofOnly", "variable {a : Type} {b : Type} [Pair a b] (x : a) (y : b)\ntheorem vt7 : Eq x x := (fun (_ : a) => rfl) (usePair x y)"),
  ("varThm/instCoveredByBinder", "variable {a : Type} {b : Type} [Pair a b] (x : a)\ntheorem vt8 (y : b) : Eq x x := rfl"),
  ("varAxiom/include", "variable (n : Nat)\ninclude n\naxiom va1 : Eq Nat.zero Nat.zero"),
  ("varAxiom/inst", "variable {a : Type} [Dflt a] (x : a)\naxiom va2 : Eq x x"),
  ("varAxiom/used", "variable (n : Nat) (m : Nat)\naxiom va3 : Eq m m"),
  ("varLevel/typeHole", "variable (α : Type _)\ndef vl1 (a : α) : α := a"),
  ("varLevel/twoHoles", "variable (α : Type _) (β : Type _)\ndef vl2 (b : β) (a : α) : β := b"),
  ("varLevel/thmHole", "variable (α : Type _)\ntheorem vl3 (a : α) : Eq a a := rfl"),
  ("varLevel/scopeUniv", "universe u\nvariable (α : Type u)\ndef vl4 (a : α) : α := a"),
  ("varLevel/axiomHole", "variable (α : Sort _)\naxiom vl5 (a : α) : α"),
  ("varLevel/holeAndExplicit", "variable (α : Type _)\ndef vl6.{v} (β : Sort v) (a : α) : α := a"),
  ("varLevel/twoDecls", "variable (α : Type _)\ndef vl7 (a : α) : α := a\ndef vl8 (a : α) : α := a"),
  ("varLevel/scopeAndExplicitThm", "universe u\nvariable (α : Sort u)\ntheorem vt9.{v} (β : Sort v) (a : α) (b : β) : Eq a a := rfl"),
  ("include/basic", "variable (n : Nat)\ninclude n\ntheorem vi1 : Eq Nat.zero Nat.zero := rfl"),
  ("include/in", "variable (n : Nat)\ninclude n in\ntheorem vi2 : Eq Nat.zero Nat.zero := rfl\ntheorem vi3 : Eq Nat.zero Nat.zero := rfl"),
  ("include/undeclared", "variable (n : Nat)\ninclude m"),
  ("include/def", "variable (n : Nat)\ninclude n\ndef vi4 : Nat := Nat.zero"),
  ("include/transitive", "variable {a : Type} (x : a)\ninclude x\ntheorem vi5 : Eq Nat.zero Nat.zero := rfl"),
  ("include/order", "variable (m : Nat) (n : Nat)\ninclude n m\ntheorem vi6 : Eq Nat.zero Nat.zero := rfl"),
  ("include/instClosure", "variable {a : Type} [Dflt a] (x : a)\ninclude x\ntheorem vi7 : Eq Nat.zero Nat.zero := rfl"),
  ("include/twice", "variable (n : Nat)\ninclude n n\ntheorem vi8 : Eq Nat.zero Nat.zero := rfl"),
  ("include/instByName", "variable {a : Type} [inst : Dflt a]\ninclude inst\ntheorem vi9 : Eq Nat.zero Nat.zero := rfl"),
  ("include/proofUsesIncluded", "variable (n : Nat)\ninclude n\ntheorem vi10 : Eq Nat.zero Nat.zero := (fun (_ : Nat) => rfl) n"),
  ("omit/inst", "variable {a : Type} [Dflt a] (x : a)\nomit [Dflt a] in\ntheorem vo1 : Eq x x := rfl"),
  ("omit/name", "variable {a : Type} [inst : Dflt a] (x : a)\nomit inst in\ntheorem vo2 : Eq x x := rfl"),
  ("omit/namedInstForm", "variable {a : Type} [inst : Dflt a] (x : a)\nomit [inst : Dflt a] in\ntheorem vo3 : Eq x x := rfl"),
  ("omit/referenced", "variable (n : Nat)\nomit n in\ntheorem vo4 : Eq n n := rfl"),
  ("omit/unmatchedName", "variable (n : Nat)\nomit m"),
  ("omit/unmatchedInst", "variable (n : Nat)\nomit [Wrap Nat]"),
  ("omit/thenInclude", "variable (n : Nat)\nomit n\ninclude n\ntheorem vo5 : Eq Nat.zero Nat.zero := rfl"),
  ("omit/includeThenOmit", "variable (n : Nat)\ninclude n\nomit n\ntheorem vo6 : Eq Nat.zero Nat.zero := rfl"),
  ("omit/def", "variable (n : Nat)\nomit n\ndef vo7 : Nat := n"),
  ("omit/axiom", "variable (n : Nat)\nomit n\naxiom vo8 : Eq n n"),
  ("omit/instDefeq", "variable {a : Type} [Dflt a] (x : a)\nomit [Dflt _] in\ntheorem vo9 : Eq x x := rfl"),
  ("omit/twoMatch", "variable {a : Type} {b : Type} [Dflt a] [Dflt b] (x : a) (y : b)\nomit [Dflt _] in\ntheorem vo10 : Eq (PProd.mk x y) (PProd.mk x y) := rfl")
```

## Appendix B — oracle results (probe 2026-10-05, `show.py` rendering; binder names erased, `d/i/s/c` = binder info)

```text
== universe/def
   defn uf1 ['u'] : ∀d:Sort u, ∀d:#0, #1   := λd:Sort u, λd:#0, #0
== universe/thm
   thm ut1 ['u'] : ∀d:Sort u, ∀d:#0, (((Eq.{u} #1) #0) #0)   := λd:Sort u, λd:#0, ((rfl.{u} #1) #0)
== universe/axiom
   axiom ua1 ['u'] : ∀d:Sort u, #0 
== universe/order
   defn uo ['u', 'v', 'w'] : ∀d:Sort w, ∀d:Sort v, ∀d:Sort u, Sort u   := λd:Sort w, λd:Sort v, λd:Sort u, #0
== universe/thmOrder
   thm uto ['u', 'v'] : ∀d:Sort v, ∀d:Sort u, ∀d:#1, ∀d:#1, (((Eq.{v} #3) #1) #1)   := λd:Sort v, λd:Sort u, λd:#1, λd:#1, ((rfl.{v} #3) #1)
== universe/unusedScope
   defn uu ['u'] : ∀d:Sort u, Sort u   := λd:Sort u, #0
== universe/unusedExplicit
   ERR unused universe parameter 'w'
== universe/dup
   ERR a universe level named `u` has already been declared
== universe/dupSame
   ERR a universe level named `u` has already been declared
== universe/declClash
   ERR a universe level named `u` has already been declared
== universe/sectionDrop
   defn us ['u'] : ∀d:Sort u, Sort u   := λd:Sort u, #0
== universe/withHole
   defn uh ['u', 'u_1'] : ∀d:Sort u, ∀d:Sort u_1, Sort u   := λd:Sort u, λd:Sort u_1, #1
== universe/thmWithHole
   thm uth ['u', 'u_1'] : ∀d:Sort u, ∀d:Sort u_1, ∀d:#0, (((Eq.{u_1} #1) #0) #0)   := λd:Sort u, λd:Sort u_1, λd:#0, ((rfl.{u_1} #1) #0)
== universe/axiomUnusedScope
   axiom aus ['v'] : ∀d:Sort v, #0 
== universe/inNamespace
   defn A.un ['u'] : ∀d:Sort u, Sort u   := λd:Sort u, #0
== var/defBody
   defn vf1 [] : ∀d:Nat, Nat   := λd:Nat, #0
== var/defUnused
   defn vf2 [] : Nat   := Nat.zero
== var/defHeader
   defn vf3 [] : ∀d:Nat, ∀d:Nat, ∀d:(((Eq.{0+1} Nat) #1) #0), Nat   := λd:Nat, λd:Nat, λd:(((Eq.{0+1} Nat) #1) #0), #1
== var/order
   defn vf4 [] : ∀d:Nat, ∀d:Nat, Nat   := λd:Nat, λd:Nat, ((pick #0) #1)
== var/instDefUnref
   defn vf5 [] : ∀i:Sort 0+1, ∀d:#0, #1   := λi:Sort 0+1, λd:#0, #0
== var/instDefRef
   defn vf6 [] : ∀i:Sort 0+1, ∀c:(Dflt #0), ∀d:#1, #2   := λi:Sort 0+1, λc:(Dflt #0), λd:#1, (((dpair #2) #1) #0)
== var/abbrev
   defn vf7 [] : ∀d:Nat, Nat   := λd:Nat, #0
== var/example
== var/auxProof
   defn vf8 [] : ∀d:Nat, ((PProd.{0+1,0} Nat) (((Eq.{0+1} Nat) (Nat.succ #0)) (Nat.succ #0)))   := λd:Nat, ((((PProd.mk.{0+1,0} Nat) (((Eq.{0+1} Nat) (Nat.succ #0)) (Nat.succ #0))) #0) (vf8._proof_1 #0))
   thm vf8._proof_1 [] : ∀d:Nat, (((Eq.{0+1} Nat) (Nat.succ #0)) (Nat.succ #0))   := λd:Nat, ((rfl.{0+1} Nat) (Nat.succ #0))
== var/multiCmd
   defn vf9 [] : ∀d:Nat, ∀d:Nat, Nat   := λd:Nat, λd:Nat, ((pick #0) #1)
== var/shadowBinder
   defn vf10 [] : ∀d:Nat, Nat   := λd:Nat, #0
== var/redeclare
   defn vf11 [] : ∀d:Nat, Nat   := λd:Nat, #0
== var/sectionDrop
   ERR Unknown identifier `n`
== var/namespace
   defn A.vf13 [] : ∀d:Nat, Nat   := λd:Nat, #0
   defn vf14 [] : Nat   := (A.vf13 Nat.zero)
== var/implicitBody
   defn vf15 [] : ∀i:Nat, Nat   := λi:Nat, #0
== var/strictImplicit
   defn vf16 [] : ∀s:Nat, Nat   := λs:Nat, #0
== var/typeVarOnlyViaHeader
   defn vf17 [] : ∀i:Sort 0+1, ∀d:#0, #1   := λi:Sort 0+1, λd:#0, #0
== var/errType
   ERR type expected, got
== var/errLaterDecl
   ERR Unknown identifier `m`
== var/noType
   defn vf19 [] : ∀d:Nat, Nat   := λd:Nat, #0
== varThm/header
   thm vt1 [] : ∀d:Nat, (((Eq.{0+1} Nat) #0) #0)   := λd:Nat, ((rfl.{0+1} Nat) #0)
== varThm/unused
   thm vt2 [] : (((Eq.{0+1} Nat) Nat.zero) Nat.zero)   := ((rfl.{0+1} Nat) Nat.zero)
== varThm/bodyOnly
   ERR Unknown identifier `n`
== varThm/inst
   thm vt4 [] : ∀i:Sort 0+1, ∀c:(Dflt #0), ∀d:#1, (((Eq.{0+1} #2) #0) #0)   := λi:Sort 0+1, λc:(Dflt #0), λd:#1, ((rfl.{0+1} #2) #0)
== varThm/instNotCovered
   thm vt5 [] : ∀i:Sort 0+1, ∀d:#0, (((Eq.{0+1} #1) #0) #0)   := λi:Sort 0+1, λd:#0, ((rfl.{0+1} #1) #0)
== varThm/instInProof
   thm vt6 [] : ∀i:Sort 0+1, ∀c:(Wrap #0), ∀d:#1, (((Eq.{0+1} #2) (((useWrap #2) #1) #0)) (((useWrap #2) #1) #0))   := λi:Sort 0+1, λc:(Wrap #0), λd:#1, ((rfl.{0+1} #2) (((useWrap #2) #1) #0))
== varThm/instUsedInProofOnly
   ERR Unknown identifier `y`
== varThm/instCoveredByBinder
   thm vt8 [] : ∀i:Sort 0+1, ∀i:Sort 0+1, ∀c:((Pair #1) #0), ∀d:#2, ∀d:#2, (((Eq.{0+1} #4) #1) #1)   := λi:Sort 0+1, λi:Sort 0+1, λc:((Pair #1) #0), λd:#2, λd:#2, ((rfl.{0+1} #4) #1)
== varAxiom/include
   axiom va1 [] : (((Eq.{0+1} Nat) Nat.zero) Nat.zero) 
== varAxiom/inst
   axiom va2 [] : ∀i:Sort 0+1, ∀d:#0, (((Eq.{0+1} #1) #0) #0) 
== varAxiom/used
   axiom va3 [] : ∀d:Nat, (((Eq.{0+1} Nat) #0) #0) 
== varLevel/typeHole
   defn vl1 ['u_1'] : ∀d:Sort u_1+1, ∀d:#0, #1   := λd:Sort u_1+1, λd:#0, #0
== varLevel/twoHoles
   defn vl2 ['u_1', 'u_2'] : ∀d:Sort u_1+1, ∀d:Sort u_2+1, ∀d:#0, ∀d:#2, #2   := λd:Sort u_1+1, λd:Sort u_2+1, λd:#0, λd:#2, #1
== varLevel/thmHole
   thm vl3 ['u_1'] : ∀d:Sort u_1+1, ∀d:#0, (((Eq.{u_1+1} #1) #0) #0)   := λd:Sort u_1+1, λd:#0, ((rfl.{u_1+1} #1) #0)
== varLevel/scopeUniv
   defn vl4 ['u'] : ∀d:Sort u+1, ∀d:#0, #1   := λd:Sort u+1, λd:#0, #0
== varLevel/axiomHole
   axiom vl5 ['u_1'] : ∀d:Sort u_1, ∀d:#0, #1 
== varLevel/holeAndExplicit
   defn vl6 ['v', 'u_1'] : ∀d:Sort u_1+1, ∀d:Sort v, ∀d:#1, #2   := λd:Sort u_1+1, λd:Sort v, λd:#1, #0
== varLevel/twoDecls
   defn vl7 ['u_1'] : ∀d:Sort u_1+1, ∀d:#0, #1   := λd:Sort u_1+1, λd:#0, #0
   defn vl8 ['u_1'] : ∀d:Sort u_1+1, ∀d:#0, #1   := λd:Sort u_1+1, λd:#0, #0
== varLevel/scopeAndExplicitThm
   thm vt9 ['u', 'v'] : ∀d:Sort u, ∀d:Sort v, ∀d:#1, ∀d:#1, (((Eq.{u} #3) #1) #1)   := λd:Sort u, λd:Sort v, λd:#1, λd:#1, ((rfl.{u} #3) #1)
== include/basic
   thm vi1 [] : ∀d:Nat, (((Eq.{0+1} Nat) Nat.zero) Nat.zero)   := λd:Nat, ((rfl.{0+1} Nat) Nat.zero)
== include/in
   thm vi2 [] : ∀d:Nat, (((Eq.{0+1} Nat) Nat.zero) Nat.zero)   := λd:Nat, ((rfl.{0+1} Nat) Nat.zero)
   thm vi3 [] : (((Eq.{0+1} Nat) Nat.zero) Nat.zero)   := ((rfl.{0+1} Nat) Nat.zero)
== include/undeclared
   ERR invalid 'include', variable `m` has not been declared in the current scope
== include/def
   defn vi4 [] : Nat   := Nat.zero
== include/transitive
   thm vi5 [] : ∀i:Sort 0+1, ∀d:#0, (((Eq.{0+1} Nat) Nat.zero) Nat.zero)   := λi:Sort 0+1, λd:#0, ((rfl.{0+1} Nat) Nat.zero)
== include/order
   thm vi6 [] : ∀d:Nat, ∀d:Nat, (((Eq.{0+1} Nat) Nat.zero) Nat.zero)   := λd:Nat, λd:Nat, ((rfl.{0+1} Nat) Nat.zero)
== include/instClosure
   thm vi7 [] : ∀i:Sort 0+1, ∀c:(Dflt #0), ∀d:#1, (((Eq.{0+1} Nat) Nat.zero) Nat.zero)   := λi:Sort 0+1, λc:(Dflt #0), λd:#1, ((rfl.{0+1} Nat) Nat.zero)
== include/twice
   thm vi8 [] : ∀d:Nat, (((Eq.{0+1} Nat) Nat.zero) Nat.zero)   := λd:Nat, ((rfl.{0+1} Nat) Nat.zero)
== include/instByName
   thm vi9 [] : ∀i:Sort 0+1, ∀c:(Dflt #0), (((Eq.{0+1} Nat) Nat.zero) Nat.zero)   := λi:Sort 0+1, λc:(Dflt #0), ((rfl.{0+1} Nat) Nat.zero)
== include/proofUsesIncluded
   thm vi10 [] : ∀d:Nat, (((Eq.{0+1} Nat) Nat.zero) Nat.zero)   := λd:Nat, (λd:Nat, ((rfl.{0+1} Nat) Nat.zero) #0)
== omit/inst
   thm vo1 [] : ∀i:Sort 0+1, ∀d:#0, (((Eq.{0+1} #1) #0) #0)   := λi:Sort 0+1, λd:#0, ((rfl.{0+1} #1) #0)
== omit/name
   thm vo2 [] : ∀i:Sort 0+1, ∀d:#0, (((Eq.{0+1} #1) #0) #0)   := λi:Sort 0+1, λd:#0, ((rfl.{0+1} #1) #0)
== omit/namedInstForm
   thm vo3 [] : ∀i:Sort 0+1, ∀d:#0, (((Eq.{0+1} #1) #0) #0)   := λi:Sort 0+1, λd:#0, ((rfl.{0+1} #1) #0)
== omit/referenced
   ERR cannot omit referenced section variable `n`
== omit/unmatchedName
   ERR `m` did not match any variables in the current scope
== omit/unmatchedInst
   ERR `[Wrap Nat]` did not match any variables in the current scope
== omit/thenInclude
   thm vo5 [] : ∀d:Nat, (((Eq.{0+1} Nat) Nat.zero) Nat.zero)   := λd:Nat, ((rfl.{0+1} Nat) Nat.zero)
== omit/includeThenOmit
   thm vo6 [] : (((Eq.{0+1} Nat) Nat.zero) Nat.zero)   := ((rfl.{0+1} Nat) Nat.zero)
== omit/def
   defn vo7 [] : ∀d:Nat, Nat   := λd:Nat, #0
== omit/axiom
   axiom vo8 [] : ∀d:Nat, (((Eq.{0+1} Nat) #0) #0) 
== omit/instDefeq
   thm vo9 [] : ∀i:Sort 0+1, ∀d:#0, (((Eq.{0+1} #1) #0) #0)   := λi:Sort 0+1, λd:#0, ((rfl.{0+1} #1) #0)
== omit/twoMatch
   thm vo10 [] : ∀i:Sort 0+1, ∀i:Sort 0+1, ∀d:#1, ∀d:#1, (((Eq.{0+1} ((PProd.{0+1,0+1} #3) #2)) ((((PProd.mk.{0+1,0+1} #3) #2) #1) #0)) ((((PProd.mk.{0+1,0+1} #3) #2) #1) #0))   := λi:Sort 0+1, λi:Sort 0+1, λd:#1, λd:#1, ((rfl.{0+1} ((PProd.{0+1,0+1} #3) #2)) ((((PProd.mk.{0+1,0+1} #3) #2) #1) #0))
```

`show.py` lives at `target/m4c2cprobe/show.py` (scratch); Task 1 copies it to `tests/fixtures/elab/show_file_corpus.py` only if a reviewer asks — it is a debugging aid, not a gate.
