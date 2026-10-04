# M4c-2a — the command loop and the env-wide aux-lemma cache — design

Status: approved in brainstorming 2026-10-04 (architectural path).
First slice of M4c-2, after M4c-1 shipped (#70, #71).

Pinned oracle: `leanprover/lean4:v4.33.0-rc1`. The citations below were
opened against that toolchain's `src/lean` while writing this spec. They are
still subject to the "verify at plan time" rule (cites drift by 1-2 lines).

## Goal

M4c-1 elaborates one declaration command into an environment. This slice
elaborates a header-less source of many commands, in order, against one
environment that grows. It also lifts the aux-lemma cache from per
declaration to environment-wide, as the oracle has it. The result is
differential-tested per command against the oracle's own run of the same
source.

**Success:**
- `CommandElab::elab_commands` elaborates every in-scope corpus record. For
  every command, the constants it adds equal the oracle's (the M4c-1
  comparison: full `ConstantInfo`, aux before main).
- A record whose last command is an oracle error stops leanr at exactly that
  command, with the same first error line.
- An aux theorem from an earlier declaration is reused exactly when the
  oracle reuses it (same type, same `levelParams`).
- Every out-of-scope command fails with a named seam, never a wrong `Ok`.
- Every existing corpus, including the 79-record `oracle_decl` gate, stays
  green and unchanged.

## Decomposition (agreed)

- **M4c-2a (this spec):** the command loop over a header-less source, plus the
  env-wide `auxLemmasExt` cache.
- **M4c-2b:** `namespace`/`section`/`end`, dotted, `protected` and `_root_`
  declaration names, `open`, full `resolveGlobalName`.
- **M4c-2c:** `universe`, `variable` (including the oracle's variable
  inclusion rules), auto-bound implicits.
- **Later:** the module header (`import` → olean closure → elaboration
  environment), and error recovery (`errToSorry`).

## User decisions

1. **No module header (Q1).** A record is a header-less multi-command source,
   run against the Elab0 environment as M4c-1's records are. Wiring imports
   to elaboration is its own later slice.
2. **Stop at the first error (Q2).** The oracle recovers from an error. Probe
   (`target/m4c2probe/P.lean`): `def a : Nat := Nat.zero + "x"` logs an
   error and still adds `a := sorry`, and a later `def b : Nat := a`
   succeeds. A duplicate `def e` adds nothing. Porting `errToSorry` (which
   places `sorry` at the innermost failing subterm) touches the whole term
   elaborator, so leanr stops at the first failing command instead. It
   claims nothing after it. Recovery is a later slice.
3. **Approach 1.** The loop lives on `CommandElab`, product code rather than
   test support. A new file-corpus gate sits alongside the unchanged
   `oracle_decl` gate. Folding the 79 single-command records into the file
   corpus was rejected: it means a full regen for no new coverage.

## The oracle model

**The loop.** The oracle's frontend parses and elaborates commands one at a
time, threading one `Command.State` (environment, messages, scopes). An
error is logged and the loop continues. Under decision 2 leanr models only
the prefix up to the first failing command.

**The aux-lemma cache** (`Meta/Tactic/AuxLemma.lean`):
- `auxLemmasExt` (`:29-30`) is an environment extension, so it lives as
  long as the environment, across declarations.
- Its key is `AuxLemmaKey` (`:16-23`): `type`, `isPrivate := !env.isExporting`
  and `defeq`. Without a `module` header, `isExporting` is false, so
  `isPrivate` is always true. `abstractNestedProofs` passes `defeq := false`.
  For this slice the key is therefore `type` alone.
- `mkAuxLemma` (`:43-79`):
  - **Hit:** a cache hit returns the cached name only if `levelParams ==`
    (`:71-73`).
  - **Mint:** otherwise it mints a name, `addDecl`s the aux (`:64`), then
    `insert`s `key → (auxName, levelParams)` (`:68`). That insert
    overwrites an entry with the same type and different `levelParams`.
  - **Rejected main:** the insert follows the aux's own `addDecl`, so an
    aux admitted before a rejected main declaration stays cached.
- Name generation (`mkAuxDeclName`, `CoreM.lean:149-153`) skips any name
  already in the environment. That includes an earlier declaration's
  `_proof_N`.

## Architecture

### The loop

```rust
pub struct FileOutcome {
    /// One entry per successfully elaborated command, in source order:
    /// admitted names (aux first, then main); empty for `example`.
    pub done: Vec<Vec<NameId>>,
    /// The first command that failed: its index and error. `None` = every
    /// command succeeded.
    pub stopped: Option<(usize, ElabError)>,
}

impl CommandElab<'_> {
    pub fn elab_commands(&mut self, cmds: &[SyntaxNode], kinds: &KindInterner) -> FileOutcome;
}
```

- **Input.** The command nodes of a `parse_module` result. The header node
  is empty (decision 1) and not passed. A parse error never reaches the
  loop: the test support fails the test, since the corpus is oracle-parsed.
- **Dispatch.** A declaration command goes to `elab_decl`, which is
  unchanged. Any other command kind stops the loop with a named seam:
  ``command `<kind>` — M4c-2b`` for `namespace`/`section`/`end`/`open`,
  ``— M4c-2c`` for `universe`/`variable`, and ``— later M4`` otherwise
  (`#print`, `instance`, …). The plan lists the kind table.
- **Stop rule.** The first `Err` ends the loop, and later commands are not
  elaborated. The environment keeps whatever `elab_decl` committed before
  failing (P2's contract: aux theorems before a rejected main declaration).
  `elab_commands`' doc names `errToSorry` as the reason it stops.

### The env-wide aux-lemma cache

Today `AuxLemmas` (`leanr_meta/src/abstract_proofs.rs:49`) carries a
per-declaration `cache: HashMap<ExprId, (NameId, Vec<NameId>)>` over scratch
ids. `mk_aux_lemma` (`:456`) already ports the oracle's hit test, the
`levelParams ==` check and overwrite-on-mint. Only the cache's lifetime is
wrong.

- **`CommandElab::aux_cache`.** A new field,
  `HashMap<ExprId, (NameId, Vec<NameId>)>`, holding persistent
  (environment-store) ids only.
- **Seeding.** `AuxLemmas::with_cache(decl_name, cache)` seeds a
  declaration's cache with a clone of `aux_cache`. `AuxLemmas::new` stays
  as the empty-cache form. Cross-declaration lookups need no translation: a
  scratch store interns through its base, so a structurally identical type,
  or a `u_N` name already in the environment, resolves to the persistent
  id.
- **Write-back from admitted constants.** `commit` rebuilds `aux_cache`
  from what it admits, not from the scratch cache. After each aux theorem's
  `add_decl_in` succeeds, it inserts `type → (name, levelParams)`, read
  from the admitted constant, so every id is persistent. Insertion follows
  admission order, so the oracle's overwrite carries over. An aux admitted
  before a rejected main declaration is cached, as in the oracle. A cache
  hit admits nothing and inserts nothing.
- **Deleted.** `CommandElab::aux_admitted`, `aux_lemma_reuse_seam`, and the
  unit test that pins that seam. `CommandElab`'s doc drops the
  per-declaration caveat.
- **Unchanged:**
  - `mk_aux_decl_name`'s conflict check (`view.get(cand)`) already sees
    earlier `_proof_N` names in the environment.
  - `example` runs no abstraction (P2 Task 8), so it never touches the
    cache. The oracle would roll the cache back anyway
    (`withoutModifyingEnv`).
  - The unsafe-aux seam.

## Harness

### Dumper

`tests/fixtures/elab/dump_decls.lean` gains a file mode. A second copy of
the encoder is not needed.

- **Selection.** `lean --run dump_decls.lean files` emits the file corpus.
  With no argument the output is byte-for-byte today's `decl-queries.jsonl`.
  `fixtures:regen-decls` gains a second step writing `file-queries.jsonl`.
- **Loop.** `fileQueries : List (String × String)` holds `(id, src)` pairs.
  Each `src` is parsed command by command (`Parser.parseCommand`, threading
  `ModuleParserState`) and elaborated with `elabCommandTopLevel`, threading
  one `Command.State` over Elab0 with `Elab.async = true`.
- **Per command.** The result is either the first error-severity message
  logged while elaborating it (from `messages` plus `snapshotTasks`, as
  `runCmd` does), or the constants added since the previous command
  (`map₂` names not present before, sorted by `Name.lt`, encoded with
  `constJ`).
- **Record.** `{"id","src","cmds":[{"consts":[C...]} | {"err":"<first line>"}]}`.
- **Generator guards.** A record with an `err` anywhere but its last command
  is reported on stderr and dropped (decision 2). So is a record that fails
  to parse.

### Gate

`crates/leanr_elab/tests/oracle_file.rs`:

- **Parse and run.** `parse_module(src)` gives the commands, and
  `elab_commands` runs them.
- **Per-command constants.** For each command `i` in `done`, its constants
  must match `cmds[i].consts`, using `run_decl_corpus`'s existing checks
  extracted into a shared `support::check_consts`: the sorted full
  `ConstantInfo` comparison, the admission order (aux before main), and the
  `sorryAx` guard.
- **Stop index.**
  - If the record ends in `err`: `stopped == Some((last, e))` with
    `e.oracle_first_line() == Some(err)`, and `done.len() == last`.
  - Otherwise: `stopped == None` and `done.len() == cmds.len()`. A seam
    anywhere in the corpus therefore fails the gate.
- **Floor.** `CORPUS_FLOOR` works as in `oracle_decl.rs`, plus a
  parse-only test.

### Corpus

About 12–15 records, every one oracle-probed at plan time:

- **Chaining:** a def referencing an earlier def; an abbrev and a theorem
  over earlier constants; a universe-polymorphic `id'.{u}` used at two
  levels.
- **Aux reuse:** an identical nested proof in a second declaration reuses
  `na._proof_1`; a distinct proof mints `nb._proof_1`.
- **Aux overwrite:** a same-type aux with different `levelParams` mints a
  fresh lemma, and a third declaration then reuses the newer one. This
  needs a level param that appears in the proof's value and not in its
  type. If plan-time probing cannot build such a source, the overwrite
  and `levelParams ==` mutations are pinned by a `CommandElab` unit test
  instead, and the plan says so.
- **Generator plus cache:** a `np/shared`-style double proof in a later
  declaration (one hit, one mint).
- **`example`:** between declarations, including an `example` whose nested
  proof would be an aux in a def, followed by a def with that proof
  (mints).
- **Errors, as the last command:** a duplicate of an earlier file-local
  declaration; a type mismatch against an earlier constant.
- **Kind coverage:** two or three of the M4c-1 single-command shapes in a
  row, so the loop exercises every `DefKind`.

### Unit pins

These cases cannot be reached from a corpus whose errors come last:
- **Mid-file error.** An error mid-file stops the loop: the right `stopped`
  index, `done.len()`, and later commands not elaborated (the environment
  lacks their names).
- **Scope command.** `namespace X` stops with the ``M4c-2b`` seam.
- **Other command.** `#print x` stops with ``later M4``.

### Mutations the plan records

Each must fail a named test:
- per-declaration cache restored (`with_cache` seeded empty) → the reuse
  record;
- keep-first instead of overwrite on write-back → the overwrite record;
- the `levelParams ==` check dropped on a hit → the overwrite record;
- loop continues past an error → the mid-file unit pin;
- write-back from the scratch cache instead of the admitted constants →
  cross-declaration lookup misses (the reuse record).

## Out of scope (named seams or unchanged)

- **Module header:** `module` and `isPrivate`.
- **Recovery:** error recovery (`errToSorry`, a declaration added despite
  an error).
- **Owned by later slices:** every non-declaration command (M4c-2b, M4c-2c,
  later M4), and everything M4c-1 already seams.
- **Message-log fidelity:** multiple errors per command, warnings, and
  linter output. The gate compares the first error line only, as in M4c-1.

## Landed

(filled in at merge)
