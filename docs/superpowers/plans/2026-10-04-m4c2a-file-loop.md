# M4c-2a: the command loop and the env-wide aux-lemma cache — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `CommandElab::elab_commands` elaborates a header-less multi-command source against one growing environment, stops at the first error, and reuses `_proof_N` aux lemmas across declarations exactly as the oracle's `auxLemmasExt` does. A 15-record per-command differential corpus gates it.

**Architecture:**
- **The loop.** `elab_commands` is a thin loop over the unchanged `elab_decl`.
- **Seams.** Non-declaration commands become named seams from one kind table, `command_seam`.
- **The cache.** The aux-lemma cache moves from `AuxLemmas`, which lives for one declaration, to `CommandElab`. It is seeded into each declaration's `AuxLemmas` and written back from the constants actually admitted, so it only ever holds persistent ids.
- **The oracle.** `dump_decls.lean` gains a `files` mode that threads one `Command.State` across a source's commands.

**Tech Stack:** Rust (workspace crates `leanr_elab`, `leanr_meta`), Lean 4 `v4.33.0-rc1` as the oracle (fixture generation only), `serde_json` in tests.

**Spec:** `docs/superpowers/specs/2026-10-04-m4c2a-file-loop-design.md`. Read its "The oracle model" and "User decisions" first. M4c-1 (`docs/superpowers/specs/2026-10-03-m4c1-single-decl-design.md`, § Landed) defines `elab_decl`, which this plan reuses unchanged.

## Global Constraints

- **Oracle pin.** `leanprover/lean4:v4.33.0-rc1`. Open every oracle citation in code against `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/` before writing it. Cites drift by 1-25 lines.
- **`leanr_meta/src`.** Only additive API that `leanr_elab` needs is allowed (the M4b accessor precedent). This plan adds exactly two items: the `AuxLemmaCache` type alias and `AuxLemmas::with_cache`.
- **`leanr_kernel`** is untouched. It is the TCB.
- **Named seams.** Every out-of-scope input returns `ElabError::UnsupportedSyntax("<what> — <slice label>")`: never a panic, never a wrong `Ok`, never an unrelated error. Slice labels: `M4c-2b` for `namespace`/`section`/`end`/`open`, `M4c-2c` for `universe`/`variable`, `later M4` for everything else.
- **Stop rule (spec decision 2).** `elab_commands` never elaborates a command after the first `Err`.
- **Build location.** Build only under `/workspace` (`target/`), never `/tmp`. `/tmp` is a 20Gi EmptyDir, and filling it evicts the pod.
- **CI.** Before every push, run `mise run ci` and block on it in-turn (fmt, clippy `-D warnings`, tests). Never background it and end the turn.
- **Mutations.** Execute every task's mutation list for real: apply the mutation, run the named test, confirm it FAILS, revert. Record the outcomes in the task's commit body. Do not trust a brief's test until a mutation fails it.
- **Concerns.** Rule explicitly on every DONE_WITH_CONCERNS item.
- **Fixtures.** Regenerate only with the mise tasks. CI never installs Lean, and the committed JSONL is the whole input.
- **Style.** Match the surrounding code. Doc comments cite the oracle line they port. `leanr_elab` integration tests use `mod support;` (`crates/leanr_elab/tests/support/mod.rs`).

## Review Focus

The happy-path corpus cannot reach these inputs, and they are the most likely to bite a user. Each one has a test in the task that owns the code.

1. **An error mid-file.** The oracle continues (`errToSorry`). leanr must stop and must not elaborate, or admit, any later command. Otherwise it would report results the oracle computes against a different environment. → Task 2 test `an_error_mid_file_stops_the_loop`.
2. **A scope command between declarations** (`namespace Foo`, `universe u`). It must stop the loop with its own slice label (`M4c-2b` / `M4c-2c`). It must not get the old blanket `M4c-2 (command loop)`, and must not be mistaken for a declaration. → Task 2 tests `scope_commands_are_m4c2b_seams` and `universe_and_variable_are_m4c2c_seams`.
3. **Other commands** (`#check`, `#print`, `mutual`). They must stop with `later M4`, not an M4c-2 label that promises a fix this milestone does not deliver. → Task 2 test `other_commands_are_later_m4_seams`.
4. **An empty source**, or one with only comments. It must elaborate nothing and report no stop, without a panic. → Task 2 test `empty_source_elaborates_nothing`.
5. **A failed declaration that leaves aux theorems behind.** When the main declaration is rejected after its aux theorems were admitted, those aux theorems must enter the cache (oracle `AuxLemma.lean:64-68`: the insert follows the aux's own `addDecl`). The stop rule makes this unobservable through `elab_commands`, but `elab_decl` is still public. → Task 3 unit test `aux_admitted_before_a_failed_main_is_cached` (`command/mod.rs`).

## Plan-time oracle facts

On 2026-10-04 every corpus record below was run through the final `dump_decls.lean files` (Task 1). A throwaway leanr probe also called `elab_decl` in sequence on one `CommandElab` (`target/m4c2probe/`, not committed). Findings:
- **leanr already matches everywhere except the aux records.** Every command of every non-`aux/` record already matches the oracle per command. Every `aux/` record fails ONLY at its second command, with the conservative `auxLemmasExt — M4c-2` seam. No term-elaborator work is hidden in this slice.
- **The `levelParams` overwrite is buildable from source** (spec § Corpus fallback NOT needed). A proof `(fun (_ : Sort u) => rfl) PUnit.{u}` carries `u` in its value but not its type. `aux/overwrite`: `ow1` mints `ow1._proof_1.{u_1}`; `ow2` (no universe) mints `ow2._proof_1` and overwrites the key; `ow3` reuses `ow2._proof_1` (admits only `ow3`); `ow4` mints `ow4._proof_1.{u_1}`. Under keep-first, `ow3` and `ow4` would both differ.
- **A universe-polymorphic hit instantiates at the caller's levels.** `aux/reuseUniv`: `pu2.{v}`'s value references `pu1._proof_1.{v}`.
- **One declaration can hit and mint.** `aux/sharedLater`: `nf` references `ne._proof_1` (hit) and mints `nf._proof_1` (a distinct type).
- **Neither `example` nor `theorem` feeds the cache.** `example/auxThenDef`: after an `example` with a nested proof, `ng` mints its own `ng._proof_1`. `thm/auxNotAbstracted`: after a theorem with the same nested proof, `th2` mints.
- **Code-generation errors are logged.** `opaque k2 : Nat := k1` over an axiom `k1` logs "`k1` not supported by code generator" (the M4c-1 compilation seam), and so does `Nat.succ` in a value ("Unknown constant `Nat.add`", as in M4c-1). The corpus avoids both.
- **The generator guard works.** With a temporary `err/notLast` record (an error in command 1 of 2), the dumper logs `an error before the last command (1/2); dropped` to stderr and emits nothing for it.
- **Default mode is unchanged.** `lean --run dump_decls.lean` with no argument reproduces the committed `decl-queries.jsonl` byte-for-byte (`cmp` clean).

---

### Task 1: File-mode oracle dumper, file corpus fixture, parse gate

**Files:**
- Modify: `tests/fixtures/elab/dump_decls.lean` (module doc; insert the file-mode block before `main`; replace `main`)
- Modify: `mise.toml` (`[tasks."fixtures:regen-decls"]`, around line 242)
- Create: `tests/fixtures/elab/file-queries.jsonl` (generated)
- Modify: `crates/leanr_elab/tests/support/mod.rs` (`parse_command` → `parse_commands` + `parse_command`, around line 1252)
- Create: `crates/leanr_elab/tests/oracle_file.rs`

**Interfaces:**
- Produces: `file-queries.jsonl`, with one record per line: `{"id","src","cmds":[{"consts":[C...]}|{"err":"<first line>"}]}`. `C` is `constJ`'s shape, as in `decl-queries.jsonl`. `err` appears only as the last element of `cmds`.
- Produces: `support::parse_commands(src: &str) -> (leanr_syntax::ParseResult, Vec<leanr_syntax::tree::SyntaxNode>)`. It returns every command node, excluding `Lean.Parser.Module.header` and `Lean.Parser.Command.eoi`, and asserts there are no parse errors.
- Produces: `oracle_file.rs`'s `const CORPUS_FLOOR: usize = 15;`.

- [ ] **Step 1: Add the file mode to the dumper.** Append this paragraph to the end of the module doc comment, before its closing `-/`:

```
File mode (`lean --run dump_decls.lean files`, M4c-2a spec
`docs/superpowers/specs/2026-10-04-m4c2a-file-loop-design.md` § Harness):
each `fileQueries` source is parsed command by command and elaborated over
ONE threaded `Command.State`, so later commands see earlier constants and
the aux-lemma cache (`auxLemmasExt`). Record shape:
  {"id","src","cmds":[{"consts":[C...]} | {"err":<string>}]}
with one element per command up to and including the first error. A
record whose error is not in its LAST command is reported on stderr and
dropped (leanr stops at the first error, spec decision 2).
```

Insert this block immediately before `unsafe def main` (after `runCmd`):

```lean
-- ===== file corpus (M4c-2a spec § Harness; every record probed at plan time) =====

/-- Multi-command sources, one command per line. Each runs against one
threaded `Command.State`; an `err` may only be the LAST command's result
(M4c-2a decision 2: leanr stops at the first error, so nothing after it
is comparable). -/
def fileQueries : List (String × String) := [
  ("chain/defRef", "def c1 : Nat := Nat.zero\ndef c2 : Nat := pick c1 c1"),
  ("chain/thmAbbrev", "def c3 (n : Nat) : Nat := pick n n\nabbrev c4 : Nat := c3 Nat.zero\ntheorem c5 : Eq c4 c4 := rfl"),
  ("chain/univ", "def idu.{u} (α : Sort u) (a : α) : α := a\ndef u1 : Nat := idu Nat Nat.zero\ndef u2 : Type := idu Type Nat"),
  ("aux/reuse", "def na (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl\ndef nb (m : Nat) : PProd Nat (Eq (Nat.succ m) (Nat.succ m)) := PProd.mk m rfl"),
  ("aux/distinct", "def nc (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl\ndef nd (n : Nat) : PProd Nat (Eq (Nat.succ (Nat.succ n)) (Nat.succ (Nat.succ n))) := PProd.mk n rfl"),
  ("aux/overwrite", "def ow1.{u} (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n ((fun (_ : Sort u) => rfl) PUnit.{u})\ndef ow2 (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl\ndef ow3 (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl\ndef ow4.{u} (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n ((fun (_ : Sort u) => rfl) PUnit.{u})"),
  ("aux/reuseUniv", "def pu1.{u} (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n ((fun (_ : Sort u) => rfl) PUnit.{u})\ndef pu2.{v} (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n ((fun (_ : Sort v) => rfl) PUnit.{v})"),
  ("aux/sharedLater", "def ne (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl\ndef nf (n : Nat) : PProd (Eq (Nat.succ n) (Nat.succ n)) (Eq (Nat.succ (Nat.succ n)) (Nat.succ (Nat.succ n))) := PProd.mk rfl rfl"),
  ("example/between", "def x1 : Nat := Nat.zero\nexample : Nat := x1\ndef x2 : Nat := pick x1 x1"),
  ("example/auxThenDef", "example (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl\ndef ng (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl"),
  ("thm/auxNotAbstracted", "theorem th1 (n : Nat) : True := (fun (_ : PProd Nat (Eq (Nat.succ n) (Nat.succ n))) => True.intro) (PProd.mk n rfl)\ndef th2 (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl"),
  ("kinds/all", "axiom k1 : Nat\nopaque k2 : Nat := Nat.zero\ntheorem k3 : True := True.intro\nabbrev k4 := k2\nexample : True := k3\ndef k5 := pick k4 k4"),
  ("err/dupLocal", "def dd : Nat := Nat.zero\ndef dd : Nat := pick Nat.zero Nat.zero"),
  ("err/mismatchEarlier", "def me : Nat := Nat.zero\ndef mf : True := me"),
  ("err/thmAfterDef", "def tq : Nat := Nat.zero\ntheorem tr : Eq tq Nat.zero := True.intro")
]

/-- The first error-severity message `s` logged, from `messages` and the
async `snapshotTasks` (see the module doc), as its first line. -/
def firstErr? (s : Command.State) : IO (Option String) := do
  let snapMsgs := s.snapshotTasks.toList.flatMap fun t =>
    t.get.getAll.toList.flatMap fun snap => snap.diagnostics.msgLog.toList
  match ((s.messages.toList ++ snapMsgs).filter (·.severity == .error)).head? with
  | some m => return some (((← m.data.toString).splitOn "\n").headD "")
  | none => return none

/-- Elaborate `src` command by command over ONE threaded `Command.State`.
Returns `(results, nCommands)`: one `{"consts"}`/`{"err"}` per command up to
and including the first error, and the number of commands the source
parses into (the commands after an error are parsed, not elaborated). -/
def runFile (env : Environment) (opts : Options) (src : String) :
    IO (Except String (Array Json × Nat)) := do
  let inputCtx := Parser.mkInputContext src "<dump_decls>"
  let ctx : Command.Context :=
    { fileName := "<dump_decls>", fileMap := inputCtx.fileMap, snap? := none, cancelTk? := none }
  let mut st := Command.mkState env {} opts
  let mut ps : Parser.ModuleParserState := {}
  let mut out : Array Json := #[]
  let mut n := 0
  let mut stopped := false
  repeat
    let scope := st.scopes.head!
    let pmctx : Parser.ParserModuleContext :=
      { env := st.env, options := scope.opts, currNamespace := scope.currNamespace,
        openDecls := scope.openDecls }
    let (stx, ps', pmsgs) := Parser.parseCommand inputCtx pmctx ps {}
    ps := ps'
    if pmsgs.hasErrors then return .error "parse error"
    if stx.isOfKind ``Parser.Command.eoi then break
    n := n + 1
    if stopped then continue
    let before : NameSet :=
      st.env.constants.map₂.toList.foldl (fun s (c, _) => s.insert c) {}
    let r ← (((Command.elabCommandTopLevel stx).run ctx).run
      { st with messages := {}, snapshotTasks := #[] }).toBaseIO
    match r with
    | .error ex =>
      out := out.push (Json.mkObj [("err", ((← ex.toMessageData.toString).splitOn "\n").headD "")])
      stopped := true
    | .ok ((), s) =>
      match ← firstErr? s with
      | some e =>
        out := out.push (Json.mkObj [("err", e)])
        stopped := true
      | none =>
        let news := ((s.env.constants.map₂.toList.map (·.1)).filter (!before.contains ·)).toArray.qsort Name.lt
        out := out.push (Json.mkObj [("consts", Json.arr (news.filterMap fun c => (s.env.find? c).map constJ))])
        st := s
  return .ok (out, n)

```

Replace the first six lines of `main` (from `unsafe def main` through `let opts : Options := Elab.async.set {} true`) with the following. The existing `for (id, src) in declQueries do …` and `declErrQueries` loops stay below it unchanged.

```lean
unsafe def main (args : List String) : IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Elab0 }] {} (trustLevel := 0) (loadExts := true)
  let opts : Options := Elab.async.set {} true
  if args == ["files"] then
    for (id, src) in fileQueries do
      match ← runFile env opts src with
      | .error msg => IO.eprintln s!"dump_decls files: {id}: {msg}"
      | .ok (cmds, n) =>
        if cmds.size != n then
          IO.eprintln s!"dump_decls files: {id}: an error before the last command ({cmds.size}/{n}); dropped"
        else
          IO.println <| Json.compress <| Json.mkObj [("id", id), ("src", src), ("cmds", Json.arr cmds)]
    return
```

- [ ] **Step 2: Add the regen step.** In `mise.toml`, `[tasks."fixtures:regen-decls"]`, append to the end of `description`: ` With the 'files' argument it also writes the M4c-2a file corpus (one threaded Command.State per multi-command source).` Then add the second `run` line:

```toml
run = [
  "sh -c 'cd tests/fixtures/elab && LEAN_PATH=$PWD lean --run dump_decls.lean > decl-queries.jsonl'",
  "sh -c 'cd tests/fixtures/elab && LEAN_PATH=$PWD lean --run dump_decls.lean files > file-queries.jsonl'",
]
```

- [ ] **Step 3: Regenerate and check.**

Run: `mise run fixtures:regen-decls 2>&1 | tail -5; wc -l tests/fixtures/elab/file-queries.jsonl; git diff --stat tests/fixtures/elab/decl-queries.jsonl`
Expected: no `dump_decls` stderr lines. `file-queries.jsonl` has 15 lines. `decl-queries.jsonl` has NO diff.

Then summarize it:

```bash
python3 - <<'EOF'
import json
for l in open('tests/fixtures/elab/file-queries.jsonl'):
    r = json.loads(l)
    print(r['id'], [('ERR ' + c['err']) if 'err' in c else [x['name'] for x in c['consts']] for c in r['cmds']])
EOF
```

Expected (the plan-time probe):

```
chain/defRef [['c1'], ['c2']]
chain/thmAbbrev [['c3'], ['c4'], ['c5']]
chain/univ [['idu'], ['u1'], ['u2']]
aux/reuse [['na', 'na._proof_1'], ['nb']]
aux/distinct [['nc', 'nc._proof_1'], ['nd', 'nd._proof_1']]
aux/overwrite [['ow1', 'ow1._proof_1'], ['ow2', 'ow2._proof_1'], ['ow3'], ['ow4', 'ow4._proof_1']]
aux/reuseUniv [['pu1', 'pu1._proof_1'], ['pu2']]
aux/sharedLater [['ne', 'ne._proof_1'], ['nf', 'nf._proof_1']]
example/between [['x1'], [], ['x2']]
example/auxThenDef [[], ['ng', 'ng._proof_1']]
thm/auxNotAbstracted [['th1'], ['th2', 'th2._proof_1']]
kinds/all [['k1'], ['k2'], ['k3'], ['k4'], [], ['k5']]
err/dupLocal [['dd'], 'ERR `dd` has already been declared']
err/mismatchEarlier [['me'], 'ERR Type mismatch']
err/thmAfterDef [['tq'], 'ERR Type mismatch']
```

If anything differs, STOP and report it. Do not edit the corpus to match.

- [ ] **Step 4: Split `parse_command` in the test support.** In `crates/leanr_elab/tests/support/mod.rs`, replace `parse_command` with:

```rust
/// Parse `src` as a header-less module; every command node, in order
/// (no `Module.header`, no `Command.eoi`). Panics on a parse error: the
/// corpora are oracle-parsed, so one is a leanr parser bug.
pub fn parse_commands(
    src: &str,
) -> (leanr_syntax::ParseResult, Vec<leanr_syntax::tree::SyntaxNode>) {
    let parsed = leanr_syntax::parse_module(src, &leanr_syntax::builtin::snapshot());
    assert!(
        parsed.errors.is_empty(),
        "leanr parse errors for {src:?}: {:?}",
        parsed.errors
    );
    let root = parsed.tree.root();
    let cmds: Vec<leanr_syntax::tree::SyntaxNode> = root
        .children()
        .filter(|n| {
            let k = parsed.tree.kinds.name(n.kind());
            k != "Lean.Parser.Module.header" && k != "Lean.Parser.Command.eoi"
        })
        .collect();
    (parsed, cmds)
}

pub fn parse_command(src: &str) -> (leanr_syntax::ParseResult, leanr_syntax::tree::SyntaxNode) {
    let (parsed, cmds) = parse_commands(src);
    assert_eq!(cmds.len(), 1, "{src:?} must be exactly one command");
    let cmd = cmds[0].clone();
    (parsed, cmd)
}
```

- [ ] **Step 5: Write the parse gate.** Create `crates/leanr_elab/tests/oracle_file.rs`:

```rust
//! M4c-2a file-corpus differential gate (spec
//! `docs/superpowers/specs/2026-10-04-m4c2a-file-loop-design.md`
//! § Harness). Every committed `{id, src, cmds}` record of
//! `file-queries.jsonl` (`tests/fixtures/elab/dump_decls.lean files`) is
//! one header-less multi-command source; leanr's parser must split it into
//! exactly the oracle's commands.

mod support;

/// `wc -l tests/fixtures/elab/file-queries.jsonl` at the last deliberate
/// regen. `>=`: adding a record is a one-line bump, not a failing gate.
const CORPUS_FLOOR: usize = 15;

#[test]
fn file_corpus_sources_parse_into_the_oracle_commands() {
    let text = std::fs::read_to_string(support::fixture_in("elab", "file-queries.jsonl"))
        .expect("committed file corpus");
    let mut n = 0;
    for line in text.lines().filter(|l| !l.trim().is_empty()) {
        let q: serde_json::Value = serde_json::from_str(line).expect("valid JSONL");
        let id = q["id"].as_str().expect("id");
        let src = q["src"].as_str().expect("src field");
        let want = q["cmds"].as_array().expect("cmds").len();
        let (_, cmds) = support::parse_commands(src);
        assert_eq!(cmds.len(), want, "{id}: leanr parses {} command(s), oracle {want}", cmds.len());
        n += 1;
    }
    assert!(n >= CORPUS_FLOOR, "file corpus shrank: {n} < {CORPUS_FLOOR}");
}
```

- [ ] **Step 6: Run the gate and the decl gate.**

Run: `cargo test -p leanr_elab --test oracle_file --test oracle_decl 2>&1 | tail -15`
Expected: PASS. `oracle_decl` is unaffected by the `parse_command` split.

- [ ] **Step 7: Mutation.** Set `CORPUS_FLOOR` to 16 and run `cargo test -p leanr_elab --test oracle_file`. Expected: FAIL `file corpus shrank: 15 < 16`. Revert.

- [ ] **Step 8: Commit.**

```bash
git add tests/fixtures/elab/dump_decls.lean tests/fixtures/elab/file-queries.jsonl mise.toml \
  crates/leanr_elab/tests/support/mod.rs crates/leanr_elab/tests/oracle_file.rs
git commit -m "M4c-2a: dump_decls.lean file mode + file corpus (15 records) + parse gate" \
  -m "Mutation: CORPUS_FLOOR 15 -> 16 FAILS file_corpus_sources_parse_into_the_oracle_commands."
```

---

### Task 2: `elab_commands`, the command seam table, and the gate on the non-aux records

**Files:**
- Modify: `crates/leanr_elab/src/command/mod.rs` (`FileOutcome`, `elab_commands`, `command_seam`)
- Modify: `crates/leanr_elab/src/command/view.rs:65-68` (use `command_seam`) and its test `unsupported_commands_are_named_seams` (around line 522)
- Modify: `crates/leanr_elab/tests/support/mod.rs` (`with_elab0_command_elab`, `with_file_elab`, `check_consts`, `run_file_corpus`; `run_decl_corpus` uses `check_consts`)
- Modify: `crates/leanr_elab/tests/oracle_file.rs` (gate + unit pins)

**Interfaces:**
- Consumes: `support::parse_commands` (Task 1); `CommandElab::elab_decl(&mut self, &SyntaxNode, &KindInterner) -> Result<Vec<NameId>, ElabError>` (M4c-1, unchanged).
- Produces, in `leanr_elab::command`:
  - `pub struct FileOutcome { pub done: Vec<Vec<NameId>>, pub stopped: Option<(usize, ElabError)> }` (derives `Debug`);
  - `CommandElab::elab_commands(&mut self, cmds: &[SyntaxNode], kinds: &KindInterner) -> FileOutcome`;
  - `pub(crate) fn command_seam(kind: &str) -> ElabError`.
- Produces in the test support:
  - `with_elab0_command_elab<R>(k: impl FnOnce(&mut CommandElab<'_>) -> R) -> R`;
  - `with_file_elab<R>(src, k: impl FnOnce(&mut CommandElab<'_>, &[SyntaxNode], &KindInterner) -> R) -> R`;
  - `check_consts(id: &str, env: &leanr_kernel::Environment, names: &[NameId], want: &[serde_json::Value], failures: &mut Vec<String>)`;
  - `run_file_corpus(queries: &str, enabled: impl Fn(&str) -> bool) -> usize`.

- [ ] **Step 1: Write the failing unit pins.** Append to `crates/leanr_elab/tests/oracle_file.rs`:

```rust
fn outcome(src: &str) -> (Vec<Vec<String>>, Option<(usize, leanr_elab::ElabError)>, usize) {
    support::with_file_elab(src, |ce, cmds, kinds| {
        let before = ce.env().len();
        let out = ce.elab_commands(cmds, kinds);
        let st = ce.env().store();
        let done = out
            .done
            .iter()
            .map(|ns| ns.iter().map(|&n| support::name_to_string(st, None, Some(n))).collect())
            .collect();
        // How many constants the run admitted in total.
        (done, out.stopped, ce.env().len() - before)
    })
}

fn stop_seam(src: &str) -> (usize, String) {
    match outcome(src).1 {
        Some((i, leanr_elab::ElabError::UnsupportedSyntax(m))) => (i, m),
        other => panic!("{src:?}: expected a seam stop, got {other:?}"),
    }
}

#[test]
fn an_error_mid_file_stops_the_loop() {
    // Oracle: `la` logs a type mismatch and is still added (`errToSorry`),
    // then `lb` and `lc` elaborate. leanr stops at `la` (spec decision 2).
    let (done, stopped, added) = outcome(
        "def la : Nat := True.intro\ndef lb : Nat := Nat.zero\ndef lc : Nat := lb",
    );
    assert!(done.is_empty(), "{done:?}");
    match stopped {
        Some((0, e)) => assert_eq!(e.oracle_first_line().as_deref(), Some("Type mismatch")),
        other => panic!("expected a stop at command 0, got {other:?}"),
    }
    assert_eq!(added, 0, "nothing at or after the stop is admitted");
}

#[test]
fn a_mid_file_error_after_successes_keeps_them() {
    let (done, stopped, added) =
        outcome("def la : Nat := Nat.zero\ndef lb : Nat := True.intro\ndef lc : Nat := la");
    assert_eq!(done, vec![vec!["la".to_string()]]);
    assert!(matches!(stopped, Some((1, _))), "{stopped:?}");
    assert_eq!(added, 1, "only `la`");
}

#[test]
fn scope_commands_are_m4c2b_seams() {
    for (src, i) in [
        ("def la : Nat := Nat.zero\nnamespace Foo", 1),
        ("section S", 0),
        ("open Nat", 0),
        ("def la : Nat := Nat.zero\nend", 1),
    ] {
        let (at, m) = stop_seam(src);
        assert_eq!(at, i, "{src:?}");
        assert!(m.ends_with(" — M4c-2b"), "{src:?}: {m}");
    }
}

#[test]
fn universe_and_variable_are_m4c2c_seams() {
    for src in ["universe u", "variable (n : Nat)"] {
        let (at, m) = stop_seam(src);
        assert_eq!(at, 0);
        assert!(m.ends_with(" — M4c-2c"), "{src:?}: {m}");
    }
}

#[test]
fn other_commands_are_later_m4_seams() {
    for src in ["#check Nat", "#print Nat", "mutual\ndef la : Nat := Nat.zero\nend"] {
        let (_, m) = stop_seam(src);
        assert!(m.ends_with(" — later M4"), "{src:?}: {m}");
    }
}

#[test]
fn empty_source_elaborates_nothing() {
    for src in ["", "-- just a comment\n", "/- block -/"] {
        let (done, stopped, _) = outcome(src);
        assert!(done.is_empty() && stopped.is_none(), "{src:?}: {done:?} {stopped:?}");
    }
}
```

- [ ] **Step 2: Run the pins to verify they fail.**

Run: `cargo test -p leanr_elab --test oracle_file 2>&1 | tail -15`
Expected: compile FAIL, with `elab_commands` and `with_file_elab` not found.

- [ ] **Step 3: Test support.** In `crates/leanr_elab/tests/support/mod.rs`, make the Elab0 replay in `with_command_elab` reusable and add the file helpers. Replace the body of `with_command_elab` from `let Replayed {` to its end with a call through a new helper:

```rust
/// Replay Elab0 into a fresh owned `Environment` and run `k` with a
/// `CommandElab` over it. One replay per call: every corpus record gets
/// its own environment.
pub fn with_elab0_command_elab<R>(
    k: impl FnOnce(&mut leanr_elab::command::CommandElab<'_>) -> R,
) -> R {
    let Replayed {
        env,
        reducibility,
        matchers,
        instances,
        default_instances,
        projection_fns,
        classes,
        coe_decls,
        aux_recs,
        elab_as_elim,
        structures,
    } = replay_fixture_in("elab", "Elab0.olean");
    let exts = leanr_meta::EnvExtensions {
        reducibility: &reducibility,
        matchers: &matchers,
        instances: &instances,
        default_instances: &default_instances,
        projection_fns: &projection_fns,
        classes: &classes,
        coe_decls: &coe_decls,
        aux_recs: &aux_recs,
        elab_as_elim: &elab_as_elim,
        structures: &structures,
    };
    let mut ce = leanr_elab::command::CommandElab::new(env, exts);
    k(&mut ce)
}
```

`with_command_elab` becomes:

```rust
pub fn with_command_elab<R>(
    src: &str,
    k: impl FnOnce(
        &mut leanr_elab::command::CommandElab<'_>,
        &leanr_syntax::tree::SyntaxNode,
        &leanr_syntax::kind::KindInterner,
    ) -> R,
) -> R {
    let (parsed, cmd) = parse_command(src);
    with_elab0_command_elab(|ce| k(ce, &cmd, &parsed.tree.kinds))
}

/// `with_command_elab` for a multi-command source: every command node.
pub fn with_file_elab<R>(
    src: &str,
    k: impl FnOnce(
        &mut leanr_elab::command::CommandElab<'_>,
        &[leanr_syntax::tree::SyntaxNode],
        &leanr_syntax::kind::KindInterner,
    ) -> R,
) -> R {
    let (parsed, cmds) = parse_commands(src);
    with_elab0_command_elab(|ce| k(ce, &cmds, &parsed.tree.kinds))
}

```

Extract the per-command comparison from `run_decl_corpus`. Its block from `let env = ce.env();` (the admission-order check) through the `if got_json != want { … }` push becomes:

```rust
/// Compare the constants one command admitted (`names`, in admission
/// order) with the oracle's `want` (sorted by `Name.lt`, `constJ` shape):
/// the admission order (every `_proof_N` before the main declaration),
/// no `sorryAx`/fvar/mvar/level-mvar, and the canonical JSON.
pub fn check_consts(
    id: &str,
    env: &leanr_kernel::Environment,
    names: &[leanr_kernel::bank::NameId],
    want: &[serde_json::Value],
    failures: &mut Vec<String>,
) {
    use serde_json::Value;
    let rendered: Vec<String> = names
        .iter()
        .map(|&n| name_to_string(env.store(), None, Some(n)))
        .collect();
    if let Some((last, auxes)) = rendered.split_last() {
        if last.contains("._proof_") || auxes.iter().any(|a| !a.contains("._proof_")) {
            failures.push(format!("{id}: admission order {rendered:?}"));
        }
    }
    let mut sorted = names.to_vec();
    sorted.sort_by(|a, b| leanr_meta::name_cmp(env.store(), None, Some(*a), Some(*b)));
    let got_json: Vec<Value> = sorted.iter().map(|&n| decl_const_json(env, n)).collect();
    let s = Value::Array(got_json.clone()).to_string();
    for bad in [
        "\"sorryAx\"",
        "\"k\":\"fvar\"",
        "\"k\":\"mvar\"",
        "\"k\":\"lmvar\"",
    ] {
        if s.contains(bad) {
            failures.push(format!("{id}: admitted constant contains {bad}"));
        }
    }
    if got_json != want {
        failures.push(format!(
            "{id}:\n  leanr  {s}\n  oracle {}",
            Value::Array(want.to_vec())
        ));
    }
}
```

In `run_decl_corpus`, the `Ok(ns)` path becomes `check_consts(&id, ce.env(), &names, &want, &mut failures);`. Keep `let want = q["consts"].as_array().expect("consts").clone();` and the `Err(e)` arm as they are. Before moving on, run `cargo test -p leanr_elab --test oracle_decl`. Expected: PASS (refactor only).

Add the file-corpus runner:

```rust
/// Elaborate every enabled `{id, src, cmds}` record of
/// `tests/fixtures/elab/<queries>` with `elab_commands` in its own fresh
/// Elab0 environment and compare per command with the oracle
/// (`check_consts`), plus the stop: leanr must stop exactly at the
/// oracle's `err` (always the last command) with the same first line, or
/// not at all. Panics listing every divergence; returns the number of
/// records checked.
pub fn run_file_corpus(queries: &str, enabled: impl Fn(&str) -> bool) -> usize {
    use serde_json::Value;
    let text = std::fs::read_to_string(fixture_in("elab", queries))
        .unwrap_or_else(|e| panic!("committed file corpus {queries}: {e}"));
    let mut failures = Vec::new();
    let mut checked = 0usize;
    for line in text.lines().filter(|l| !l.trim().is_empty()) {
        let q: Value = serde_json::from_str(line).expect("committed JSONL is valid");
        let id = q["id"].as_str().expect("id").to_string();
        if !enabled(&id) {
            continue;
        }
        checked += 1;
        let src = q["src"].as_str().expect("src").to_string();
        assert!(
            !q.to_string().contains("\"sorryAx\""),
            "{id}: the oracle record contains sorryAx — it is an oracle error"
        );
        let want = q["cmds"].as_array().expect("cmds").clone();
        with_file_elab(&src, |ce, cmds, kinds| {
            assert_eq!(cmds.len(), want.len(), "{id}: command count");
            let out = ce.elab_commands(cmds, kinds);
            let want_err = want.last().and_then(|c| c.get("err")).and_then(Value::as_str);
            let n_ok = want.len() - usize::from(want_err.is_some());
            match (&out.stopped, want_err) {
                (None, None) => {}
                (Some((i, e)), Some(w)) if *i == n_ok => {
                    let line = e.oracle_first_line();
                    if line.as_deref() != Some(w) {
                        failures.push(format!(
                            "{id}[{i}]: leanr error {e:?} (first line {line:?}); oracle {w:?}"
                        ));
                    }
                }
                (Some((i, e)), _) => failures.push(format!(
                    "{id}[{i}]: leanr stopped with {e:?}; oracle {}",
                    want[*i]
                )),
                (None, Some(w)) => failures.push(format!(
                    "{id}: leanr elaborated every command; oracle's last errors with {w:?}"
                )),
            }
            for (i, names) in out.done.iter().enumerate() {
                let Some(w) = want[i]["consts"].as_array() else {
                    failures.push(format!("{id}[{i}]: leanr admitted; oracle {}", want[i]));
                    continue;
                };
                check_consts(&format!("{id}[{i}]"), ce.env(), names, w, &mut failures);
            }
        });
    }
    assert!(
        failures.is_empty(),
        "{} file divergence(s):\n{}",
        failures.len(),
        failures.join("\n")
    );
    checked
}
```

- [ ] **Step 4: Implement `FileOutcome`, `elab_commands` and `command_seam`.** In `crates/leanr_elab/src/command/mod.rs`, update the module doc's first sentence to add "M4c-2a: a header-less source of many commands (`elab_commands`), spec `docs/superpowers/specs/2026-10-04-m4c2a-file-loop-design.md`." Add after `Built`:

```rust
/// What [`CommandElab::elab_commands`] did with a source's commands.
#[derive(Debug)]
pub struct FileOutcome {
    /// One entry per command elaborated successfully, in source order:
    /// its admitted names (aux `_proof_N` first, the main declaration
    /// last); empty for `example`.
    pub done: Vec<Vec<NameId>>,
    /// The first command that failed: its index and error. `None` = every
    /// command succeeded. Nothing after it was elaborated.
    pub stopped: Option<(usize, ElabError)>,
}
```

Add to `impl CommandElab`, after `elab_decl`:

```rust
    /// Elaborate a header-less source's commands in order against this
    /// growing environment (the oracle frontend's command loop, threading
    /// one `Command.State`).
    ///
    /// Stops at the first error (spec decision 2). The oracle logs the error
    /// and goes on, but it has usually ADDED the failed declaration with
    /// `sorry` in place of the failing subterm (`errToSorry`), so every
    /// later command runs against an environment leanr does not have. Error
    /// recovery is a later slice. What the failed command committed before
    /// failing stays (`elab_decl`'s contract).
    pub fn elab_commands(&mut self, cmds: &[SyntaxNode], kinds: &KindInterner) -> FileOutcome {
        let mut done = Vec::with_capacity(cmds.len());
        for (i, cmd) in cmds.iter().enumerate() {
            match self.elab_decl(cmd, kinds) {
                Ok(names) => done.push(names),
                Err(e) => {
                    return FileOutcome {
                        done,
                        stopped: Some((i, e)),
                    }
                }
            }
        }
        FileOutcome {
            done,
            stopped: None,
        }
    }
```

Add as a free function, after `label_seam`:

```rust
/// The named seam for a command that is not a declaration, labelled with
/// the slice that ports it (spec § Decomposition).
pub(crate) fn command_seam(kind: &str) -> ElabError {
    let slice = match kind {
        "Lean.Parser.Command.namespace"
        | "Lean.Parser.Command.section"
        | "Lean.Parser.Command.end"
        | "Lean.Parser.Command.open" => "M4c-2b",
        "Lean.Parser.Command.universe" | "Lean.Parser.Command.variable" => "M4c-2c",
        _ => "later M4",
    };
    ElabError::UnsupportedSyntax(format!("command `{kind}` — {slice}"))
}
```

In `view.rs`, `DefView::from_syntax`, replace

```rust
        if ck != "Lean.Parser.Command.declaration" {
            return Err(seam(format!("command `{ck}` — M4c-2 (command loop)")));
        }
```

with

```rust
        if ck != "Lean.Parser.Command.declaration" {
            return Err(super::command_seam(ck));
        }
```

and update `unsupported_commands_are_named_seams`'s last three assertions:

```rust
        assert!(seam("namespace Foo").ends_with(" — M4c-2b"));
        assert!(seam("#check Nat").ends_with(" — later M4"));
        assert!(seam("mutual\ndef a : Nat := Nat.zero\nend").ends_with(" — later M4"));
```

Before relying on the kind names, check them. Run `grep -rn '"Lean.Parser.Command.\(namespace\|section\|end\|open\|universe\|variable\|mutual\|print\|check\)"' crates/leanr_syntax/src` and confirm that each of the six table kinds is the OUTER node kind the parser produces. For example, `open Nat` must give a node whose kind is `Lean.Parser.Command.open`, not `openSimple`. The unit pins in Step 1 are the check.

- [ ] **Step 5: Add the gate on the non-aux records.** Append to `oracle_file.rs`:

```rust
#[test]
fn oracle_file_gate() {
    // M4c-2a Task 3 lifts the `aux/` filter (env-wide auxLemmasExt cache).
    let checked = support::run_file_corpus("file-queries.jsonl", |id| !id.starts_with("aux/"));
    assert!(checked >= 9, "non-aux file records: checked {checked}");
}
```

- [ ] **Step 6: Run everything touched.**

Run: `cargo test -p leanr_elab --test oracle_file --test oracle_decl --lib command 2>&1 | tail -20`
Expected: PASS. All `oracle_file` tests pass, `oracle_decl` stays at 79, and the `view.rs` unit tests pass.

- [ ] **Step 7: Mutations.** Run each, confirm FAIL, revert:
1. In `elab_commands`, replace the `Err(e) => return …` arm with `Err(e) => { if first.is_none() { first = Some((i, e)) } }` (declare `let mut first = None;` and return `stopped: first`): the loop continues past an error. → `an_error_mid_file_stops_the_loop` FAILS (`added` is 2).
2. `stopped: Some((i + 1, e))`. → `oracle_file_gate` FAILS on `err/dupLocal` and `an_error_mid_file_stops_the_loop` FAILS.
3. In `command_seam`, move `"Lean.Parser.Command.open"` to the `M4c-2c` arm. → `scope_commands_are_m4c2b_seams` FAILS.
4. In `run_file_corpus`, drop the `if *i == n_ok` guard. → none of the committed tests fails, because the generator guarantees `err` is last. Record this as an equivalent harness mutation: the guard documents the invariant rather than testing it.

- [ ] **Step 8: Commit.**

```bash
git add crates/leanr_elab/src/command/mod.rs crates/leanr_elab/src/command/view.rs \
  crates/leanr_elab/tests/support/mod.rs crates/leanr_elab/tests/oracle_file.rs
git commit -m "leanr_elab: CommandElab::elab_commands (stop at first error) + command seam table; file gate on non-aux records" \
  -m "<mutation outcomes 1-4 from Step 7>"
```

---

### Task 3: The env-wide aux-lemma cache

**Files:**
- Modify: `crates/leanr_meta/src/abstract_proofs.rs:46-80` (`AuxLemmaCache`, `AuxLemmas::with_cache`)
- Modify: `crates/leanr_meta/src/lib.rs:51` (export `AuxLemmaCache`)
- Modify: `crates/leanr_elab/src/command/def.rs` (`elab_def` takes the cache)
- Modify: `crates/leanr_elab/src/command/mod.rs` (`aux_cache` replaces `aux_admitted`; write-back in `commit`; delete `aux_lemma_reuse_seam`; the `CommandElab` doc)
- Modify: `crates/leanr_elab/tests/oracle_decl.rs:253-279` (the seam test becomes the reuse pin)
- Modify: `crates/leanr_elab/tests/oracle_file.rs` (lift the `aux/` filter; floor 15)
- Test: `crates/leanr_elab/src/command/mod.rs` `tests` (the failed-main pin)

**Interfaces:**
- Consumes: `elab_commands`, `run_file_corpus` (Task 2).
- Produces:
  - `leanr_meta::AuxLemmaCache = HashMap<ExprId, (NameId, Vec<NameId>)>`;
  - `AuxLemmas::with_cache(decl_name: NameId, cache: AuxLemmaCache) -> AuxLemmas`;
  - `def::elab_def(elab, view, kinds, aux_cache: &AuxLemmaCache)`.

- [ ] **Step 1: Turn the seam test into the reuse pin, and add the failed-main pin.** In `crates/leanr_elab/tests/oracle_decl.rs`, replace `aux_lemma_reuse_across_declarations_is_a_seam` with:

```rust
#[test]
fn aux_lemma_is_reused_across_declarations() {
    // Oracle probe (env threaded across commands, `aux/reuse`): after `na`
    // admits `na._proof_1`, an identical `nb` REUSES it (`auxLemmasExt`,
    // `Meta/Tactic/AuxLemma.lean:70-73`) and admits only `nb`.
    let na = "def na (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl";
    let nb = "def nb (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl";
    support::with_command_elab(na, |ce, cmd, kinds| {
        let first = ce.elab_decl(cmd, kinds).expect("na admits");
        assert_eq!(first.len(), 2, "na._proof_1 then na");
        let before = ce.env().len();
        let (parsed, cmd2) = support::parse_command(nb);
        let second = ce.elab_decl(&cmd2, &parsed.tree.kinds).expect("nb admits");
        let st = ce.env().store();
        let names: Vec<String> = second
            .iter()
            .map(|&n| support::name_to_string(st, None, Some(n)))
            .collect();
        assert_eq!(names, vec!["nb".to_string()]);
        assert_eq!(ce.env().len(), before + 1);
    });
}
```

Add the failed-main pin (Review Focus 5) to the `tests` module of `crates/leanr_elab/src/command/mod.rs`. No source in the Elab0 corpus gets a main declaration past the elaborator and then rejected by the kernel, so the pin drives `commit` directly with hand-built declarations. The fixture was run at plan time against the pre-change `commit`. It returned `Err(Kernel(DefTypeMismatch(t)))` with `t._proof_1` admitted.

```rust
    #[test]
    fn aux_admitted_before_a_failed_main_is_cached() {
        // oracle: `mkAuxLemma` inserts into `auxLemmasExt` right after the
        // aux's own `addDecl` (`Meta/Tactic/AuxLemma.lean:64-68`), so the
        // entry survives the main declaration's rejection.
        use leanr_kernel::{
            BinderInfo, ConstantVal, DefinitionSafety, DefinitionVal, Nat, ReducibilityHints,
            TheoremVal,
        };
        let exts = EnvExtensions {
            reducibility: &[],
            matchers: &[],
            instances: &[],
            default_instances: &[],
            projection_fns: &[],
            classes: &[],
            coe_decls: &[],
            structures: &[],
            aux_recs: &[],
            elab_as_elim: &[],
        };
        let mut ce = CommandElab::new(Environment::default(), exts);
        let mut scratch = Store::scratch();
        let (aux, main) = {
            let base = Some(ce.env.store());
            let s = &mut scratch;
            let zero = s.level_zero(base).unwrap();
            let prop = s.expr_sort(base, zero).unwrap();
            let b0 = s.expr_bvar(base, &Nat::from(0u64)).unwrap();
            let b1 = s.expr_bvar(base, &Nat::from(1u64)).unwrap();
            // `t._proof_1 : ∀ (p : Prop) (h : p), p := fun p h => h`
            let inner_ty = s.expr_forall(base, None, b0, b1, BinderInfo::Default).unwrap();
            let ty = s.expr_forall(base, None, prop, inner_ty, BinderInfo::Default).unwrap();
            let inner_val = s.expr_lam(base, None, b0, b0, BinderInfo::Default).unwrap();
            let value = s.expr_lam(base, None, prop, inner_val, BinderInfo::Default).unwrap();
            let t = s.intern_str(base, "t").unwrap();
            let t = s.name_str(base, None, t).unwrap();
            let p1 = s.intern_str(base, "_proof_1").unwrap();
            let p1 = s.name_str(base, Some(t), p1).unwrap();
            let aux = Declaration::Thm(TheoremVal {
                val: ConstantVal { name: p1, level_params: vec![], ty },
                value,
                all: vec![p1],
            });
            // `def t : Prop := Prop` is ill-typed (`Prop : Type`): the
            // kernel rejects the main declaration after admitting the aux.
            let main = Declaration::Defn(DefinitionVal {
                val: ConstantVal { name: t, level_params: vec![], ty: prop },
                value: prop,
                hints: ReducibilityHints::Regular(1),
                safety: DefinitionSafety::Safe,
                all: vec![t],
            });
            (aux, main)
        };
        let r = ce.commit(&mut scratch, Built::Add(vec![aux, main]));
        assert!(matches!(r, Err(ElabError::Kernel(_))), "{r:?}");
        assert_eq!(ce.env.len(), 1, "the aux stays admitted");
        assert_eq!(ce.aux_cache.len(), 1, "and cached");
        let (&ty, &(name, ref lps)) = ce.aux_cache.iter().next().unwrap();
        let cv = ce.env.get(name).expect("cached name is admitted").constant_val();
        assert_eq!(cv.ty, ty, "keyed by the admitted (persistent) type");
        assert!(lps.is_empty());
    }
```

- [ ] **Step 2: Lift the gate filter, and verify that it and the pin fail.** In `oracle_file.rs`, make `oracle_file_gate`:

```rust
#[test]
fn oracle_file_gate() {
    let checked = support::run_file_corpus("file-queries.jsonl", |_| true);
    assert!(
        checked >= CORPUS_FLOOR,
        "file corpus shrank: checked {checked}, floor {CORPUS_FLOOR}. Check \
         `dump_decls.lean files`' stderr for a dropped record, or lower the floor deliberately."
    );
}
```

Run: `cargo test -p leanr_elab --test oracle_file --test oracle_decl 2>&1 | tail -20`
Expected: FAIL. `oracle_file_gate` reports the 5 `aux/` records stopping at command 1 with `aux-lemma reuse across declarations (auxLemmasExt) — M4c-2`, and `aux_lemma_is_reused_across_declarations` panics on `expect("nb admits")`. (`aux_admitted_before_a_failed_main_is_cached` does not compile yet: there is no `aux_cache` field.)

- [ ] **Step 3: Add `AuxLemmaCache` and `with_cache` in `leanr_meta`.** In `abstract_proofs.rs`, before `pub struct AuxLemmas`:

```rust
/// The `auxLemmasExt` state (`Meta/Tactic/AuxLemma.lean:25-30`): aux-lemma
/// type → (name, levelParams). The oracle's key `AuxLemmaKey` (`:16-23`)
/// also holds `isPrivate := !env.isExporting` and `defeq`. Without a
/// `module` header `isExporting` is false, and `abstractNestedProofs`
/// passes `defeq := false`, so both are constant and the key is the type
/// alone. Hash-consing makes `ExprId` equality structural, as the oracle's
/// `BEq Expr` is.
pub type AuxLemmaCache = HashMap<ExprId, (NameId, Vec<NameId>)>;
```

Change the `cache` field to:

```rust
    /// Seeded from the caller's environment-wide cache (`with_cache`);
    /// `mk_aux_lemma` reads it and inserts what it mints.
    cache: AuxLemmaCache,
```

Replace `new` with:

```rust
    /// `withDeclNameForAuxNaming decl_name` (`CoreM.lean:158-169`, entered at
    /// `PreDefinition/Basic.lean:125`): a fresh generator, prefix
    /// `decl_name`, index 1, and an empty aux-lemma cache.
    pub fn new(decl_name: NameId) -> Self {
        Self::with_cache(decl_name, AuxLemmaCache::new())
    }

    /// `new`, seeded with the environment's `auxLemmasExt` state, so a
    /// nested proof whose type an earlier declaration's aux lemma already
    /// has reuses that constant (`AuxLemma.lean:70-73`). `cache`'s ids must
    /// be resolvable from the caller's store: environment-store ids are.
    pub fn with_cache(decl_name: NameId, cache: AuxLemmaCache) -> Self {
        AuxLemmas {
            decl_name,
            next_idx: 1,
            cache,
            pending: Vec::new(),
        }
    }
```

In `lib.rs:51`: `pub use abstract_proofs::{AuxLemmaCache, AuxLemmas};`

- [ ] **Step 4: Thread the cache through `elab_def`.** In `def.rs`, add `AuxLemmaCache` to the `leanr_meta::{…}` import and a parameter to `elab_def`:

```rust
pub(super) fn elab_def(
    elab: &mut TermElabM,
    view: &DefView,
    kinds: &KindInterner,
    aux_cache: &AuxLemmaCache,
) -> Result<Built, ElabError> {
```

Replace `let mut aux = AuxLemmas::new(id.name);` with:

```rust
    // The cache is the environment's (`auxLemmasExt`), seeded per
    // declaration; `CommandElab::commit` writes back what is admitted.
    let mut aux = AuxLemmas::with_cache(id.name, aux_cache.clone());
```

- [ ] **Step 5: Put `aux_cache` on `CommandElab` and write it back in `commit`.** In `command/mod.rs`:
- Import: `use leanr_meta::{AuxLemmaCache, Config, EnvExtensions, MetaCtx};`
- Replace the `aux_admitted` field and its doc with:

```rust
    /// The environment's `auxLemmasExt` state (`Meta/Tactic/AuxLemma.lean:
    /// 29-30`): every admitted `_proof_N`'s type → (name, levelParams), in
    /// admission order, so a later same-type mint overwrites (`:68`).
    /// Environment-store ids only (see `commit`).
    aux_cache: AuxLemmaCache,
```

- `new`: `aux_cache: AuxLemmaCache::new(),`
- In `elab_decl_unlabelled`: `_ => def::elab_def(&mut elab, &view, kinds, &self.aux_cache),`
- Replace `CommandElab`'s doc paragraph that starts `/// Aux lemmas: the oracle's mkAuxLemma cache` with:

```rust
/// Aux lemmas: the oracle's `mkAuxLemma` cache (`auxLemmasExt`,
/// `Meta/Tactic/AuxLemma.lean:29-30`, looked up at `:70-78`) is
/// ENVIRONMENT-wide: a later declaration whose nested proof has the type
/// (and level params) of an earlier `_proof_N` reuses that constant
/// instead of minting its own. `aux_cache` is that state; each declaration's
/// `AuxLemmas` is seeded from it.
```

- In `commit`'s `Built::Add` arm, delete the `if decls.len() > 1 && self.aux_admitted { … }` block. Replace the admission loop with:

```rust
                let n_aux = decls.len().saturating_sub(1);
                for (i, d) in decls.into_iter().enumerate() {
                    self.env
                        .add_decl_in(scratch, d)
                        .map_err(ElabError::Kernel)?;
                    if i < n_aux {
                        // `mkAuxLemma` inserts right after the aux's own
                        // `addDecl` (`AuxLemma.lean:64-68`), so an aux stays
                        // cached even if the main declaration is then
                        // rejected. Read back from the ADMITTED constant:
                        // its type and names are environment-store ids,
                        // which the next declaration's scratch store
                        // resolves to (it interns through its base).
                        let cv = self
                            .env
                            .get(names[i])
                            .ok_or_else(|| {
                                ElabError::Internal("admitted aux lemma is not in the environment".into())
                            })?
                            .constant_val();
                        self.aux_cache
                            .insert(cv.ty, (cv.name, cv.level_params.clone()));
                    }
                }
                Ok(names)
```

- Delete `aux_lemma_reuse_seam` and its doc.

Run `grep -rn "aux_admitted\|aux_lemma_reuse_seam\|auxLemmasExt) — M4c-2" crates/`. Expected: no hits.

- [ ] **Step 6: Run the gates.**

Run: `cargo test -p leanr_elab --test oracle_file --test oracle_decl 2>&1 | tail -20 && cargo test -p leanr_meta abstract 2>&1 | tail -5`
Then: `cargo test -p leanr_elab --lib aux_admitted_before_a_failed_main_is_cached`.
Expected: PASS. `oracle_file_gate` checks 15, `oracle_decl` 79, and both new pins pass.

- [ ] **Step 7: Mutations.** Run each against `cargo test -p leanr_elab --test oracle_file --test oracle_decl`, confirm FAIL, revert:
1. In `def.rs`, `AuxLemmas::with_cache(id.name, AuxLemmaCache::new())` (per-declaration cache). → `oracle_file_gate` FAILS on `aux/reuse`, `aux/overwrite`, `aux/reuseUniv` and `aux/sharedLater`; `aux_lemma_is_reused_across_declarations` FAILS.
2. Keep-first write-back: `self.aux_cache.entry(cv.ty).or_insert((cv.name, cv.level_params.clone()));`. → `oracle_file_gate` FAILS on `aux/overwrite` (`ow3` mints `ow3._proof_1`, and `ow4` reuses `ow1._proof_1`).
3. In `abstract_proofs.rs` `mk_aux_lemma`, drop `if *lps == level_params` (always return a hit). → `oracle_file_gate` FAILS on `aux/overwrite` (`ow2` hits `ow1._proof_1`).
4. Write back scratch ids. Capture `(ty, name, lps)` from `d` BEFORE `add_decl_in` (`if let Declaration::Thm(t) = &d { (t.val.ty, t.val.name, t.val.level_params.clone()) }`) and insert those instead of the read-back. → `oracle_file_gate` FAILS on `aux/reuse` (scratch ids never match the next declaration's persistent ones, or match a different node).
5. Skip the write-back entirely, deleting the `if i < n_aux { … }` block. → same failures as mutation 1, plus `aux_admitted_before_a_failed_main_is_cached`.
6. Write back only on full success: move the insert into a second loop after the admission loop. → `aux_admitted_before_a_failed_main_is_cached` FAILS (`aux_cache` is empty).

- [ ] **Step 8: Commit.**

```bash
git add crates/leanr_meta/src/abstract_proofs.rs crates/leanr_meta/src/lib.rs \
  crates/leanr_elab/src/command/def.rs crates/leanr_elab/src/command/mod.rs \
  crates/leanr_elab/tests/oracle_decl.rs crates/leanr_elab/tests/oracle_file.rs
git commit -m "M4c-2a: env-wide aux-lemma cache (auxLemmasExt) on CommandElab; full file gate (15 records)" \
  -m "<mutation outcomes 1-6 from Step 7>"
```

---

### Task 4: Seam audit, docs, spec Landed, CI

**Files:**
- Modify: `docs/superpowers/specs/2026-10-04-m4c2a-file-loop-design.md` (§ Landed)
- Modify: `docs/superpowers/specs/2026-10-03-m4c1-single-decl-design.md` (§ Landed › P2 open seams: two bullets)
- Test: the whole workspace via `mise run ci`

**Interfaces:**
- Consumes: everything above.

- [ ] **Step 1: Seam label audit.** Run: `grep -rn "M4c-2[^abc]\|M4c-2\"\|M4c-2 (" crates/leanr_elab/src crates/leanr_elab/tests`
Expected: the only hits are seams that still belong to M4c-2 as a whole: the header auto-bound seam (`M4c-2c` work) and the dotted-name seam (`M4c-2b` work). Relabel each one to its sub-slice, `— M4c-2c` for auto-bound and `— M4c-2b` for dotted, `protected` and `_root_` names. Update the tests that assert `contains("M4c-2")`: they keep passing on the substring, but tighten them to the sub-slice label. Re-run `cargo test -p leanr_elab`.

- [ ] **Step 2: Update the M4c-1 spec's open seams.** In `2026-10-03-m4c1-single-decl-design.md` § Landed › P2 › "Open seams carried forward":
- Replace the first bullet's "the env-wide `auxLemmasExt` cache (Amendment 1 item 2)" with "(the env-wide `auxLemmasExt` cache and the command loop: CLOSED in M4c-2a)".
- Append "(M4c-2a: the cache now keeps it; with the stop-at-first-error loop the re-declaration is unreachable through `elab_commands`)" to the "After a kernel rejection" bullet.

- [ ] **Step 3: Write the M4c-2a spec's § Landed.** Replace "(filled in at merge)" with:
- the commit list (`git log --oneline main..HEAD`);
- each commit's mutation outcomes, copied from the commit bodies (`git log --format=%B`);
- open seams carried forward: error recovery (`errToSorry`, continue past an error), the module header and `isPrivate`, every non-declaration command (by slice label), and the compile-error blind spot (the oracle logs code-generator errors that leanr cannot see, so a file corpus must avoid them).

- [ ] **Step 4: Run full CI, blocking.**

Run: `mise run ci 2>&1 | tail -30; echo CI_EXIT=$?`
Expected: `CI_EXIT=0`. If fmt fails, run `cargo fmt --all`, re-run, and amend the relevant commit, or make a `style:` commit.

- [ ] **Step 5: Commit.**

```bash
git add docs/superpowers/specs/ crates/
git commit -m "M4c-2a: seam sub-slice labels, docs, spec Landed"
```
