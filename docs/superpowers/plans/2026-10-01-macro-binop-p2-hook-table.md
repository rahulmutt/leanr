# Macro/binop% P2 — expansion hook, Init table, ElabOp harness Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `leanr_elab` expands Init's term notations before dispatch, the way the oracle's `elabTermAux` does. The logic notations (`∧ ∨ ¬ ↔ <->`) elaborate end to end. The 24 operator notations stop at a named `binop%`-family seam that P3 removes.

**Architecture:** `macros::expand` is pure. It looks up a node's kind in a hand-ported table of Init's `macro_rules` (`macros/init.rs`) and returns an `Expansion`. `elab_term_core` calls it first and recurses on `TermTarget::Expanded { ref, exp }`. An `App` expansion goes to the application elaborator with a pre-resolved global head (hygiene). An `Op` expansion raises `UnsupportedSyntax` named by its literal kind, the same seam a literal `binop% f a b` already hits. The differential harness is a new prelude fixture, `ElabOp`, that a script generates from the pinned toolchain's own `Init/Prelude`/`Coe`/`Notation` sources. It has its own corpus and an oracle expansion golden file, so the table is checked against real Init in both directions.

**Tech Stack:** Rust (`leanr_elab`, plus `leanr_grammar` as a new dev-dependency), Lean 4 dumpers (`lean --run`), mise tasks.

**Spec:** `docs/superpowers/specs/2026-10-01-macro-expansion-binop-design.md` § P2. Decision 3 and § Harness were amended on 2026-10-02 while writing this plan: the old "copy Init into Elab0" decision does not work in prelude mode. Read the amended sections.

## Global Constraints

- Pinned oracle `leanprover/lean4:v4.33.0-rc1`. Oracle source is at
  `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/`. Open
  every line before citing it, and print it with its real number
  (`awk 'NR>=a && NR<=b {print NR": "$0}' FILE`). Plan citations have been
  off by 1–2 lines before. The citations in this plan were opened on
  2026-10-02.
- `lean-toolchain` is not bumped. No new external dependencies. The one
  new edge is `leanr_grammar` as a **dev**-dependency of `leanr_elab`, a
  workspace crate that the tests use to assemble ElabOp's grammar.
- `crates/leanr_meta`, `crates/leanr_kernel` and `crates/leanr_syntax`
  are untouched.
- **Elab0 is frozen.** `Elab0.lean`, `Elab0.olean` and
  `elab-queries.jsonl` must not change. The Elab0 gate keeps its floor
  (345) and must stay green.
- `ElabOp.lean` is **generated**. Never hand-edit it: change
  `gen_elab_op.sh` and run `mise run fixtures:regen-elab-op`.
- CI has no Lean. Every fixture the tests read must be committed:
  `ElabOp.lean`, `ElabOp.olean`, `op-expansions.jsonl` and
  `op-queries.jsonl`.
- Run `cargo fmt --all` before every commit. CI gates on
  `cargo fmt --check` and clippy `-D warnings`.
- Build under `/workspace` only, never `/tmp` (the pod's `/tmp` is a
  20 GiB EmptyDir).
- **Mutation discipline.** Every task's "run the mutation" step is
  mandatory. Apply the mutation, watch a named test go red, revert. If
  it survives, add a test that kills it before committing. Record each
  result in the commit body. Treat any claim in this plan that a test
  kills a mutation as a hypothesis until you have run it. Earlier plans
  in this repo shipped many such claims that were false.
- **Every new corpus query must use only syntax leanr already
  supports.** All 18 queries in Task 3 were oracle-checked on
  2026-10-02. They were not run through leanr, because the hook did not
  exist yet. If one hits an unrelated pre-existing leanr gap, drop it,
  say so in the commit body, and lower the floor to match. Do not fix
  the unrelated gap in this slice.

## Review Focus

1. **Trailing input silently dropped.** `parse_term` returns a short
   term with no error when it meets an unknown token (`a ⊕⊕ b` parses
   to `<ident>` `a`). A corpus record would then test the wrong term.
   Every gate must assert the parsed term spans the whole source. (Task 1
   for golden sources; Task 3 for both corpus gates.)
2. **Notation under `@(…)` / implicit-lambda-off.** The
   `!implicit_lambda` branch strips parens and calls
   `elab_using_elab_fns` directly, which would skip the hook. Expect
   `@(True ∧ False)` to elaborate. (Task 3, the `op/explicit-paren`
   record.)
3. **A local with the same name as the expansion head.**
   `fun (And : Nat) => True ∧ False` must still mean the global `And`.
   (Task 3, the `op/hygiene` record.)
4. **Notation in an implicit-lambda position.** The expected type has a
   leading implicit binder, so the wrap runs and the expansion must
   happen inside it. Expect `g fun {α} => True ∧ False`. (Task 3, the
   `op/implicit-lambda` record.)
5. **A notation term postponed whole, then resumed.** The postponed mvar
   must store the original node and re-expand on resume. Storing an
   `Expansion` cannot be serialized. (Task 4 white-box test. No P2
   corpus path postpones a whole App expansion; see Task 4's note.)

---

## File structure

| File | Change | Responsibility |
|---|---|---|
| `tests/fixtures/elab/gen_elab_op.sh` | create | Generates `ElabOp.lean` from the toolchain's Init sources |
| `tests/fixtures/elab/ElabOp.lean` / `.olean` | create (generated) | The notation-bearing prelude fixture |
| `tests/fixtures/elab/dump_op_expansions.lean` | create | Oracle: kind / expansion kind / head / arity per notation |
| `tests/fixtures/elab/op-expansions.jsonl` | create (generated) | Golden file for the above, 31 lines |
| `tests/fixtures/elab/dump_elab.lean` | modify `main` + add `opQueries` | `lean --run dump_elab.lean ElabOp` writes the op corpus |
| `tests/fixtures/elab/op-queries.jsonl` | create (generated) | The op corpus |
| `mise.toml` | add `fixtures:regen-elab-op` | Regen task, with a diff against real Init |
| `crates/leanr_elab/Cargo.toml` | dev-dep `leanr_grammar` | Assemble ElabOp's grammar in tests |
| `crates/leanr_elab/src/macros/mod.rs` | create | `OpKind`, `Expansion`, `expand` |
| `crates/leanr_elab/src/macros/init.rs` | create | `MacroRow`, `INIT_MACROS` (29 rows), `lookup` |
| `crates/leanr_elab/src/lib.rs` | `pub mod macros;` + docs | |
| `crates/leanr_elab/src/elab.rs` | `TermTarget::Expanded`, hook, dispatch arm | |
| `crates/leanr_elab/src/app/mod.rs` | `elab_app_expanded` | Pre-resolved-head application |
| `crates/leanr_elab/src/dispatch.rs` | doc table only | Deferral table reconciliation |
| `crates/leanr_elab/tests/support/mod.rs` | `run_elab_corpus` | Shared corpus replay, with the whole-source assert |
| `crates/leanr_elab/tests/oracle_elab.rs` | call `run_elab_corpus` | |
| `crates/leanr_elab/tests/oracle_op.rs` | create | Golden, table, expand, gate and seam tests over ElabOp |

---

### Task 1: ElabOp fixture, expansion golden, regen task, parse guard

**Files:**
- Create: `tests/fixtures/elab/gen_elab_op.sh`, `tests/fixtures/elab/dump_op_expansions.lean`
- Create (generated): `tests/fixtures/elab/ElabOp.lean`, `ElabOp.olean`, `op-expansions.jsonl`
- Modify: `mise.toml` (new task after `fixtures:regen-elab`, ~line 229; `fixtures:regen`'s `depends_post`, ~line 212)
- Modify: `crates/leanr_elab/Cargo.toml`
- Create: `crates/leanr_elab/tests/oracle_op.rs`

**Interfaces:**
- Produces: `op-expansions.jsonl` lines
  `{"arity":N,"exp":"<expansion kind>","f":"<pre-resolved head>","kind":"<notation kind>","src":"<source>"}`
  (31 lines: 29 parsed samples, plus 2 forced-kind lines for `«term_>=_»`/`«term_<=_»`).
- Produces, in `tests/oracle_op.rs`: `fn elab_op_grammar() -> leanr_syntax::grammar::GrammarSnapshot`,
  `fn golden() -> Vec<serde_json::Value>`,
  `fn parse_whole(src: &str, snap: &GrammarSnapshot) -> (leanr_syntax::ParseResult, SynElem)`,
  and `const KNOWN_PARSE_DIVERGENCES: &[(&str, &str)]`.

- [ ] **Step 1: Write the generator.** `tests/fixtures/elab/gen_elab_op.sh` (`chmod +x`):

```sh
#!/bin/sh
# Generates ElabOp.lean (stdout) from the pinned toolchain's own Init
# sources: macro/binop% design spec § Harness (amended 2026-10-02).
# Whole files, verbatim except: `module`/`prelude`/`import` lines are
# removed and the `public`/`meta` modifiers dropped (module-system
# syntax a plain prelude file cannot carry). Run from the repo so elan
# resolves the pinned toolchain: `mise run fixtures:regen-elab-op`.
set -eu
SRC="$(lean --print-prefix)/src/lean"
strip() {
  sed -E \
    -e '/^module$/d' \
    -e '/^prelude( |$)/d' \
    -e '/^(public )?(meta )?import /d' \
    -e 's/^public (meta )?section/section/' \
    -e 's/^@\[expose\] (public )?section/section/' \
    -e 's/^(public meta|public|meta) (def|abbrev|instance|theorem|structure|class|inductive|opaque|axiom|macro|syntax|@\[|noncomputable|unsafe|partial|protected|private|set_option)/\2/' \
    "$1"
}
echo "-- GENERATED by gen_elab_op.sh from the pinned toolchain's Init sources."
echo "-- Do not edit: run \`mise run fixtures:regen-elab-op\`."
echo "prelude"
for f in Init/Prelude.lean Init/Coe.lean Init/Notation.lean; do
  echo "-- ===== $f ====="
  strip "$SRC/$f"
done
# Init/Notation.lean:592 opens `namespace Lean` and never closes it; without
# this the Core excerpts below land in `Lean` (kind `Lean.«term_↔_»`).
echo "end Lean"
echo "-- ===== Init/Core.lean excerpts: Iff (:188-197), bne (:772-777), Ne (:875-880) ====="
for r in 188,197 772,777 875,880; do
  sed -n "${r}p" "$SRC/Init/Core.lean"
done
```

Before trusting the excerpt ranges, print them:
`awk 'NR>=188&&NR<=197||NR>=772&&NR<=777||NR>=875&&NR<=880{print NR": "$0}' ~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/Init/Core.lean`.
You should see `structure Iff` through `infix:20 " ↔ "   => Iff`, then
`def bne` through `macro_rules | \`($x != $y) …`, then `def Ne` through
`macro_rules | \`($x ≠ $y) …`.

- [ ] **Step 2: Write the expansion dumper.** `tests/fixtures/elab/dump_op_expansions.lean`. This file was run on 2026-10-02 and its output diffed clean against real `Init`:

```lean
/-
Oracle golden file for leanr_elab's hand-ported Init macro table
(macro/binop% design spec § Harness). For each notation sample: the
parsed kind, the kind of its `expandMacroImpl?` result
(`Lean/Elab/Util.lean:157-167`), the head identifier's pre-resolved
global and the arity.

`lean --run dump_op_expansions.lean <Module>` (LEAN_PATH = this dir).
The regen task runs it against `ElabOp` (the committed golden) and
against the real `Init`, and diffs the two: this is the guard that
ElabOp's copy has not drifted from Init.
-/
import Lean
open Lean Lean.Elab

/-- `(src, forced kind)`: `src` parsed, then its root re-kinded.
`(priority := low)` puts `«term_>=_»`/`«term_<=_»` behind their unicode
twins (`Init/Notation.lean:370-377`), so no source text parses to them;
their `macro_rules` (`:372-373`) still exist. -/
def forced : List (String × Name) :=
  [ ("a >= b", `«term_>=_»), ("a <= b", `«term_<=_») ]

def samples : List String :=
  [ "a ||| b", "a ^^^ b", "a &&& b", "a + b", "a - b", "a * b", "a / b", "a % b"
  , "a ^ b", "a ++ b", "- a", "a • b"
  , "a >= b", "a <= b", "a ≤ b", "a < b", "a > b", "a ≥ b", "a = b", "a == b"
  , "a <|> b", "a >> b", "a != b", "a ≠ b"
  , "a ∧ b", "a ∨ b", "¬ a", "a ↔ b", "a <-> b" ]

/-- The global a hygienic head identifier was pre-resolved to by the quotation. -/
def preresolved : Syntax → Option Name
  | .ident _ _ _ pre => pre.findSome? fun | .decl n _ => some n | _ => none
  | _ => none

/-- `(kind, expansionKind, f, arity)` for `src` parsed and macro-expanded in `env`. -/
def expandIn (env : Environment) (src : String) (kind? : Option Name := none) :
    MetaM (Option (String × String × String × Nat)) := do
  match Parser.runParserCategory env `term src with
  | .error _ => return none
  | .ok stx =>
    let stx := match kind? with | some k => stx.setKind k | none => stx
    let r : Option (Name × Except Macro.Exception Syntax) ←
      withEnv env <| Term.TermElabM.run' <| liftMacroM <| expandMacroImpl? env stx
    match r with
    | some (_, .ok new) =>
      -- `binop% f a b` / `unop% f a`: the head is child 1. `f a b` (an `app`): child 0.
      let (head, arity) :=
        if new.getKind == ``Lean.Parser.Term.app then (new[0], new[1].getNumArgs)
        else (new[1], new.getNumArgs - 2)
      return some (stx.getKind.toString, new.getKind.toString, (preresolved head).getD .anonymous |>.toString, arity)
    | _ => return none

unsafe def main (args : List String) : IO Unit := do
  let [mod] := args | throw <| IO.userError "usage: dump_op_expansions.lean <Module>"
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← importModules #[{ module := mod.toName }] {} (trustLevel := 0) (loadExts := true)
  let ctx : Core.Context := { fileName := "<dump_op_expansions>", fileMap := default }
  let go : MetaM Unit := do
    for (src, kind?) in samples.map (·, none) ++ forced.map fun (s, k) => (s, some k) do
      let some (kind, exp, f, arity) ← expandIn env src kind? | throwError "no expansion for {src} in {mod}"
      IO.println <| Json.compress <| Json.mkObj
        [("src", src), ("kind", kind), ("exp", exp), ("f", f), ("arity", arity)]
  discard <| go.toIO ctx { env }
```

(Importing `Init` and `ElabOp` in one process fails with
"`enableInitializersExecution` must be run before…" on the second
import. That is why the cross-check is two runs and a `diff`.)

- [ ] **Step 3: Add the regen task** to `mise.toml`, directly after the `fixtures:regen-elab` block:

```toml
[tasks."fixtures:regen-elab-op"]
description = "Regenerate the macro/binop% ElabOp fixture (gen_elab_op.sh from the pinned toolchain's Init sources), its expansion golden file (diffed against the real Init), and its corpus. Needs the elan toolchain; never runs in CI."
depends = ["elan:bootstrap"]
run = [
  "sh -c 'cd tests/fixtures/elab && ./gen_elab_op.sh > ElabOp.lean && lean ElabOp.lean -o ElabOp.olean'",
  "sh -c 'cd tests/fixtures/elab && LEAN_PATH=$PWD lean --run dump_op_expansions.lean ElabOp > op-expansions.jsonl'",
  # The drift guard: ElabOp's copy must expand exactly as the real Init does.
  "sh -c 'cd tests/fixtures/elab && LEAN_PATH=$PWD lean --run dump_op_expansions.lean Init | diff op-expansions.jsonl -'",
]
```

Add `"fixtures:regen-elab-op"` to `fixtures:regen`'s `depends_post`
list (currently `["fixtures:regen-notation", "fixtures:regen-elab"]`).

- [ ] **Step 4: Run it.**

Run: `mise run fixtures:regen-elab-op`
Expected: exit 0, and `lean ElabOp.lean` prints warnings only (missing
docs, `@[expose]`), no `error`. Then:
`wc -l tests/fixtures/elab/op-expansions.jsonl` → `31`;
`grep -c '"exp":"Lean.Parser.Term.app"' tests/fixtures/elab/op-expansions.jsonl` → `5`;
`grep '"kind":"«term_↔_»"' tests/fixtures/elab/op-expansions.jsonl` → one
line with `"f":"Iff"` (if it reads `Lean.«term_↔_»`, the `end Lean` line is
missing). `ls -la tests/fixtures/elab/ElabOp.olean` → ~7.8 MB.

- [ ] **Step 5: Add the dev-dependency.** In `crates/leanr_elab/Cargo.toml` under `[dev-dependencies]`:

```toml
# Assembles ElabOp.olean's imported grammar for tests/oracle_op.rs (M3b2a machinery).
leanr_grammar = { path = "../leanr_grammar" }
```

- [ ] **Step 6: Write the parse guard test.** Create `crates/leanr_elab/tests/oracle_op.rs`:

```rust
//! macro/binop% P2: the ElabOp fixture (prelude copy of the real Init
//! notations, `tests/fixtures/elab/gen_elab_op.sh`) and the oracle's
//! expansion golden file `op-expansions.jsonl` (`dump_op_expansions.lean`).
//! See the design spec § Harness (amended 2026-10-02).

mod support;

use std::sync::Arc;

use leanr_elab::dispatch::SynElem;
use leanr_kernel::bank::Store;
use leanr_olean::ModuleData;
use leanr_syntax::grammar::GrammarSnapshot;
use leanr_syntax::{parse_term, ParseResult};

/// leanr's parser picks a different kind than the oracle for these
/// sources. `(priority := low)` on `>=`/`<=` (`Init/Notation.lean:370-371`)
/// should put them behind `≥`/`≤`; leanr_syntax picks the low-priority
/// alternative. Both rows of each pair expand to the same head
/// (`:372-373` vs `:389`, `:392`), so elaboration cannot observe it. A
/// leanr_syntax follow-up. Pinned here so a fix shows up as a failure
/// to update, not silently.
const KNOWN_PARSE_DIVERGENCES: &[(&str, &str)] =
    &[("a >= b", "«term_>=_»"), ("a <= b", "«term_<=_»")];

fn elab_op_grammar() -> GrammarSnapshot {
    let bytes = std::fs::read(support::fixture_in("elab", "ElabOp.olean")).expect("committed ElabOp.olean");
    let mut st = Store::persistent();
    let md = ModuleData::parse(&bytes, &mut st).expect("decode ElabOp.olean");
    assert!(md.imports.is_empty(), "ElabOp must stay import-free");
    let name = Arc::new(leanr_kernel::Name::Anonymous); // display-only
    leanr_grammar::assemble(&[(name, md)], &st).snapshot
}

fn golden() -> Vec<serde_json::Value> {
    std::fs::read_to_string(support::fixture_in("elab", "op-expansions.jsonl"))
        .expect("committed op-expansions.jsonl")
        .lines()
        .filter(|l| !l.trim().is_empty())
        .map(|l| serde_json::from_str(l).expect("valid JSONL"))
        .collect()
}

/// Parse `src` as a term and insist the term spans ALL of it:
/// `parse_term` stops silently at an unknown token (`a ⊕⊕ b` is
/// `<ident>` with no error), which would test the wrong term.
fn parse_whole(src: &str, snap: &GrammarSnapshot) -> (ParseResult, SynElem) {
    let parsed = parse_term(src, snap);
    assert!(parsed.errors.is_empty(), "{src:?}: parse errors {:?}", parsed.errors);
    let elem = parsed
        .tree
        .root()
        .first_child_or_token()
        .unwrap_or_else(|| panic!("{src:?}: no term child"));
    let range = elem.text_range();
    assert_eq!(
        (usize::from(range.start()), usize::from(range.end())),
        (0, src.trim_end().len()),
        "{src:?}: the parsed term does not span the whole source"
    );
    (parsed, elem)
}

/// Every golden source parses whole under ElabOp's grammar, to the
/// oracle's kind or to a pinned known divergence.
#[test]
fn golden_sources_parse_to_the_oracle_kind() {
    let snap = elab_op_grammar();
    let golden = golden();
    assert_eq!(golden.len(), 31, "op-expansions.jsonl: 29 samples + 2 forced kinds");
    for g in &golden {
        let src = g["src"].as_str().unwrap();
        let want = g["kind"].as_str().unwrap();
        let (parsed, elem) = parse_whole(src, &snap);
        let got = parsed.tree.kinds.name(elem.kind());
        if got != want {
            assert!(
                KNOWN_PARSE_DIVERGENCES.contains(&(src, got)),
                "{src:?}: leanr kind {got:?}, oracle {want:?}"
            );
        }
    }
}
```

`(0, src.trim_end().len())` measures bytes, and `text_range` is in
bytes, so `≥` counts 3. (`ParseResult` is re-exported at
`leanr_syntax`'s root, `lib.rs:32-35`.)

- [ ] **Step 7: Run the test.**

Run: `cargo test -p leanr_elab --test oracle_op -- --nocapture`
Expected: PASS. The forced lines (`src` `a >= b` with kind `«term_>=_»`)
match directly. The sample lines (`a >= b` with kind `«term_≥_»`) pass
through `KNOWN_PARSE_DIVERGENCES`.

- [ ] **Step 8: Mutations.** For each, apply it, watch the test fail, revert.
  (a) In `parse_whole`, drop the span assertion and change one golden
  `src` in a scratch copy to `a ⊕⊕ b`. The test passes without the
  assertion and fails with it. This proves the assertion is what catches
  truncation.
  (b) Delete the `end Lean` line from `gen_elab_op.sh` and rerun
  Steps 4 and 7. The regen's own diff stays clean (both sides go
  through the same parser), but the golden `kind` for `↔` becomes
  `Lean.«term_↔_»`, and Step 4's grep catches it. Record this: the kind
  guard for this failure is the Step 4 check plus Task 2's table test,
  not this test. Restore the line and regenerate.
  (c) Empty `KNOWN_PARSE_DIVERGENCES`. Expected: FAIL on `a >= b`.

- [ ] **Step 9: Commit.**

```bash
cargo fmt --all
git add tests/fixtures/elab/gen_elab_op.sh tests/fixtures/elab/dump_op_expansions.lean \
  tests/fixtures/elab/ElabOp.lean tests/fixtures/elab/ElabOp.olean tests/fixtures/elab/op-expansions.jsonl \
  mise.toml crates/leanr_elab/Cargo.toml Cargo.lock crates/leanr_elab/tests/oracle_op.rs
git commit -m "fixtures: ElabOp (generated from real Init) + oracle expansion golden (macro/binop% P2 T1)"
```

---

### Task 2: the `macros` module — table, `expand`, golden bijection

**Files:**
- Create: `crates/leanr_elab/src/macros/mod.rs`, `crates/leanr_elab/src/macros/init.rs`
- Modify: `crates/leanr_elab/src/lib.rs:244-253` (add `pub mod macros;` in alphabetical position, between `error` and `postpone`)
- Test: `crates/leanr_elab/tests/oracle_op.rs`

**Interfaces:**
- Consumes: Task 1's `elab_op_grammar`, `golden`, `parse_whole`, `KNOWN_PARSE_DIVERGENCES`.
- Produces (`leanr_elab::macros`):
  - `pub enum OpKind { BinOp, BinOpLazy, BinRel, BinRelNoProp, UnOp, LeftAct, RightAct }` (derives `Debug, Clone, Copy, PartialEq, Eq`), with `pub fn syntax_kind(self) -> &'static str`
  - `pub enum Expansion { Op { kind: OpKind, f: &'static str, args: Vec<SynElem> }, App { f: &'static str, args: Vec<SynElem> } }` (derives `Debug, Clone`), with `pub fn kind_name(&self) -> &'static str`, `pub fn f(&self) -> &'static str` and `pub fn args(&self) -> &[SynElem]`
  - `pub fn expand(elem: &SynElem, kinds: &KindInterner) -> Result<Option<Expansion>, ElabError>`
  - `leanr_elab::macros::init::{Shape, Head, MacroRow, INIT_MACROS, lookup}`; `MacroRow` has `pub fn expansion_kind(&self) -> &'static str` and `pub fn arity(&self) -> usize`

- [ ] **Step 1: Write the failing tests** (append to `tests/oracle_op.rs`):

```rust
use leanr_elab::macros::{self, init};

/// The table and the oracle's golden file agree in BOTH directions: every
/// golden kind has a row with the same expansion kind, head and arity,
/// and every row's kind is in the golden file. Deleting a row, swapping
/// a head, or swapping an op kind fails here.
#[test]
fn table_matches_oracle_expansions() {
    let golden = golden();
    let mut seen = std::collections::HashSet::new();
    for g in &golden {
        let kind = g["kind"].as_str().unwrap();
        let row = init::lookup(kind).unwrap_or_else(|| panic!("table has no row for {kind}"));
        assert_eq!(row.expansion_kind(), g["exp"].as_str().unwrap(), "{kind}: expansion kind");
        assert_eq!(row.f, g["f"].as_str().unwrap(), "{kind}: head");
        assert_eq!(row.arity() as u64, g["arity"].as_u64().unwrap(), "{kind}: arity");
        seen.insert(kind.to_string());
    }
    for row in init::INIT_MACROS {
        assert!(seen.contains(row.kind), "row {} has no oracle golden line", row.kind);
    }
    assert_eq!(init::INIT_MACROS.len(), 29);
}

/// `expand` over real ElabOp parse trees: operands in source order,
/// taken from the notation node's own children.
#[test]
fn expand_reads_operands_in_order() {
    let snap = elab_op_grammar();
    for g in &golden() {
        let src = g["src"].as_str().unwrap();
        let (parsed, elem) = parse_whole(src, &snap);
        let exp = macros::expand(&elem, &parsed.tree.kinds)
            .unwrap_or_else(|e| panic!("{src}: {e:?}"))
            .unwrap_or_else(|| panic!("{src}: no expansion"));
        assert_eq!(exp.kind_name(), g["exp"].as_str().unwrap(), "{src}");
        assert_eq!(exp.f(), g["f"].as_str().unwrap(), "{src}");
        let texts: Vec<String> = exp.args().iter().map(|a| a.to_string()).collect();
        let want: Vec<&str> = if g["arity"] == 1 { vec!["a"] } else { vec!["a", "b"] };
        assert_eq!(texts.iter().map(|s| s.trim()).collect::<Vec<_>>(), want, "{src}: operands");
    }
}

/// A kind with no row is not expanded: `elab_term_core` must elaborate
/// it as is.
#[test]
fn non_table_kinds_do_not_expand() {
    let snap = elab_op_grammar();
    for src in ["fun x => x", "binop% HAdd.hAdd a b", "(a)"] {
        let (parsed, elem) = parse_whole(src, &snap);
        assert!(macros::expand(&elem, &parsed.tree.kinds).unwrap().is_none(), "{src}");
    }
}
```

`SynElem`'s `to_string()` is rowan's `Display`, the source text including
trivia, hence the `trim()`. If `NodeOrToken` has no `Display` impl, use
`match a { NodeOrToken::Node(n) => n.text().to_string(), NodeOrToken::Token(t) => t.text().to_string() }`.

- [ ] **Step 2: Run to verify failure.**

Run: `cargo test -p leanr_elab --test oracle_op`
Expected: compile error, `could not find macros in leanr_elab`.

- [ ] **Step 3: Write `crates/leanr_elab/src/macros/init.rs`:**

```rust
//! The hand-ported Init macro table (macro/binop% design spec § The
//! table). leanr has no VM, so Init's compiled `macro_rules` cannot run;
//! each row reproduces one. Where a kind has two macros (the
//! `infixl`-generated `f a b` and a later `macro_rules`), the row is the
//! one `expandMacroImpl?` (`Lean/Elab/Util.lean:157-167`) picks: the most
//! recently declared, which is the first entry `getEntries` returns.
//!
//! `tests/oracle_op.rs`'s `table_matches_oracle_expansions` holds this
//! table to the oracle's `op-expansions.jsonl` in both directions, and the
//! regen task diffs that file against the real Init. Kind names are the
//! oracle's `Name.toString` spelling, which is also `KindInterner`'s.

use super::OpKind;

/// Where the operands sit among the notation node's non-trivia children.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Shape {
    /// `lhs op rhs`: children `[lhs, atom, rhs]`.
    Infix,
    /// `op x`: children `[atom, x]`.
    Prefix,
}

/// What the expansion's head is applied through.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Head {
    /// `binop% f a b` and the rest of the family.
    Op(OpKind),
    /// A plain application `f a b`.
    App,
}

#[derive(Debug)]
pub struct MacroRow {
    pub kind: &'static str,
    pub shape: Shape,
    pub head: Head,
    /// The global the quotation's hygienic identifier pre-resolves to.
    pub f: &'static str,
}

impl MacroRow {
    pub fn expansion_kind(&self) -> &'static str {
        match self.head {
            Head::Op(k) => k.syntax_kind(),
            Head::App => "Lean.Parser.Term.app",
        }
    }

    pub fn arity(&self) -> usize {
        match self.shape {
            Shape::Infix => 2,
            Shape::Prefix => 1,
        }
    }
}

const fn op(kind: &'static str, k: OpKind, f: &'static str) -> MacroRow {
    MacroRow { kind, shape: Shape::Infix, head: Head::Op(k), f }
}

const fn app(kind: &'static str, shape: Shape, f: &'static str) -> MacroRow {
    MacroRow { kind, shape, head: Head::App, f }
}

/// One row per kind. Citations are `Init/Notation.lean` unless noted.
pub static INIT_MACROS: &[MacroRow] = &[
    op("«term_|||_»", OpKind::BinOp, "HOr.hOr"), // :302
    op("«term_^^^_»", OpKind::BinOp, "HXor.hXor"), // :303
    op("«term_&&&_»", OpKind::BinOp, "HAnd.hAnd"), // :304
    op("«term_+_»", OpKind::BinOp, "HAdd.hAdd"), // :305
    op("«term_-_»", OpKind::BinOp, "HSub.hSub"), // :306
    op("«term_*_»", OpKind::BinOp, "HMul.hMul"), // :307
    op("«term_/_»", OpKind::BinOp, "HDiv.hDiv"), // :308
    op("«term_%_»", OpKind::BinOp, "HMod.hMod"), // :309
    op("«term_^_»", OpKind::RightAct, "HPow.hPow"), // :311
    op("«term_++_»", OpKind::BinOp, "HAppend.hAppend"), // :312
    MacroRow { kind: "«term-_»", shape: Shape::Prefix, head: Head::Op(OpKind::UnOp), f: "Neg.neg" }, // :313
    op("«term_•_»", OpKind::LeftAct, "HSMul.hSMul"), // :347
    op("«term_>=_»", OpKind::BinRel, "GE.ge"), // :372
    op("«term_<=_»", OpKind::BinRel, "LE.le"), // :373
    op("«term_≤_»", OpKind::BinRel, "LE.le"), // :389
    op("«term_<_»", OpKind::BinRel, "LT.lt"), // :390
    op("«term_>_»", OpKind::BinRel, "GT.gt"), // :391
    op("«term_≥_»", OpKind::BinRel, "GE.ge"), // :392
    op("«term_=_»", OpKind::BinRel, "Eq"), // :393
    op("«term_==_»", OpKind::BinRelNoProp, "BEq.beq"), // :394
    op("«term_<|>_»", OpKind::BinOpLazy, "HOrElse.hOrElse"), // :436
    op("«term_>>_»", OpKind::BinOpLazy, "HAndThen.hAndThen"), // :437
    op("«term_!=_»", OpKind::BinRelNoProp, "bne"), // Init/Core.lean:777
    op("«term_≠_»", OpKind::BinRel, "Ne"), // Init/Core.lean:880
    app("«term_∧_»", Shape::Infix, "And"), // :404 (infixr, unicode `/\`)
    app("«term_∨_»", Shape::Infix, "Or"), // :405 (infixr, unicode `\/`)
    app("«term¬_»", Shape::Prefix, "Not"), // :406 (notation)
    app("«term_<->_»", Shape::Infix, "Iff"), // Init/Core.lean:196
    app("«term_↔_»", Shape::Infix, "Iff"), // Init/Core.lean:197
];

/// The row for a syntax kind, if Init declares a macro for it.
pub fn lookup(kind: &str) -> Option<&'static MacroRow> {
    INIT_MACROS.iter().find(|r| r.kind == kind)
}

#[cfg(test)]
mod tests {
    #[test]
    fn kinds_are_unique() {
        let mut kinds: Vec<&str> = super::INIT_MACROS.iter().map(|r| r.kind).collect();
        kinds.sort_unstable();
        kinds.dedup();
        assert_eq!(kinds.len(), super::INIT_MACROS.len());
    }
}
```

Before committing, print every cited line:
`awk 'NR==302||NR==303||NR==304||NR==305||NR==306||NR==307||NR==308||NR==309||NR==311||NR==312||NR==313||NR==347||NR==372||NR==373||NR==389||NR==390||NR==391||NR==392||NR==393||NR==394||NR==404||NR==405||NR==406||NR==436||NR==437{print NR": "$0}' …/Init/Notation.lean`
and `awk 'NR==196||NR==197||NR==777||NR==880{print NR": "$0}' …/Init/Core.lean`.
Each line must be the `macro_rules`/`infix`/`notation` the comment names.

- [ ] **Step 4: Write `crates/leanr_elab/src/macros/mod.rs`:**

```rust
//! Macro expansion in dispatch (macro/binop% P2; design spec § P2).
//!
//! oracle: `elabTermAux` (`Lean/Elab/Term/TermElabM.lean:1823-1856`) runs
//! `expandMacroImpl?` (`:1831`) before the implicit-lambda check and
//! before any elaborator, and recurses on the result (`:1837`). leanr
//! has no VM to run Init's compiled `macro_rules`, so [`expand`] reads
//! the hand-ported [`init::INIT_MACROS`] instead. A VM later replaces
//! the table behind the same call. Mathlib's own notations stay
//! unsupported until then (`UnsupportedSyntax`, named by their kind).
//!
//! Expansion is pure: no `Expr`, no `MetaCtx`, and the same answer for
//! the same node every time. That is what lets a postponed notation
//! store its ORIGINAL node and re-expand on resume
//! (`elab.rs`'s `TermTarget::Expanded`).

pub mod init;

use leanr_syntax::kind::KindInterner;

use crate::dispatch::{non_trivia_children, SynElem};
use crate::error::ElabError;
use init::{Head, Shape};

/// The `binop%` family (`Lean/Elab/Extra.lean:478-482`, `:564-566`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum OpKind {
    BinOp,
    BinOpLazy,
    BinRel,
    BinRelNoProp,
    UnOp,
    LeftAct,
    RightAct,
}

impl OpKind {
    /// The kind of the literal form (`binop% f a b`, …), as `leanr_syntax`
    /// registers it (`builtin/term/term_app.rs`'s `register_binop_family`).
    pub fn syntax_kind(self) -> &'static str {
        match self {
            OpKind::BinOp => "Lean.Parser.Term.binop",
            OpKind::BinOpLazy => "Lean.Parser.Term.binop_lazy",
            OpKind::BinRel => "Lean.Parser.Term.binrel",
            OpKind::BinRelNoProp => "Lean.Parser.Term.binrel_no_prop",
            OpKind::UnOp => "Lean.Parser.Term.unop",
            OpKind::LeftAct => "Lean.Parser.Term.leftact",
            OpKind::RightAct => "Lean.Parser.Term.rightact",
        }
    }
}

/// A notation's expansion. leanr cannot build nodes inside an existing
/// rowan tree, so this stands for the synthesized syntax.
///
/// `f` models the quotation's hygienic identifier: a global the
/// quotation pre-resolved, never looked up in the local context, so
/// `fun (And : Nat) => True ∧ False` still means the global `And`.
/// `args` are the notation's own operand subtrees, so error positions
/// land on real source.
#[derive(Debug, Clone)]
pub enum Expansion {
    /// `binop% f a b` and the rest of the family. Elaborated by P3; until
    /// then a named `UnsupportedSyntax` seam.
    Op {
        kind: OpKind,
        f: &'static str,
        args: Vec<SynElem>,
    },
    /// `f a b`, a plain application.
    App { f: &'static str, args: Vec<SynElem> },
}

impl Expansion {
    /// The kind the expanded syntax would carry in the oracle.
    pub fn kind_name(&self) -> &'static str {
        match self {
            Expansion::Op { kind, .. } => kind.syntax_kind(),
            Expansion::App { .. } => "Lean.Parser.Term.app",
        }
    }

    pub fn f(&self) -> &'static str {
        match self {
            Expansion::Op { f, .. } | Expansion::App { f, .. } => f,
        }
    }

    pub fn args(&self) -> &[SynElem] {
        match self {
            Expansion::Op { args, .. } | Expansion::App { args, .. } => args,
        }
    }
}

/// oracle: `expandMacroImpl?` (`Lean/Elab/Util.lean:157-167`) over the
/// table. `Ok(None)`: no row for this kind, so elaborate `elem` as is.
pub fn expand(elem: &SynElem, kinds: &KindInterner) -> Result<Option<Expansion>, ElabError> {
    let Some(row) = init::lookup(kinds.name(elem.kind())) else {
        return Ok(None);
    };
    let node = elem.as_node().ok_or_else(|| {
        ElabError::IllFormedSyntax(format!("{}: a notation that is a token, not a node", row.kind))
    })?;
    let ch = non_trivia_children(node);
    let args = match (row.shape, ch.as_slice()) {
        (Shape::Infix, [lhs, _, rhs]) => vec![lhs.clone(), rhs.clone()],
        (Shape::Prefix, [_, operand]) => vec![operand.clone()],
        _ => {
            return Err(ElabError::IllFormedSyntax(format!(
                "{}: {} children, expected {}",
                row.kind,
                ch.len(),
                row.arity() + 1
            )))
        }
    };
    Ok(Some(match row.head {
        Head::Op(kind) => Expansion::Op { kind, f: row.f, args },
        Head::App => Expansion::App { f: row.f, args },
    }))
}
```

Add `pub mod macros; // macro/binop% P2` to `lib.rs` between
`pub mod error;` and `mod postpone;`.

- [ ] **Step 5: Run the tests.**

Run: `cargo test -p leanr_elab --test oracle_op && cargo test -p leanr_elab --lib macros`
Expected: PASS, all four integration tests and `kinds_are_unique`.

- [ ] **Step 6: Mutations.** Apply each, watch the named test fail, revert.
  (a) Delete the `«term_∧_»` row → `table_matches_oracle_expansions` ("table has no row").
  (b) `HAdd.hAdd` → `HSub.hSub` on the `+` row → `table_matches_oracle_expansions` ("head").
  (c) `OpKind::RightAct` → `OpKind::BinOp` on the `^` row → same test ("expansion kind").
  (d) Add a bogus row `op("«term_+++_»", OpKind::BinOp, "HAdd.hAdd")` → "no oracle golden line".
  (e) In `expand`, `vec![rhs.clone(), lhs.clone()]` → `expand_reads_operands_in_order`.
  (f) In `expand`, `Shape::Prefix` reads `[operand, _]` → `expand_reads_operands_in_order` (the IllFormedSyntax path panics, or the operand is the atom `-`).

- [ ] **Step 7: Commit.**

```bash
cargo fmt --all
git add crates/leanr_elab/src/macros crates/leanr_elab/src/lib.rs crates/leanr_elab/tests/oracle_op.rs
git commit -m "leanr_elab: hand-ported Init macro table + pure expand (macro/binop% P2 T2)"
```

---

### Task 3: the hook, `TermTarget::Expanded`, App elaboration, ElabOp gate

**Files:**
- Modify: `crates/leanr_elab/src/elab.rs:18-61` (`TermTarget`), `:483-547` (`elab_term_core`), `:599-625` (`dispatch_target`)
- Modify: `crates/leanr_elab/src/app/mod.rs` (add `elab_app_expanded` after `elab_atom`, ~line 175)
- Modify: `crates/leanr_elab/tests/support/mod.rs`, `crates/leanr_elab/tests/oracle_elab.rs`, `crates/leanr_elab/tests/oracle_op.rs`
- Modify: `tests/fixtures/elab/dump_elab.lean` (`main`, plus a new `opQueries`), `mise.toml` (`fixtures:regen-elab-op`)
- Create (generated): `tests/fixtures/elab/op-queries.jsonl`

**Interfaces:**
- Consumes: `macros::{expand, Expansion, OpKind}` (Task 2); `elab_op_grammar` (Task 1).
- Produces: `TermTarget::Expanded { r#ref: SynElem, exp: crate::macros::Expansion }`;
  `pub(crate) fn app::elab_app_expanded(elab: &mut TermElabM, f: &str, args: &[SynElem], stx: &SynElem, kinds: &KindInterner, expected: Option<ExprId>) -> Result<ExprId, ElabError>`;
  test support `pub fn run_elab_corpus(fixture: &str, queries: &str, snap: &GrammarSnapshot) -> usize`.

- [ ] **Step 1: Share the corpus loop.** Move the body of `oracle_elab_gate`
  (`crates/leanr_elab/tests/oracle_elab.rs`, from `replay_fixture_in(…)`
  through the `failures.is_empty()` assertion) into
  `crates/leanr_elab/tests/support/mod.rs` as:

```rust
/// Replay `tests/fixtures/elab/<fixture>`, then elaborate every
/// `{id, src, exp|err}` record of `<queries>` against it, parsing with
/// `snap`. Panics listing every divergence. Returns the number of records
/// replayed, for the caller's floor.
pub fn run_elab_corpus(fixture: &str, queries: &str, snap: &leanr_syntax::grammar::GrammarSnapshot) -> usize {
    // … the moved body, with `replay_fixture_in("elab", fixture)`,
    // `fixture_in("elab", queries)`, and `parse_term(src, snap)` …
    replayed
}
```

  Keep every comment that moves with the code. In the moved body,
  directly after `term_elem` is computed, add the whole-source assertion
  (same reason and wording as Task 1's `parse_whole`):

```rust
        let range = term_elem.text_range();
        assert_eq!(
            (usize::from(range.start()), usize::from(range.end())),
            (0, src.trim_end().len()),
            "{id}: the parsed term does not span the whole source {src:?} \
             (`parse_term` stops silently at an unknown token)"
        );
```

  `oracle_elab_gate` becomes:

```rust
#[test]
fn oracle_elab_gate() {
    let replayed = support::run_elab_corpus("Elab0.olean", "elab-queries.jsonl", &builtin::snapshot());
    // FLOOR on the corpus size. (Keep the existing floor comment block and history verbatim.)
    const CORPUS_FLOOR: usize = 345;
    assert!(replayed >= CORPUS_FLOOR, /* existing message */);
}
```

Remove the imports `oracle_elab.rs` no longer uses (`encode_expr`,
`EncSt`, `Store`, `MetaCtx`, …). Clippy runs on test targets with
`-D warnings`.

Run: `cargo test -p leanr_elab --test oracle_elab`
Expected: PASS, with no behaviour change yet. **If any Elab0 record fails
the span assertion, stop and report it.** That would be an existing
record that has been testing a truncated term. Do not weaken the
assertion and do not edit Elab0.

- [ ] **Step 2: Add the op corpus to the dumper.** In
  `tests/fixtures/elab/dump_elab.lean`, add before `main`:

```lean
/-- macro/binop% P2: notations whose Init expansion is a plain
application (`∧ ∨ ¬ ↔ <->`), elaborated against `ElabOp`
(`lean --run dump_elab.lean ElabOp`). The `binop%`-family rows' records
land in P3. Every query here was checked against the oracle on
2026-10-02. -/
def opQueries : List (String × String) :=
  [ ("op/and",              "True ∧ False")
  , ("op/and-ascii",        "True /\\ False")
  , ("op/or",               "True ∨ False")
  , ("op/or-ascii",         "True \\/ False")
  , ("op/not",              "¬ True")
  , ("op/iff",              "True ↔ False")
  , ("op/iff-ascii",        "True <-> False")
  -- precedence: `∧` (35) binds tighter than `∨` (30)
  , ("op/prec",             "True ∧ False ∨ True")
  , ("op/nested-paren",     "¬ (True ∧ False) ∨ True")
  , ("op/under-binder",     "fun (p q : Prop) => p ∧ q → q ∧ p")
  , ("op/iff-of-and",       "fun (p q : Prop) => p ∧ q ↔ q ∧ p")
  , ("op/not-local",        "fun (p : Prop) => ¬ p")
  -- hygiene: the expansion's `And` is the global, not the local
  , ("op/hygiene",          "fun (And : Nat) => True ∧ False")
  -- implicit-lambda position: the wrap runs, then the expansion inside it
  , ("op/implicit-lambda",  "fun (g : ({α : Type} → Prop) → Prop) => g (True ∧ False)")
  -- `@(t)`: elabTerm t (implicitLambda := false); the hook must still run
  , ("op/explicit-paren",   "@(True ∧ False)")
  -- an operand postponed (lval on an mvar-typed local) and resumed
  , ("op/postponed-operand", "(fun x => x.1 ∧ True) (PProd.mk True True)")
  , ("op/as-arg",           "And True (True ∨ False)")
  , ("op/ascribed",         "(True ∧ False : Prop)") ]
```

  Change `main` to take the module from its arguments:

```lean
unsafe def main (args : List String) : IO Unit := do
  -- `lean --run dump_elab.lean` → Elab0's corpus; `… ElabOp` → the op corpus.
  let (mod, queries, errQueries) : Name × List (String × String) × List (String × String) :=
    match args with
    | ["ElabOp"] => (`ElabOp, opQueries, [])
    | _ => (`Elab0, strQueries ++ identQueries ++ /- … the existing list, unchanged … -/ elimQueries, elimErrQueries)
```

  Then replace `` `Elab0 `` in `importModules` with `mod`, the first
  `for … in strQueries ++ … do` with `for (id, src) in queries do`, and
  `for (id, src) in elimErrQueries do` with
  `for (id, src) in errQueries do`. Add this line to `fixtures:regen-elab-op`'s `run` list in `mise.toml`:

```toml
  "sh -c 'cd tests/fixtures/elab && LEAN_PATH=$PWD lean --run dump_elab.lean ElabOp > op-queries.jsonl'",
```

Run: `mise run fixtures:regen-elab-op && mise run fixtures:regen-elab && git status --short tests/fixtures/elab`
Expected: `op-queries.jsonl` is new with 18 lines (`wc -l`), and nothing
on stderr says "elaboration failed". `elab-queries.jsonl` is **unchanged**,
which proves the default branch still emits Elab0's corpus byte for
byte. If `git status` shows `Elab0.olean` or `elab-queries.jsonl`
modified, stop and investigate.

- [ ] **Step 3: Write the failing gate** (append to `tests/oracle_op.rs`):

```rust
/// The op corpus: notations elaborated end to end against ElabOp.
#[test]
fn oracle_op_gate() {
    let replayed = support::run_elab_corpus("ElabOp.olean", "op-queries.jsonl", &elab_op_grammar());
    // Raise deliberately when records are added (`wc -l op-queries.jsonl`).
    // 0 -> 18 (macro/binop% P2 T3): the op/* App-notation records.
    const CORPUS_FLOOR: usize = 18;
    assert!(replayed >= CORPUS_FLOOR, "op corpus shrank: {replayed} < {CORPUS_FLOOR}");
}
```

Run: `cargo test -p leanr_elab --test oracle_op oracle_op_gate`
Expected: FAIL, with every record erroring
`UnsupportedSyntax("«term_∧_»")` (or the record's own notation kind).

- [ ] **Step 4: `TermTarget::Expanded`.** In `elab.rs`, extend the enum
  and its three methods. Replace the doc's last sentence ("The
  macro-expansion slice's synthesized syntax grows here.") with the
  `Expanded` description:

```rust
/// … `report.rs`'s range ordering all see what the oracle's see (design
/// spec 2026-09-30-m4b4b § The tail form). `Expanded` is a notation node
/// after macro expansion (macro/binop% P2, `macros/`): `r#ref` is the
/// notation node itself, matching the expanded syntax's
/// `SourceInfo.fromRef`, so postponement stores the ORIGINAL node and a
/// resume re-expands it (`from_parts` → `Stx` → the hook).
#[derive(Debug, Clone)]
pub(crate) enum TermTarget {
    Stx(SynElem),
    AnonCtorTail { node: SyntaxNode, from: usize },
    Expanded { r#ref: SynElem, exp: crate::macros::Expansion },
}
```

  `ref_elem`: add `TermTarget::Expanded { r#ref, .. } => r#ref.clone(),`.
  `tail_from`: change the `Stx(_) => None` arm to
  `TermTarget::Stx(_) | TermTarget::Expanded { .. } => None,`.
  `from_parts` is unchanged.

- [ ] **Step 5: The hook.** At the top of `elab_term_core`, before
  `if !implicit_lambda {`:

```rust
        // oracle: `expandMacroImpl?` runs FIRST (`TermElabM.lean:1831-1837`),
        // before `useImplicitLambda` (`:1839`), and the expansion is
        // elaborated with the SAME flags (`:1837`). Only real syntax
        // expands: an `Expansion` is never a table key, so this cannot
        // loop and needs no depth guard. The VM slice, whose macros can
        // loop, owns `withIncRecDepth` (`:1825`) here.
        if let TermTarget::Stx(elem) = target {
            if let Some(exp) = crate::macros::expand(elem, kinds)? {
                let expanded = TermTarget::Expanded {
                    r#ref: elem.clone(),
                    exp,
                };
                return self.elab_term_core(&expanded, kinds, expected, catch_ex_postpone, implicit_lambda);
            }
        }
```

  In the `!implicit_lambda` branch, the paren loop's result must go back
  through the hook. Replace the final
  `return self.elab_using_elab_fns(&TermTarget::Stx(cur), …)` with:

```rust
            // The inner term of a stripped paren goes back through the
            // hook: in the oracle `paren` is itself a macro, so its
            // expansion `t` re-enters `elabTermAux` macro step first.
            // `@(True ∧ False)` reaches here.
            if cur != *elem {
                return self.elab_term_core(&TermTarget::Stx(cur), kinds, expected, catch_ex_postpone, false);
            }
            return self.elab_using_elab_fns(&TermTarget::Stx(cur), kinds, expected, catch_ex_postpone);
```

- [ ] **Step 6: Dispatch the expansion.** In `dispatch_target`, add an arm:

```rust
            TermTarget::Expanded { r#ref, exp } => match exp {
                crate::macros::Expansion::App { f, args } => {
                    crate::app::elab_app_expanded(self, f, args, r#ref, kinds, expected)
                }
                // P3 owns the op elaborator. Until then an expansion stops
                // where a literal `binop% f a b` already does, named by the
                // literal form's kind (dispatch's catch-all).
                crate::macros::Expansion::Op { kind, .. } => {
                    Err(ElabError::UnsupportedSyntax(kind.syntax_kind().to_string()))
                }
            },
```

  Update `dispatch_target`'s doc to read: "… `elab_anon_ctor` for a flatten
  tail …, the application elaborator or the op seam for an expansion."

- [ ] **Step 7: `elab_app_expanded`.** In `app/mod.rs`, after `elab_atom`:

```rust
/// A table expansion's `f $args*` (`macros::Expansion::App`), as
/// `elabApp` sees it: `elabAppFn`'s ident arm (`App.lean:2102`) →
/// `elabAppFnId` (`:1952`). The quotation pre-resolved `f` to a global,
/// and its macro scopes keep a same-named local from capturing it, so
/// `f` goes straight to `mkConst` with fresh levels and never through
/// `resolve_local_name`: `fun (And : Nat) => True ∧ False` is the global
/// `And`. No fields, so no LVals. `stx` is the notation node, which is
/// `Context::stx` (the ambient ref).
pub(crate) fn elab_app_expanded(
    elab: &mut TermElabM,
    f: &str,
    args: &[SynElem],
    stx: &SynElem,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let name = head::intern_dotted(elab, f)?;
    if elab.view.get(name).is_none() {
        return Err(ElabError::UnknownIdent(f.to_string()));
    }
    let f = head::mk_const(elab, name, &[], f)?;
    let call = AppCall {
        named_args: Vec::new(),
        args: args.iter().cloned().map(Arg::Stx).collect(),
        expected,
        explicit: false,
        ellipsis: false,
        stx: stx.clone(),
    };
    lval::elab_app_lvals(elab, f, Vec::new(), call, kinds)
}
```

  Check the cited lines first:
  `awk 'NR==1952||NR==2102{print NR": "$0}' …/Lean/Elab/App.lean` should
  show `private def elabAppFnId` and the `elabAppFnId id [] lvals …` call.
  Import `lval` if `app/mod.rs` does not already (`use crate::app::lval;`
  or the full path).

- [ ] **Step 8: Run everything.**

Run: `cargo build -p leanr_elab 2>&1 | grep -E "^(error|warning)" ; cargo test -p leanr_elab`
Expected: the build is clean (fix any non-exhaustive `match` on
`TermTarget` the compiler names), `oracle_op_gate` PASSES with 18
records, and every existing test passes. Elab0's corpus contains no
table kind (its grammar is `builtin::snapshot()`), so nothing there
changes.

  If an `op/*` record diverges, isolate it first. Run its source through
  the oracle (`LEAN_PATH=tests/fixtures/elab lean --run …`) and through
  leanr separately. If the cause is a pre-existing leanr gap unrelated to
  expansion (the Global Constraints rule), drop the query from
  `opQueries`, regenerate, lower the floor, and say so in the commit
  body.

- [ ] **Step 9: Mutations.** Apply each, watch it fail, revert.
  (a) Delete the hook block → every `op/*` record fails `UnsupportedSyntax("«term_…»")`.
  (b) Keep the hook but drop the paren-strip recursion (always
  `elab_using_elab_fns(Stx(cur))`) → `op/explicit-paren` fails.
  (c) Move the hook into the `UseImplicitLambda::No` arm only →
  `op/implicit-lambda` fails, because the `Yes` arm dispatches the raw
  notation.
  (d) Resolve `f` lexically: in `elab_app_expanded`, first try
  `crate::resolve::resolve_local_name(&elab.mctx, &head::intern_prefixes(elab, &[f])?)`
  and use the fvar if found → `op/hygiene` fails.
  (e) Swap `args` (`.rev()`) in `elab_app_expanded` → `op/under-binder`
  and `op/as-arg` fail.
  (f) Pass `Expanded`'s expansion syntax instead of the original ref to
  `use_implicit_lambda`. You cannot write this: an `Expansion` is not a
  `SynElem`. Record that it is not expressible. `blockImplicitLambda` and
  `isLocalIdent?` are both false on every table node and on every
  expansion (an `app` with an ident head, or a `binop%`-family node), so
  the two refs agree for all 29 rows.
  (g) Remove the span assertion from `run_elab_corpus`, then append a
  junk record `{"id":"zz","src":"True ⊕⊕ False","exp":…op/and's exp…}`
  to a scratch copy of `op-queries.jsonl` → it passes without the
  assertion and fails with it. Do not commit the scratch line.

- [ ] **Step 10: Commit.**

```bash
cargo fmt --all
git add crates/leanr_elab tests/fixtures/elab/dump_elab.lean tests/fixtures/elab/op-queries.jsonl mise.toml
git commit -m "leanr_elab: macro expansion hook + App notations end to end (macro/binop% P2 T3)"
```

---

### Task 4: seams, postponement, literal `binop%`, docs, spec § Landed

**Files:**
- Test: `crates/leanr_elab/tests/oracle_op.rs`; `crates/leanr_elab/src/elab.rs` (`#[cfg(test)]` module, new or existing)
- Modify: `crates/leanr_elab/src/dispatch.rs:178-182` (deferral table), `crates/leanr_elab/src/lib.rs:132-139` (crate doc)
- Modify: `docs/superpowers/specs/2026-10-01-macro-expansion-binop-design.md` (§ Landed › P2)

**Interfaces:**
- Consumes: everything above. Produces nothing new.

- [ ] **Step 1: The op seam test** (append to `tests/oracle_op.rs`). It replays ElabOp, so give it its own harness, built the same way `run_elab_corpus` builds one record's `TermElabM`. Extract that construction in `support/mod.rs` as
  `pub fn elab_src_in(r: &Replayed, src: &str, snap: &GrammarSnapshot) -> Result<(), leanr_elab::ElabError>`
  (parse with `parse_term`, assert no errors, then `elab_term_and_synthesize(…, None)` and discard the result), and make `run_elab_corpus` use it if that stays readable. Then:

```rust
/// Until P3, every op-family notation, and the literal form, stops at a
/// seam named by the LITERAL kind.
#[test]
fn op_notations_stop_at_the_literal_kind_seam() {
    let r = support::replay_fixture_in("elab", "ElabOp.olean");
    let snap = elab_op_grammar();
    let mut cases: Vec<(String, String)> = golden()
        .iter()
        .filter(|g| g["exp"] != "Lean.Parser.Term.app")
        .map(|g| {
            (
                format!("fun (a b : Nat) => {}", g["src"].as_str().unwrap()),
                g["exp"].as_str().unwrap().to_string(),
            )
        })
        .collect();
    cases.push(("fun (a b : Nat) => binop% HAdd.hAdd a b".into(), "Lean.Parser.Term.binop".into()));
    cases.push(("fun (a : Nat) => unop% Neg.neg a".into(), "Lean.Parser.Term.unop".into()));
    for (src, kind) in cases {
        match support::elab_src_in(&r, &src, &snap) {
            Err(leanr_elab::ElabError::UnsupportedSyntax(m)) => assert_eq!(m, kind, "{src}"),
            other => panic!("{src}: expected UnsupportedSyntax({kind}), got {other:?}"),
        }
    }
}

/// The App rows elaborate end to end on Prop operands (the corpus pins
/// the terms; this pins that every App row reaches the elaborator).
#[test]
fn app_notations_elaborate() {
    let r = support::replay_fixture_in("elab", "ElabOp.olean");
    let snap = elab_op_grammar();
    for g in golden().iter().filter(|g| g["exp"] == "Lean.Parser.Term.app") {
        let src = format!("fun (a b : Prop) => {}", g["src"].as_str().unwrap());
        support::elab_src_in(&r, &src, &snap).unwrap_or_else(|e| panic!("{src}: {e:?}"));
    }
}
```

Run: `cargo test -p leanr_elab --test oracle_op`
Expected: PASS. Mutations: (a) in `dispatch_target`'s Op arm, use
`"binop%".to_string()` → `op_notations_…` fails. (b) Map `OpKind::BinRel`'s
`syntax_kind` to `"Lean.Parser.Term.binop"` → it fails on `=`. Then
both fail, because the literal row and the golden row disagree.

- [ ] **Step 2: Postponement white-box test** (`elab.rs`, in a
  `#[cfg(test)] mod tests` at the end of the file; create one if there is none).

  No P2 corpus path postpones a whole App expansion. `elabAppArgs`
  postpones only when the head's type is an mvar
  (`tryPostponeIfMVar fType`, `App.lean:1366-1367`), and `And`/`Or`/
  `Not`/`Iff` have known types. Operands postpone at the argument
  level, on real syntax (`op/postponed-operand`). This test pins the
  contract that postponement relies on:

```rust
    /// A postponed `Expanded` target stores its ORIGINAL node and no tail,
    /// so the resume rebuilds `Stx(node)` and goes back through the hook
    /// (`synthetic/ladder.rs`'s `from_parts`). An `Expansion` itself is
    /// never stored: `SyntheticMVarKind::Postponed` has no field for one.
    #[test]
    fn expanded_target_postpones_as_its_original_node() {
        let snap = leanr_syntax::builtin::snapshot();
        let parsed = leanr_syntax::parse_term("Nat.succ Nat.zero", &snap);
        let node = parsed.tree.root().first_child_or_token().unwrap();
        let target = TermTarget::Expanded {
            r#ref: node.clone(),
            exp: crate::macros::Expansion::App { f: "And", args: Vec::new() },
        };
        assert_eq!(target.ref_elem(), node);
        assert_eq!(target.tail_from(), None);
        match TermTarget::from_parts(&target.ref_elem(), target.tail_from()).unwrap() {
            TermTarget::Stx(e) => assert_eq!(e, node),
            other => panic!("resume must rebuild real syntax, got {other:?}"),
        }
    }
```

  (Any node serves as the ref. The test is about the target's
  bookkeeping, not about what `ref` is.)

Run: `cargo test -p leanr_elab --lib expanded_target_postpones`
Expected: PASS. Mutations: (a) make `tail_from` return `Some(0)` for
`Expanded` → it fails. (b) make `ref_elem` return the first arg (with a
one-arg `args`) → it fails. Record in the commit body that "store the
expanded target instead of the original on postpone" cannot be written,
because the postponed record has no field for an `Expansion`.

- [ ] **Step 3: Reconcile the docs.** In `dispatch.rs`'s deferral table, replace:

```text
///   binop% ..................................... the macro-expansion slice
///   macro expansion in dispatch ................ first macro-form slice
```

with:

```text
///   binop% family (literal and expanded) ....... macro/binop% P3 — named by the literal kind
///   macro expansion in dispatch ................ P2 SHIPPED (macro/binop%) — macros/, elab.rs
///   Mathlib (non-Init) notations ............... the VM slice — UnsupportedSyntax(kind)
```

  In `lib.rs`'s crate doc, rewrite the `binop%` sentence (`:133`) to
  "`binop%` and its family — macro/binop% P3." Rewrite the
  `**macro expansion**` bullet (`:136-139`) to say that `elab_term_core`
  expands Init notations through the hand-ported table (`macros/`)
  before dispatch, as `elabTermAux` does, and that other macro forms
  stay `UnsupportedSyntax` until the VM slice.

Run: `cargo test -p leanr_elab --test seam_audit`
Expected: PASS. If a text-scan gate trips on the new wording, adjust
the wording, not the gate.

- [ ] **Step 4: Spec § Landed › P2.** Append to the spec, after § Landed › P1:

```markdown
### P2 (PR #NN): expansion hook, Init table, ElabOp harness

Commits: <T1 sha> (ElabOp + golden), <T2 sha> (table + expand), <T3 sha>
(hook + App + gate), <T4 sha> (seams, postponement, docs).

Mutations run: <paste each task's list with killed/survived>.

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
- P3: the op elaborator, plus corpus records for the 24 op rows.
```

- [ ] **Step 5: Full CI locally.**

Run: `mise run ci 2>&1 | tail -30; echo CI_EXIT=$?`
Expected: `CI_EXIT=0`. Block on it in-turn. Do not background it.

- [ ] **Step 6: Commit.**

```bash
cargo fmt --all
git add -A crates/leanr_elab docs/superpowers/specs/2026-10-01-macro-expansion-binop-design.md
git commit -m "leanr_elab: op seam + postponement contract tests, docs, spec Landed (macro/binop% P2 T4)"
```
