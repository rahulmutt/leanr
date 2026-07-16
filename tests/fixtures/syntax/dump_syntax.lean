/-
Oracle parse-tree dump (M3a spec §Oracle harness). Parse-only frontend
loop: header via parseHeader/processHeader (so imported grammar IS
honored — M3b's full-Mathlib sweep reuses this), then parseCommand in a
loop WITHOUT elaboration. M3a fixtures therefore must not rely on
same-file grammar extensions (they can't — that's the M3a/M3b line).

Canonical JSON (locked, see plan Global Constraints):
  node    {"c":[…],"k":"<kind>"}     atom  {"a":"<text>","s":[b,e]}
  ident   {"i":"<raw>","s":[b,e]}    missing {"k":"<missing>"}
Json.compress prints object keys RBMap-sorted = alphabetical, matching
leanr's canon.rs writer.

Usage: lean --run dump_syntax.lean <file.lean>   (pinned toolchain)

M3b2a Task 2 addendum: `Lean.enableInitializersExecution` MUST run
before `Parser.parseHeader`/`processHeader` (same fact documented in
`dump_syntax_elab.lean`'s module doc) or `importModules (loadExts :=
true)` throws internally and `processHeader` silently falls back to an
EMPTY environment — invisible for every prior M3a/M3b1 fixture (none
imports a LOCAL module with its own notation/parser extensions; `import
Lean` itself doesn't need loadExts to round-trip a parse-only dump), but
fatal for the M3b2a `import/` corpus: `NotaDep`'s custom notation must
actually be live in `env` for the importer fixtures' term parser to
recognize e.g. `⊕⊕`, or the parser just stops at the plain numeral and
silently drops the rest of the line into that command's trailing span
(confirmed empirically: the header parses and `import NotaDep`
succeeds syntactically either way — only the LATER environment-driven
parsing is affected, which is why this was never caught by the M3a
corpus's own oracle_golden gate).
-/
import Lean

open Lean Parser Elab

def spanJson : SourceInfo → Json
  | .original _ pos _ tailPos => Json.arr #[Json.num pos.byteIdx, Json.num tailPos.byteIdx]
  | _ => Json.null

partial def toCanon : Syntax → Json
  | .missing => Json.mkObj [("k", "<missing>")]
  | .node _ kind args =>
    Json.mkObj [("k", kind.toString), ("c", Json.arr (args.map toCanon))]
  | .atom info val =>
    Json.mkObj [("a", val), ("s", spanJson info)]
  | .ident info rawVal _ _ =>
    Json.mkObj [("i", rawVal.toString), ("s", spanJson info)]

unsafe def main (args : List String) : IO Unit := do
  let fileName := args.head!
  let input ← IO.FS.readFile fileName
  -- Must run before parseHeader/processHeader (module doc above) or
  -- `importModules (loadExts := true)` throws internally and
  -- `processHeader` silently falls back to an empty environment.
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, _messages) ← processHeader header {} messages inputCtx
  IO.println (toCanon header.raw).compress
  let pmctx : Parser.ParserModuleContext := { env, options := {} }
  let mut state := parserState
  let mut msgs : MessageLog := {}
  repeat
    let (cmd, state', msgs') := Parser.parseCommand inputCtx pmctx state msgs
    state := state'
    msgs := msgs'
    IO.println (toCanon cmd).compress
    if Parser.isTerminalCommand cmd then
      break
