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
