/-
Oracle parse-tree dump — ELABORATING variant (M3b1 Task 8, "CRITICAL
BLOCKER" resolution in the task brief). Used ONLY for the M3b1
`Notation*.lean` fixtures; every other fixture keeps using the
parse-only `dump_syntax.lean` (unmodified, still authoritative for M3a).

WHY THIS EXISTS: `dump_syntax.lean` runs `Parser.parseCommand` in a loop
against a FIXED `env` and never elaborates — so it can never observe a
`notation`/mixfix command growing the grammar for LATER commands in the
same file (that only happens once the command is actually ELABORATED,
which registers a new parser-table entry in the environment). This file
drives the real Lean frontend (`Lean.Elab.IO.processCommands`, the same
"parse a command, elaborate it, thread the updated `env` into the next
`parseCommand`" loop `lean` itself runs) so a same-file `notation`
really is live for subsequent commands, exactly like leanr's own
`parse_module` command loop (crates/leanr_syntax/src/parse.rs) is meant
to reproduce.

TECHNIQUE (read from the M3b1 Task 3 report,
`/workspace/.superpowers/sdd/task-3-report.md`, and this crate's own
`grammar/notation.rs` module doc — both drove this exact API before):
  - `Lean.enableInitializersExecution` MUST run before
    `Parser.parseHeader`/`processHeader`, or `importModules (loadExts
    := true)` throws internally and `processHeader` silently falls back
    to an EMPTY environment (invisible unless the returned `MessageLog`
    is inspected — irrelevant to `dump_syntax.lean`, which is parse-only
    and never elaborates, but fatal here).
  - The fixtures this dumper runs on must NOT use the `prelude` header
    directive (unlike every M3a fixture): `prelude` suppresses the
    implicit `import Init`, and the notation ELABORATOR itself
    (`Lean.Elab.Notation`/`Lean.Elab.Syntax`) is ordinary Lean code that
    references library types (`Lean.TrailingParserDescr`, etc.) which
    must already be loaded for elaboration to run at all — independent
    of whether the USER's own source needs `Init`. So `Notation*.lean`
    fixtures rely on the file's implicit `import Init` (no header
    directive at all), not `prelude`.
  - `Lean.Elab.IO.processCommands` (NOT `Lean.Elab.Frontend.IO.
    processCommands` — that qualification is a common mistake, see the
    Task 3 report addendum: `Frontend.lean` opens `namespace
    Lean.Elab.Frontend`, closes it early with `end Frontend`, then
    `open Frontend` before declaring `IO.processCommands`, so the
    declaration itself lands in `Lean.Elab`, not `Lean.Elab.Frontend`)
    parses+elaborates every command in one pass and returns a
    `Frontend.State` whose `commands : Array Syntax` field holds EVERY
    parsed command's syntax tree, in source order, INCLUDING the
    trailing `eoi` — exactly the sequence `dump_syntax.lean`'s own
    manual loop prints (it pushes `cmd` unconditionally before checking
    `isTerminalCommand`, see `Lean/Elab/Frontend.lean`'s
    `Frontend.processCommand`). So printing `s.commands` post-hoc,
    in order, via the SAME `toCanon` this file copies verbatim from
    `dump_syntax.lean`, reproduces `dump_syntax.lean`'s own output
    byte-for-byte on any fixture that doesn't grow its own grammar —
    confirmed empirically in Task 8's spot-check against a committed
    M3a `.stx.jsonl` (see task-8-report.md).
  - A command's stored `Syntax` is captured AT PARSE TIME, before
    `elabCommandAtFrontend` runs on it — so an elaboration failure (a
    genuinely malformed `notation`, an unresolved identifier in the
    corpus's deliberately-nonsense RHS terms, ...) can never perturb the
    PRINTED tree for that command; it can only affect whether LATER
    commands' grammar reflects a fresh registration. `Command.
    elabCommandTopLevel` (what `elabCommandAtFrontend` calls) already
    catches ordinary elaboration exceptions and logs them as `Message`s
    rather than raising to the surrounding `IO` monad — confirmed
    empirically in the Task 3 report addendum (a `notation "a b" ...`
    that fails elaboration with "invalid atom" did not abort that
    probe's dump loop) and again by this file's own error fixture
    (`NotationBadResync.lean`, no `.stx.jsonl` — round-trip only).

Canonical JSON format: IDENTICAL to `dump_syntax.lean` — `toCanon`/
`spanJson` below are copied verbatim so dumps stay byte-comparable.

Usage: lean --run dump_syntax_elab.lean <file.lean>   (pinned toolchain)
-/
import Lean
import Lean.Elab.Frontend

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
  let commandState := Command.mkState env {} {}
  let st ← Lean.Elab.IO.processCommands inputCtx parserState commandState
  for cmd in st.commands do
    IO.println (toCanon cmd).compress
