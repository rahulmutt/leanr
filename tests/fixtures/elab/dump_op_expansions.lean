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
