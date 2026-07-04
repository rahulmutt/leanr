/-
Golden-fixture generator: prints one `<kind> <name>` line per constant
in a module's `.olean`, in `ModuleData.constants` order. leanr's
`ConstantInfo::kind()` and `Display for Name` (unescaped, dot-joined)
must match this output byte-for-byte — that is the golden contract.
Run via `mise run fixtures:regen`.
-/
import Lean

open Lean

def kindStr : ConstantInfo → String
  | .axiomInfo _  => "axiom"
  | .defnInfo _   => "def"
  | .thmInfo _    => "thm"
  | .opaqueInfo _ => "opaque"
  | .quotInfo _   => "quot"
  | .inductInfo _ => "induct"
  | .ctorInfo _   => "ctor"
  | .recInfo _    => "rec"

def main (args : List String) : IO Unit := do
  let (mod, region) ← readModuleData ⟨args.head!⟩
  for c in mod.constants do
    IO.println s!"{kindStr c} {c.name.toString (escape := false)}"
  -- Keep the region alive until after printing: `mod`'s objects live
  -- inside it.
  discard <| pure region
