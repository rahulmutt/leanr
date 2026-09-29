/- Dumps, for every structure declared in `Elab0`, the oracle's own
answers to the `Structure.lean` accessors leanr ports (M4b-4a P1, design
spec § Testing: "compared against values the oracle dumps ... never
hand-computed"). One JSON object per line, sorted by structure name.
Run with LEAN_PATH set to this directory (see `fixtures:regen-elab`). -/
import Lean
open Lean

def nameStr (n : Name) : String := n.toString (escape := false)

def biStr : BinderInfo → String
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

def optName : Option Name → Json
  | none => Json.null
  | some n => Json.str (nameStr n)

unsafe def main : IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Elab0 }] {} (trustLevel := 0) (loadExts := true)
  let some modIdx := env.getModuleIdx? `Elab0
    | throw (IO.userError "dump_structs: Elab0 not loaded")
  let names := env.constants.fold (init := #[]) fun acc n _ =>
    if env.getModuleIdxFor? n == some modIdx && isStructure env n then acc.push n else acc
  let names := names.qsort (fun a b => nameStr a < nameStr b)
  let coreCtx : Core.Context := { fileName := "<dump_structs>", fileMap := default }
  let coreState : Core.State := { env }
  let go : CoreM Unit := do
    for s in names do
      let some info := getStructureInfo? env s | unreachable!
      let order ← getStructureResolutionOrder s
      let paths := order.toList.map fun b =>
        Json.mkObj [("base", nameStr b),
          ("path", match getPathToBaseStructure? env b s with
            | none => Json.null
            | some p => Json.arr (p.map (Json.str ∘ nameStr)).toArray)]
      let mut seen : Array Name := #[]
      for t in order do
        for f in getStructureFields env t do
          unless seen.contains f do seen := seen.push f
      unless seen.contains `zzz do seen := seen.push `zzz
      let find := seen.toList.map fun f =>
        Json.mkObj [("f", nameStr f), ("in", optName (findField? env s f))]
      let j := Json.mkObj [
        ("s", nameStr s),
        ("fields", Json.arr (info.fieldNames.map (Json.str ∘ nameStr))),
        ("info", Json.arr (info.fieldInfo.map fun fi => Json.mkObj [
          ("f", nameStr fi.fieldName), ("proj", nameStr fi.projFn),
          ("sub", optName fi.subobject?), ("bi", biStr fi.binderInfo)])),
        ("parents", Json.arr (info.parentInfo.map fun p => Json.mkObj [
          ("s", nameStr p.structName), ("sub", p.subobject), ("proj", nameStr p.projFn)])),
        ("order", Json.arr (order.map (Json.str ∘ nameStr))),
        ("paths", Json.arr paths.toArray),
        ("find", Json.arr find.toArray)]
      IO.println j.compress
  discard <| go.toIO coreCtx coreState
