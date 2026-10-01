/- M4b-4c P1: per-constant oracle answers for the `shouldElabAsElim`
predicates (`App.lean:1322-1328`, `AuxRecursor.lean:31-51`) and for
`getElabElimInfo` (`App.lean:1006-1053`), over EVERY constant of `Elab0`.
`info` is `{"err": …}` with the message's FIRST line when the oracle
throws (most constants are not eliminators: "unexpected eliminator
resulting type"). Run with LEAN_PATH set to this directory (see
`fixtures:regen-elab`). Consumers: crates/leanr_meta/tests/
aux_recursor_oracle.rs (predicates), crates/leanr_elab/tests/
elim_info_oracle.rs (`rec`, `info`). -/
import Lean
open Lean Lean.Meta Lean.Elab.Term

def nameStr (n : Name) : String := n.toString (escape := false)

unsafe def main : IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Elab0 }] {} (trustLevel := 0) (loadExts := true)
  let names := env.constants.fold (init := #[]) fun acc n _ => acc.push n
  let names := names.qsort (fun a b => nameStr a < nameStr b)
  let coreCtx : Core.Context := { fileName := "<dump_elim>", fileMap := default }
  let coreState : Core.State := { env }
  let go : MetaM Unit := do
    for n in names do
      let info ← try
          let i ← getElabElimInfo n
          pure <| Json.mkObj [("motive", i.motivePos),
            ("majors", Json.arr (i.majorsPos.map toJson))]
        catch ex =>
          let msg ← ex.toMessageData.toString
          pure <| Json.mkObj [("err", (msg.splitOn "\n").headD "")]
      let j := Json.mkObj [
        ("n", nameStr n), ("rec", isRecCore env n), ("aux", isAuxRecursor env n),
        ("casesOn", isCasesOnRecursor env n), ("recOn", isRecOnRecursor env n),
        ("brecOn", isBRecOnRecursor env n), ("tag", elabAsElim.hasTag env n),
        ("info", info)]
      IO.println j.compress
  discard <| go.toIO coreCtx coreState
