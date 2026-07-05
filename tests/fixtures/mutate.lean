/-
Mutation-differential harness generator (M1b Task 15).

Runs under the pinned Lean toolchain via `lean --run`. Given a target
module and an output `.olean` path, it:

  1. Imports the target module (default `Init.Core`) at the `.private`
     level, so full definition/theorem bodies are available.
  2. Reads the target module's OWN constants in the deterministic order
     of its `.olean` `constants` array (NO randomness — the "seed" is the
     constant's position in that array, so regeneration is byte-stable).
  3. Selects the first `K = 40` safe theorems/defs (skips `unsafe`,
     `partial`, and non-def/thm constants).
  4. For each selected constant at position `i`, applies ONE structural
     mutation chosen by `i % 5`:
       (a) swap the last two args of the outermost application in the value;
       (b) crossover: replace the value with the PREVIOUS mutant's value;
       (c) bump the first `Sort u` in the type to `Sort (u+1)`;
       (d) identity wrapper: replace value `v` with `(fun x : T => x) v`
           (type-preserving — an ACCEPT-expected mutant);
       (e) replace the outermost lambda body's `#0` with a global constant
           of the binder type, if one exists.
     Mutations (a),(b),(c),(e) may be structurally inapplicable to a given
     constant (no outermost app, no previous mutant, no `Sort` in the type,
     non-lambda value / no constant of the binder type). When the chosen
     mutation is inapplicable we FALL BACK to mutation (d), so every
     selected constant yields exactly one deterministic mutant and the
     mutant count is a stable function of the target module. This is the
     documented "tuned mix" the task brief allows.
  5. Records the REAL kernel verdict via `Environment.addDeclCore env 0
     decl none (doCheck := true)` (the elaboration wrapper around the
     `lean_add_decl` kernel extern, Environment.lean:296/701) against the
     env of the module's imports. `.ok ⇒ accept`, `.error ⇒ reject`.
  6. Accumulates every mutant (accepted OR rejected) into a second env via
     `addDeclCore … (doCheck := false)` (unchecked add, Environment.lean:307/692),
     then `writeModule` writes ONE single-region `.olean` (the import env is
     non-module because `importModules` uses `level := .private`, so
     `isModule = false` and `writeModule` takes the single-file branch)
     containing ALL mutants, each renamed `mutant_<i>_<origName>`.
  7. Emits JSON Lines to stdout: a header object then one
     `{"name":…,"verdict":…}` per mutant.

Regenerate via `mise run fixtures:mutations`.
-/
import Lean

open Lean

/-- Is this a constant we mutate at the `Declaration` level: a safe def or a
theorem. (Inductive-shape mutations are covered by the Task 9/10 rejection
corpus instead — see the task brief scope note.) -/
def isMutable : ConstantInfo → Bool
  | .defnInfo v => v.safety == .safe
  | .thmInfo _  => true
  | _           => false

/-- (a) Swap the last two arguments of the outermost application in `value`.
Inapplicable (`none`) when the head is not applied to ≥ 2 arguments. -/
def mutSwapArgs (value : Expr) : Option Expr :=
  let fn   := value.getAppFn
  let args := value.getAppArgs
  if args.size ≥ 2 then
    let n := args.size
    let a := args[n-1]!
    let b := args[n-2]!
    let args := (args.set! (n-1) b).set! (n-2) a
    some (mkAppN fn args)
  else
    none

/-- (c) Bump every `Sort u` node in `type` to `Sort (u+1)`. Inapplicable
(`none`) when `type` contains no `Sort` node (the rewrite is a no-op, so the
result is structurally equal to the input). -/
def mutBumpSort (type : Expr) : Option Expr :=
  let type' := type.replace fun e =>
    match e with
    | .sort u => some (.sort (.succ u))
    | _       => none
  if type' == type then none else some type'

/-- (d) Identity wrapper: `(fun x : type => x) value`. Type-preserving, so an
ACCEPT-expected mutant. Always applicable. -/
def mutIdentity (type value : Expr) : Expr :=
  mkApp (Expr.lam `x type (Expr.bvar 0) BinderInfo.default) value

/-- (e) Replace the outermost lambda body's `#0` with a global constant whose
type is structurally the binder type. Inapplicable (`none`) when `value` is
not a lambda or no such constant is in `originals`. -/
def mutDropBinder (value : Expr) (originals : Array (Name × Expr)) : Option Expr :=
  match value with
  | .lam n dom body bi =>
    match originals.find? (fun (_, t) => t == dom) with
    | some (cname, _) =>
      -- Substitute bvar #0 (the binder) inside `body` with the constant.
      let body := body.replace fun e =>
        match e with
        | .bvar 0 => some (mkConst cname)
        | _       => none
      some (.lam n dom body bi)
    | none => none
  | _ => none

/-- Build the mutated `Declaration` (renamed) for `ci` at position `i`, given
the previous mutant's value and the pool of original (name, type) pairs. Also
returns the new value so the next `(b)` crossover can use it. -/
def mutateDecl (i : Nat) (ci : ConstantInfo) (prevValue : Option Expr)
    (originals : Array (Name × Expr)) : Option (Declaration × Expr) := do
  let newName := Name.mkSimple s!"mutant_{i}_{ci.name.toString (escape := false)}"
  let type := ci.type
  let value ← match ci with
    | .defnInfo v => some v.value
    | .thmInfo v  => some v.value
    | _           => none
  -- Choose the mutation; fall back to the identity wrapper (d) when the
  -- chosen structural mutation is inapplicable.
  let (newType, newValue) : Expr × Expr :=
    match i % 5 with
    | 0 => match mutSwapArgs value with
           | some v => (type, v)
           | none   => (type, mutIdentity type value)
    | 1 => match prevValue with
           | some v => (type, v)
           | none   => (type, mutIdentity type value)
    | 2 => match mutBumpSort type with
           | some t => (t, value)
           | none   => (type, mutIdentity type value)
    | 3 => (type, mutIdentity type value)
    | _ => match mutDropBinder value originals with
           | some v => (type, v)
           | none   => (type, mutIdentity type value)
  let decl ← match ci with
    | .defnInfo v =>
      some (Declaration.defnDecl
        { v with name := newName, type := newType, value := newValue, all := [newName] })
    | .thmInfo v =>
      some (Declaration.thmDecl
        { v with name := newName, type := newType, value := newValue, all := [newName] })
    | _ => none
  some (decl, newValue)

def jsonEscape (s : String) : String := (Json.str s).compress

def main (args : List String) : IO Unit := do
  let targetName := (args[0]?.getD "Init.Core").toName
  let outPath : System.FilePath := ⟨args[1]?.getD "tests/fixtures/Mutations.olean"⟩
  let k : Nat := ((args[2]?).bind (·.toNat?)).getD 40
  -- Search path: the toolchain (for `Init.*`) plus the fixtures dir (for the
  -- import-free hermetic base module).
  initSearchPath (← findSysroot)
  searchPathRef.modify (fun sp => (⟨"tests/fixtures"⟩ : System.FilePath) :: sp)
  let env ← importModules #[{module := targetName}] {} (trustLevel := 0)
  -- Read the target module's own constants in deterministic array order, with
  -- full bodies. Module-mode toolchain oleans split their data across
  -- `.olean{,.server,.private}` companion parts that are NOT independently
  -- decodable (they share the base part's compactor region), so we read them
  -- together and take the LAST (most private) part — exactly `LeanChecker`'s
  -- `replayFromImports` idiom. A plain/prelude module (e.g. the hermetic
  -- `MutBase`) has just the one part.
  let mFile ← findOLean targetName
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  let some (modData, _) := parts[parts.size - 1]?
    | throw (IO.userError "no module data parts")
  let ownConsts := modData.constants
  -- Pool of (name, type) for mutation (e).
  let originals : Array (Name × Expr) := ownConsts.map (fun c => (c.name, c.type))
  -- Select the first K safe defs/thms.
  let selected := (ownConsts.filter isMutable).extract 0 k
  let mut accEnv := env
  let mut prevValue : Option Expr := none
  let mut lines : Array String := #[]
  let mut nAccept := 0
  let mut nReject := 0
  for h : i in [0:selected.size] do
    let ci := selected[i]
    match mutateDecl i ci prevValue originals with
    | none => pure ()
    | some (decl, newValue) =>
      prevValue := some newValue
      let name := decl.getTopLevelNames.head!
      -- Verdict against the fixed import env.
      let verdict := match env.addDeclCore 0 decl none (doCheck := true) with
        | .ok _    => "accept"
        | .error _ => "reject"
      if verdict == "accept" then nAccept := nAccept + 1 else nReject := nReject + 1
      -- Accumulate the mutant into the emission env WITHOUT checking.
      match accEnv.addDeclCore 0 decl none (doCheck := false) with
      | .ok e    => accEnv := e
      | .error _ => pure ()  -- unchecked add cannot fail on well-formed shapes
      let nameStr := name.toString (escape := false)
      lines := lines.push s!"\{\"name\":{jsonEscape nameStr},\"verdict\":\"{verdict}\"}"
  -- Emit the header first, then the per-mutant lines.
  let header := s!"\{\"module\":{jsonEscape targetName.toString},\"githash\":{jsonEscape Lean.githash},\"count\":{lines.size},\"accepts\":{nAccept},\"rejects\":{nReject}}"
  IO.println header
  for l in lines do
    IO.println l
  -- Write the single-region olean containing all mutants (`writeModule` lives
  -- in the top-level `Lean` namespace, not `Lean.Environment`).
  writeModule accEnv outPath
  -- Keep the compacted regions alive until the end (`modData`'s objects live
  -- inside them).
  discard <| pure parts
