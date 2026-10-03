/- Emits the M4c-1 declaration corpus (spec
`docs/superpowers/specs/2026-10-03-m4c1-single-decl-design.md` § Harness):
for each `(id, src)`, the COMMAND `src` is parsed and elaborated with
`Lean.Elab.Command.elabCommandTopLevel` against the Elab0 environment, and
the constants it added are dumped.

Runs with LEAN_PATH set to this directory so `Elab0` resolves to the
committed fixture and nothing else (the `dump_elab.lean` hermetic contract).

`Elab.async` is set to `true`, matching the `lean` command line
(`CoreM.lean:35`): a theorem then takes `elabAsync`
(`MutualDef.lean:1266`). An async body reports its errors through
`Command.State.snapshotTasks`, NOT `messages`, so the error scan below walks
both (an async error left out reads as a silently dropped theorem).

Record shapes:
  {"id","src","consts":[C...]}   -- the command added these constants
  {"id","src","err":<string>}    -- the first error's first line
where `C` is
  {"name","kind":"defn"|"thm"|"opaque"|"axiom","levelParams":[..],
   "type":E, "value":E?, "hints":"opaque"|"abbrev"|{"regular":N}?,
   "safety":"safe"|"unsafe"|"partial"?, "unsafe":bool?, "all":[..]?}
and `E` is the canonical expr scheme of `dump_elab.lean` (copied verbatim
below). `consts` is sorted by `Name.lt`: the environment's constant map
is unordered, so the dumper cannot observe insertion order. The leanr
gate sorts its own admitted names the same way and checks the admission
order (every `_proof_N` before the main declaration) separately.

A `declQueries` command that logs an error is reported on stderr and
DROPPED (the gate's floor catches a shrinking corpus); a `declErrQueries`
command that elaborates cleanly is reported on stderr and dropped.
-/
-- NOT `import Elab0`: see `dump_elab.lean` (Elab0 is prelude-mode and
-- collides with the real `Init` this file needs).
import Lean
open Lean Lean.Meta Lean.Elab

-- ===== canonical expr/level encoder (dump_defeq.lean's scheme + lmvar) =====

/-- `default`->d, `implicit`->i, `strictImplicit`->s, `instImplicit`->c
(binder NAMES are erased everywhere; only this kind letter survives). -/
def biStr : BinderInfo → String
  | .default => "d"
  | .implicit => "i"
  | .strictImplicit => "s"
  | .instImplicit => "c"

/-- Per-query numbering state for mvars/fvars/level-mvars, first-
occurrence order. Shared across one query's whole encode call (there is
only ever ONE side per elab query — `exp` — unlike `dump_defeq.lean`'s
`in`/`out` pair, so there is no `encPair`-style threading need here;
`EncSt` is still its own structure, freshly `{}`-initialized per query,
mirroring `dump_defeq.lean`'s naming for the same role). -/
structure EncSt where
  fvars : Std.HashMap FVarId Nat := {}
  fNext : Nat := 0
  mvars : Std.HashMap MVarId Nat := {}
  mNext : Nat := 0
  lvars : Std.HashMap LMVarId Nat := {}
  lNext : Nat := 0

abbrev EncM := StateM EncSt

partial def encLevel : Level → EncM Json
  | .zero => pure <| Json.mkObj [("k", "zero")]
  | .succ u => do
    let uj ← encLevel u
    pure <| Json.mkObj [("k", "succ"), ("u", uj)]
  | .max a b => do
    let aj ← encLevel a
    let bj ← encLevel b
    pure <| Json.mkObj [("k", "max"), ("a", aj), ("b", bj)]
  | .imax a b => do
    let aj ← encLevel a
    let bj ← encLevel b
    pure <| Json.mkObj [("k", "imax"), ("a", aj), ("b", bj)]
  | .param n => pure <| Json.mkObj [("k", "param"), ("n", n.toString (escape := false))]
  | .mvar id => do
    let st ← get
    match st.lvars.get? id with
    | some n => pure <| Json.mkObj [("k", "lmvar"), ("i", n)]
    | none =>
      let n := st.lNext
      modify fun s => { s with lvars := s.lvars.insert id n, lNext := n + 1 }
      pure <| Json.mkObj [("k", "lmvar"), ("i", n)]

partial def encExpr : Expr → EncM Json
  | .bvar i => pure <| Json.mkObj [("k", "bvar"), ("i", i)]
  | .fvar id => do
    let st ← get
    match st.fvars.get? id with
    | some n => pure <| Json.mkObj [("k", "fvar"), ("i", n)]
    | none =>
      let n := st.fNext
      modify fun s => { s with fvars := s.fvars.insert id n, fNext := n + 1 }
      pure <| Json.mkObj [("k", "fvar"), ("i", n)]
  | .mvar id => do
    let st ← get
    match st.mvars.get? id with
    | some n => pure <| Json.mkObj [("k", "mvar"), ("i", n)]
    | none =>
      let n := st.mNext
      modify fun s => { s with mvars := s.mvars.insert id n, mNext := n + 1 }
      pure <| Json.mkObj [("k", "mvar"), ("i", n)]
  | .sort u => do
    let uj ← encLevel u
    pure <| Json.mkObj [("k", "sort"), ("u", uj)]
  | .const n us => do
    let usj ← us.mapM encLevel
    pure <| Json.mkObj
      [("k", "const"), ("n", n.toString (escape := false)), ("us", Json.arr usj.toArray)]
  | .app f a => do
    let fj ← encExpr f
    let aj ← encExpr a
    pure <| Json.mkObj [("k", "app"), ("f", fj), ("a", aj)]
  | .lam _ t b bi => do
    let tj ← encExpr t
    let bj ← encExpr b
    pure <| Json.mkObj [("k", "lam"), ("bi", biStr bi), ("t", tj), ("b", bj)]
  | .forallE _ t b bi => do
    let tj ← encExpr t
    let bj ← encExpr b
    pure <| Json.mkObj [("k", "pi"), ("bi", biStr bi), ("t", tj), ("b", bj)]
  | .letE _ t v b nd => do
    let tj ← encExpr t
    let vj ← encExpr v
    let bj ← encExpr b
    pure <| Json.mkObj [("k", "let"), ("t", tj), ("v", vj), ("b", bj), ("nd", nd)]
  | .lit (.natVal n) => pure <| Json.mkObj [("k", "lit"), ("n", toString n)]
  | .lit (.strVal s) => pure <| Json.mkObj [("k", "str"), ("v", s)]
  | .proj s i e => do
    let ej ← encExpr e
    pure <| Json.mkObj [("k", "proj"), ("s", s.toString (escape := false)), ("i", i), ("e", ej)]
  | .mdata _ e => encExpr e -- mdata ERASED: recurse straight through

-- ===== query corpus (Task 4: `str` slice only) =====

def hintsJ : ReducibilityHints → Json
  | .opaque => "opaque"
  | .abbrev => "abbrev"
  | .regular h => Json.mkObj [("regular", toJson h.toNat)]

def safetyStr : DefinitionSafety → String
  | .safe => "safe" | .unsafe => "unsafe" | .partial => "partial"

def nameJ (n : Name) : Json := n.toString (escape := false)

def namesJ (ns : List Name) : Json := Json.arr (ns.map nameJ).toArray

def constJ (ci : ConstantInfo) : Json :=
  let enc (e : Expr) : Json := (encExpr e).run' {}
  let base : List (String × Json) :=
    [("name", nameJ ci.name), ("levelParams", namesJ ci.levelParams), ("type", enc ci.type)]
  let kind (k : String) : String × Json := ("kind", Json.str k)
  match ci with
  | .defnInfo v => Json.mkObj (kind "defn" :: base ++
      [("value", enc v.value), ("hints", hintsJ v.hints),
       ("safety", Json.str (safetyStr v.safety)), ("all", namesJ v.all)])
  | .thmInfo v => Json.mkObj (kind "thm" :: base ++
      [("value", enc v.value), ("all", namesJ v.all)])
  | .opaqueInfo v => Json.mkObj (kind "opaque" :: base ++
      [("value", enc v.value), ("unsafe", toJson v.isUnsafe), ("all", namesJ v.all)])
  | .axiomInfo v => Json.mkObj (kind "axiom" :: base ++ [("unsafe", toJson v.isUnsafe)])
  | _ => Json.mkObj (kind "other" :: base)

-- ===== query corpus (spec § Corpus; every record probed at plan time) =====

def declQueries : List (String × String) := [
  ("kind/def", "def d1 : Nat := Nat.zero"),
  ("kind/theorem", "theorem t1 : True := True.intro"),
  ("kind/abbrev", "abbrev a1 : Nat := Nat.zero"),
  ("kind/opaque", "opaque o1 : Nat := Nat.zero"),
  ("kind/axiom", "axiom ax1 : Nat"),
  ("kind/example", "example : Nat := Nat.zero"),
  ("kind/exampleParams", "example (x : Nat) : Nat := x"),
  ("kind/propDef", "def dp : True := True.intro"),
  ("kind/abbrevProp", "abbrev abp : True := True.intro"),
  ("kind/opaqueProp", "opaque opp : True := True.intro"),
  ("type/inferred", "def inf1 := List.cons Nat.zero List.nil"),
  ("type/unify", "def uni1 : List Nat := List.nil"),
  ("type/lamValue", "def lam1 : Nat → Nat := fun x => x"),
  ("type/implicitBinder", "def ib {α : Type} (a : α) : α := a"),
  ("type/instBinder", "def ii {a : Type} [Wrap a] (x : a) : a := Wrap.wrap x"),
  ("type/optParamCleanup", "def oe (n : optParam Nat Nat.zero) : Nat := n"),
  ("type/headerMVarSolvedByBody", "def dv : Sort _ := Nat"),
  ("type/groupHoles", "def tw (α β : Sort _) (a : α) (b : β) : α := a"),
  ("univ/explicit1", "def ue1.{u} (α : Sort u) (a : α) : α := a"),
  ("univ/explicit2", "def ue2.{u, v} (α : Sort u) (β : Sort v) (a : α) (b : β) : α := a"),
  ("univ/sortHole", "def us1 (α : Sort _) (a : α) : α := a"),
  ("univ/idBody", "def ub1 := @id"),
  ("univ/order", "def uo.{v} (α : Sort _) (β : Sort v) (a : α) (b : β) : β := b"),
  ("univ/orderRev", "def uo2.{v, u} (α : Sort u) (β : Sort v) (a : α) (b : β) : β := b"),
  ("univ/skipUsedName", "def sk.{u_1} (α : Sort u_1) (β : Sort _) (b : β) : β := b"),
  ("univ/defElevenLex", "def el (a1 : Sort _) (a2 : Sort _) (a3 : Sort _) (a4 : Sort _) (a5 : Sort _) (a6 : Sort _) (a7 : Sort _) (a8 : Sort _) (a9 : Sort _) (a10 : Sort _) (a11 : Sort _) : Nat := Nat.zero"),
  ("univ/thmElevenNumeric", "theorem el2 (a1 : Sort _) (a2 : Sort _) (a3 : Sort _) (a4 : Sort _) (a5 : Sort _) (a6 : Sort _) (a7 : Sort _) (a8 : Sort _) (a9 : Sort _) (a10 : Sort _) (a11 : Sort _) : True := True.intro"),
  ("univ/propDefElevenNumeric", "def el3 (a1 : Sort _) (a2 : Sort _) (a3 : Sort _) (a4 : Sort _) (a5 : Sort _) (a6 : Sort _) (a7 : Sort _) (a8 : Sort _) (a9 : Sort _) (a10 : Sort _) (a11 : Sort _) : True := True.intro"),
  ("univ/thmSortHole", "theorem ut1 (α : Sort _) (a : α) : Eq a a := rfl"),
  ("univ/thmExplicit", "theorem te.{u} (α : Sort u) (a : α) : Eq a a := rfl"),
  ("univ/thmUserAndHole", "theorem tuh.{v} (α : Sort _) (β : Sort v) (b : β) : Eq b b := rfl"),
  ("univ/defHeaderUnivByBody", "def dx (α : Sort _) : Nat := (fun (_ : Type) => Nat.zero) α"),
  ("univ/axiomSortHole", "axiom as1 (α : Sort _) : α"),
  ("univ/axiomElevenLex", "axiom ael (a1 : Sort _) (a2 : Sort _) (a3 : Sort _) (a4 : Sort _) (a5 : Sort _) (a6 : Sort _) (a7 : Sort _) (a8 : Sort _) (a9 : Sort _) (a10 : Sort _) (a11 : Sort _) : Nat"),
  ("univ/abbrevUniv", "abbrev abu.{u} (α : Sort u) : Sort u := α"),
  ("univ/thmLevelOnlyBody", "theorem tl : True := (fun (_ : Sort 1) => True.intro) Nat"),
  ("height/pick", "def hc := pick Nat.zero Nat.zero"),
  ("height/id", "def hid := id Nat.zero"),
  ("height/overThm", "def ht := @eq_of_heq"),
  ("height/abbrev", "abbrev ab2 := pick Nat.zero"),
  ("height/explicitTy", "def dit : Nat → Nat := id"),
  ("np/one", "def np1 (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl"),
  ("np/trivial", "def np0 (n : Nat) : PProd Nat (Eq n n) := PProd.mk n rfl"),
  ("np/shared", "def np2 (n : Nat) : PProd (Eq (Nat.succ n) (Nat.succ n)) (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk rfl rfl"),
  ("np/distinct", "def np3 (n : Nat) : PProd (Eq (Nat.succ n) (Nat.succ n)) (Eq (Nat.succ (Nat.succ n)) (Nat.succ (Nat.succ n))) := PProd.mk rfl rfl"),
  ("np/binder", "def np4 : (n : Nat) → PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := fun n => PProd.mk n rfl"),
  ("np/univ", "def np5.{u} (α : Sort u) (a : α) : PProd α (Eq (id a) (id a)) := PProd.mk a rfl"),
  ("np/theorem", "theorem np6 (n : Nat) : True := (fun (_ : PProd Nat (Eq (Nat.succ n) (Nat.succ n))) => True.intro) (PProd.mk n rfl)"),
  ("np/example", "example (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl"),
  ("np/abbrev", "abbrev np7 (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl"),
  ("np/opaque", "opaque np8 (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl"),
  ("np/twoBinders", "def npb (n : Nat) (m : Nat) : PProd Nat (Eq (Nat.succ m) (Nat.succ m)) := PProd.mk n rfl"),
  ("np/lambdaArg", "def npl (n : Nat) : Nat := (fun (_ : Eq (Nat.succ n) (Nat.succ n)) => n) rfl"),
  ("np/nestedTwice", "def npn (n : Nat) : PProd Nat (PProd Nat (Eq (Nat.succ n) (Nat.succ n))) := PProd.mk n (PProd.mk n rfl)")
]

def declErrQueries : List (String × String) := [
  ("err/already", "def pick : Nat := Nat.zero"),
  ("err/thmAlready", "theorem eq_of_heq : True := True.intro"),
  ("err/univDup", "def udup.{u, u} : Nat := Nat.zero"),
  ("err/unusedUniv", "def uu.{u} : Nat := Nat.zero"),
  ("err/unusedUniv2", "def uu2.{u, v} (α : Sort v) : Sort v := α"),
  ("err/axiomUnusedUniv", "axiom au.{u} : Nat"),
  ("err/thmUnivValueOnly", "theorem ta.{u} : True := (fun (_ : Sort u) => True.intro) PUnit.{u}"),
  ("err/mismatch", "def em : Nat := True.intro"),
  ("err/exampleMismatch", "example : Nat := True.intro"),
  ("err/thmTypeNotProp", "theorem tnp : Nat := Nat.zero"),
  ("err/propDefHeaderUniv", "def dxp (α : Sort _) : True := (fun (_ : Type) => True.intro) α"),
  ("err/appLast", "def dl : Nat := dep Nat Nat"),
  ("err/thmHeaderUnivByBody", "theorem tx (α : Sort _) : True := (fun (_ : Type) => True.intro) α"),
  ("err/unassignedImplicit", "def eu := id"),
  ("err/holeArg", "def eh2 : Nat := pick _ Nat.zero"),
  ("err/holeBare", "def eh3 := _"),
  ("err/binderHole", "def eh (x : _) : Nat := Nat.zero"),
  ("err/funBinderType", "def eh4 := fun x => x"),
  ("err/defTypeHole", "def eh5 : _ := Nat.zero"),
  ("err/thmTypeHole", "theorem thb : _ := True.intro"),
  ("err/axiomBinderHole", "axiom ah (x : _) : Nat"),
  ("err/axiomTypeHole", "axiom ahole : _"),
  ("err/levelMVarValue", "def lv : Nat := (fun (_ : Sort _) => Nat.zero) PUnit"),
  ("err/levelMVarThm", "theorem tc : True := (fun (_ : Sort _) => True.intro) PUnit"),
  ("err/unknownIdBody", "def uib : Nat := nope")
]

/-- Elaborate one command; `.inl firstErrorLine` or `.inr newConstants`. -/
def runCmd (env : Environment) (opts : Options) (src : String) :
    IO (Except String (Except String (Array Json))) := do
  match Lean.Parser.runParserCategory env `command src with
  | .error msg => return .error s!"parse error: {msg}"
  | .ok stx =>
    let ctx : Command.Context :=
      { fileName := "<dump_decls>", fileMap := FileMap.ofString src, snap? := none, cancelTk? := none }
    let r ← (((Command.elabCommandTopLevel stx).run ctx).run (Command.mkState env {} opts)).toBaseIO
    match r with
    | .error ex => return .ok (.error ((← ex.toMessageData.toString).splitOn "\n" |>.headD ""))
    | .ok ((), s) =>
      let snapMsgs := s.snapshotTasks.toList.flatMap fun t =>
        t.get.getAll.toList.flatMap fun snap => snap.diagnostics.msgLog.toList
      let errs := (s.messages.toList ++ snapMsgs).filter (·.severity == .error)
      match errs.head? with
      | some m => return .ok (.error (((← m.data.toString).splitOn "\n").headD ""))
      | none =>
        let news := (s.env.constants.map₂.toList.map (·.1)).toArray.qsort Name.lt
        return .ok (.ok (news.filterMap fun n => (s.env.find? n).map constJ))

unsafe def main (_args : List String) : IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Elab0 }] {} (trustLevel := 0) (loadExts := true)
  let opts : Options := Elab.async.set {} true
  for (id, src) in declQueries do
    match ← runCmd env opts src with
    | .error msg => IO.eprintln s!"dump_decls: {id}: {msg}"
    | .ok (.error e) => IO.eprintln s!"dump_decls: {id} logged an error: {e}"
    | .ok (.ok cs) =>
      IO.println <| Json.compress <| Json.mkObj [("id", id), ("src", src), ("consts", Json.arr cs)]
  for (id, src) in declErrQueries do
    match ← runCmd env opts src with
    | .error msg => IO.eprintln s!"dump_decls: {id}: {msg}"
    | .ok (.ok _) => IO.eprintln s!"dump_decls: {id} was expected to fail but elaborated"
    | .ok (.error e) =>
      IO.println <| Json.compress <| Json.mkObj [("id", id), ("src", src), ("err", e)]
