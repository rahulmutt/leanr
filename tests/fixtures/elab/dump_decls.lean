/- Emits the M4c-1 declaration corpus (spec
`docs/superpowers/specs/2026-10-03-m4c1-single-decl-design.md` § Harness):
for each `(id, src)`, the COMMAND `src` is parsed and elaborated with
`Lean.Elab.Command.elabCommandTopLevel` against the Elab0 environment, and
the constants it added are dumped.

Runs with LEAN_PATH set to this directory so `Elab0` resolves to the
committed fixture and nothing else (the `dump_elab.lean` hermetic contract).

`Elab.async` is set to `true`, matching the `lean` command line
(`Elab/Frontend.lean:291-292`; `CoreM.lean:35` declares it, default false): a theorem then takes `elabAsync`
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

File mode (`lean --run dump_decls.lean files`, M4c-2a spec
`docs/superpowers/specs/2026-10-04-m4c2a-file-loop-design.md` § Harness):
each `fileQueries` source is parsed command by command and elaborated over
ONE threaded `Command.State`, so later commands see earlier constants and
the aux-lemma cache (`auxLemmasExt`). Record shape:
  {"id","src","cmds":[{"consts":[C...]} | {"err":<string>}]}
with one element per command up to and including the first error. A
record whose error is not in its LAST command is reported on stderr and
dropped (leanr stops at the first error, spec decision 2).
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

-- ===== file corpus (M4c-2a spec § Harness; every record probed at plan time) =====

/-- Multi-command sources, one command per line. Each runs against one
threaded `Command.State`; an `err` may only be the LAST command's result
(M4c-2a decision 2: leanr stops at the first error, so nothing after it
is comparable). -/
def fileQueries : List (String × String) := [
  ("chain/defRef", "def c1 : Nat := Nat.zero\ndef c2 : Nat := pick c1 c1"),
  ("chain/thmAbbrev", "def c3 (n : Nat) : Nat := pick n n\nabbrev c4 : Nat := c3 Nat.zero\ntheorem c5 : Eq c4 c4 := rfl"),
  ("chain/univ", "def idu.{u} (α : Sort u) (a : α) : α := a\ndef u1 : Nat := idu Nat Nat.zero\ndef u2 : Type := idu Type Nat"),
  ("aux/reuse", "def na (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl\ndef nb (m : Nat) : PProd Nat (Eq (Nat.succ m) (Nat.succ m)) := PProd.mk m rfl"),
  ("aux/distinct", "def nc (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl\ndef nd (n : Nat) : PProd Nat (Eq (Nat.succ (Nat.succ n)) (Nat.succ (Nat.succ n))) := PProd.mk n rfl"),
  ("aux/overwrite", "def ow1.{u} (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n ((fun (_ : Sort u) => rfl) PUnit.{u})\ndef ow2 (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl\ndef ow3 (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl\ndef ow4.{u} (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n ((fun (_ : Sort u) => rfl) PUnit.{u})"),
  ("aux/reuseUniv", "def pu1.{u} (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n ((fun (_ : Sort u) => rfl) PUnit.{u})\ndef pu2.{v} (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n ((fun (_ : Sort v) => rfl) PUnit.{v})"),
  ("aux/sharedLater", "def ne (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl\ndef nf (n : Nat) : PProd (Eq (Nat.succ n) (Nat.succ n)) (Eq (Nat.succ (Nat.succ n)) (Nat.succ (Nat.succ n))) := PProd.mk rfl rfl"),
  ("aux/sortType", "def ta (α : Type) (a : α) : PProd α (Eq (PProd.mk a a) (PProd.mk a a)) := PProd.mk a rfl\ndef tb (β : Type) (b : β) : PProd β (Eq (PProd.mk b b) (PProd.mk b b)) := PProd.mk b rfl"),
  ("aux/sortProp", "def pa (p : Prop) (h : p) (n : Nat) : PProd Nat (And p (Eq (Nat.succ n) (Nat.succ n))) := PProd.mk n (And.intro h (Eq.refl (Nat.succ n)))\ndef pb (q : Prop) (g : q) (m : Nat) : PProd Nat (And q (Eq (Nat.succ m) (Nat.succ m))) := PProd.mk m (And.intro g (Eq.refl (Nat.succ m)))"),
  ("aux/binderInfo", "def bi1 {n : Nat} : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl\ndef bi2 (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl"),
  ("example/between", "def x1 : Nat := Nat.zero\nexample : Nat := x1\ndef x2 : Nat := pick x1 x1"),
  ("example/auxThenDef", "example (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl\ndef ng (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl"),
  ("thm/auxNotAbstracted", "theorem th1 (n : Nat) : True := (fun (_ : PProd Nat (Eq (Nat.succ n) (Nat.succ n))) => True.intro) (PProd.mk n rfl)\ndef th2 (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl"),
  ("kinds/all", "axiom k1 : Nat\nopaque k2 : Nat := Nat.zero\ntheorem k3 : True := True.intro\nabbrev k4 := k2\nexample : True := k3\ndef k5 := pick k4 k4"),
  ("err/dupLocal", "def dd : Nat := Nat.zero\ndef dd : Nat := pick Nat.zero Nat.zero"),
  ("err/mismatchEarlier", "def me : Nat := Nat.zero\ndef mf : True := me"),
  ("err/thmAfterDef", "def tq : Nat := Nat.zero\ntheorem tr : Eq tq Nat.zero := True.intro"),
  ("scope/ns", "namespace A\ndef f : Nat := Nat.zero\nend A\ndef g : Nat := A.f"),
  ("scope/nested", "namespace A.B\ndef f : Nat := Nat.zero\nend A.B\ndef g : Nat := A.B.f"),
  ("scope/nestedSplit", "namespace A.B\ndef f : Nat := Nat.zero\nend B\ndef g : Nat := B.f\nend A"),
  ("scope/section", "section\ndef s1 : Nat := Nat.zero\nend\nsection Foo\ndef s2 : Nat := s1\nend Foo"),
  ("scope/sectionInNs", "namespace A\nsection S\ndef f : Nat := Nat.zero\nend S\ndef g : Nat := f\nend A"),
  ("scope/sectionDotted", "section A.B\ndef f : Nat := Nat.zero\nend A.B"),
  ("scope/reopen", "namespace A\ndef f : Nat := Nat.zero\nend A\nnamespace A\ndef g : Nat := f\nend A"),
  ("name/dotted", "def A.g : Nat := Nat.zero\ndef A.f : Nat := g"),
  ("name/dottedNoNs", "def Foo.bar : Nat := Nat.zero\ndef baz : Nat := Foo.bar"),
  ("name/dottedInNs", "namespace A\ndef B.f : Nat := Nat.zero\ndef g : Nat := B.f\nend A"),
  ("name/rootInNs", "namespace A\ndef _root_.rx : Nat := Nat.zero\ndef f : Nat := rx\nend A"),
  ("name/rootDotted", "namespace A\ndef _root_.B.rx : Nat := Nat.zero\nend A\ndef f : Nat := B.rx"),
  ("name/protected", "namespace A\nprotected def p : Nat := Nat.zero\ndef q : Nat := A.p\nend A"),
  ("name/protectedDotted", "protected def A.p2 : Nat := Nat.zero\ndef q2 : Nat := A.p2"),
  ("name/protectedNonAtomic", "namespace A\nprotected def B.p : Nat := Nat.zero\ndef q : Nat := B.p\nend A"),
  ("name/protectedTheorem", "namespace A\nprotected theorem t : True := True.intro\nend A\ntheorem u : True := A.t"),
  ("name/protectedRootDotted", "protected def A.B : Nat := Nat.zero\nnamespace A\ndef f : Nat := A.B\nend A"),
  ("res/walkInner", "def w : Nat := Nat.zero\nnamespace A\ndef w : Nat := pick Nat.zero Nat.zero\nnamespace B\ndef u : Nat := w\nend B\nend A"),
  ("res/rootFallback", "def r0 : Nat := Nat.zero\nnamespace A\ndef f : Nat := r0\nend A"),
  ("res/fieldSplit", "namespace A\ndef pp : PProd Nat Nat := PProd.mk Nat.zero Nat.zero\ndef f : Nat := pp.fst\nend A"),
  ("res/qualifiedInNs", "namespace A\ndef f : Nat := Nat.zero\nend A\nnamespace B\ndef g : Nat := A.f\nend B"),
  ("res/importedOpen", "open Scope0\ndef f : Nat := shown\ndef g : Nat := Inner.deep"),
  ("res/importedNs", "namespace Scope0\ndef f : Nat := shown\ndef g : Nat := Scope0.hidden\nend Scope0"),
  ("res/alias", "def f : Nat := ex"),
  ("res/aliasQualified", "def f : Nat := Scope0Exp.ex"),
  ("res/protectedQualified", "open Scope0\ndef f : Nat := Scope0.hidden"),
  ("res/numeralShadow", "namespace X\ndef OfNat : Nat := Nat.zero\ndef z : Nat := 0\nend X"),
  ("res/recPrefix", "def f : Nat := Nat.zero\nnamespace B\ndef g : Nat := f\nend B"),
  ("res/globalDeclFound", "def foo.aux : Nat := Nat.zero\ndef foo : Nat := foo.aux"),
  ("res/openNat", "open Nat\ndef f : Nat := zero"),
  ("res/aliasInNs", "namespace Scope0Exp\ndef g : Nat := ex\nend Scope0Exp"),
  ("res/binderShadowsSelf", "def g (g : Nat) : Nat := g"),
  ("res/headerBinderSelf", "def h : Eq ((fun (h : Nat) => h) Nat.zero) Nat.zero := rfl"),
  ("res/headerSeesRoot", "def x : Nat := Nat.zero\nnamespace A\ndef x : Eq x x := rfl"),
  ("open/simple", "open Scope0\ndef f : Nat := Scope0.shown"),
  ("open/two", "open Scope0 Scope0Exp\ndef f : Nat := shown"),
  ("open/only", "open Scope0 (shown)\ndef f : Nat := shown"),
  ("open/onlyTwo", "open Scope0.Inner (deep)\ndef f : Nat := deep"),
  ("open/hiding", "open Scope0 hiding shown\ndef f : Nat := Inner.deep"),
  ("open/renaming", "open Scope0 renaming shown → sh\ndef f : Nat := sh"),
  ("open/in", "open Scope0 in\ndef f : Nat := shown\ndef g : Nat := Scope0.shown"),
  ("open/rootQualified", "namespace Scope0\ndef f : Nat := _root_.Scope0.shown\nend Scope0"),
  ("open/explicitPrefix", "namespace A\ndef k : Nat := Nat.zero\ndef k.sub : Nat := Nat.zero\nend A\nopen A (k)\ndef f : Nat := k.sub"),
  ("open/relative", "namespace Scope0\nopen Inner\ndef f : Nat := deep\nend Scope0"),
  ("open/sectionScoped", "section\nopen Scope0\ndef f : Nat := shown\nend\ndef g : Nat := Scope0.shown"),
  ("open/fileLocal", "namespace A\ndef k : Nat := Nat.zero\nend A\nopen A\ndef f : Nat := k"),
  ("open/prefixOnly", "def _root_.A.k : Nat := Nat.zero\nopen A\ndef f : Nat := k"),
  ("open/threaded", "open Scope0 Inner\ndef f : Nat := deep"),
  ("open/nsScopeFirst", "namespace A\nnamespace C\ndef k : Nat := Nat.zero\nend C\nend A\nnamespace C\ndef j : Nat := Nat.zero\nend C\nnamespace A\nopen C\ndef f : Nat := k\nend A"),
  ("err/endNoScope", "def f : Nat := Nat.zero\nend"),
  ("err/endMissingName", "namespace A\nend"),
  ("err/endTooMany", "namespace A\nend A.B"),
  ("err/endMismatch", "namespace A\nend B"),
  ("err/endUnnamed", "section\nend A"),
  ("err/unknownNs", "open Nope"),
  ("err/protectedRoot", "protected def p : Nat := Nat.zero"),
  ("err/rootBare", "def _root_ : Nat := Nat.zero"),
  ("err/openOnlyMissing", "open Scope0 (nope)"),
  ("err/protectedShort", "namespace A\nprotected def p : Nat := Nat.zero\ndef q : Nat := p"),
  ("err/importedProtected", "open Scope0\ndef f : Nat := hidden"),
  ("err/hidden", "open Scope0 hiding shown\ndef f : Nat := shown"),
  ("err/sectionClosed", "section\nopen Scope0\nend\ndef f : Nat := shown"),
  ("err/dupInNs", "namespace A\ndef f : Nat := Nat.zero\ndef f : Nat := Nat.zero"),
  ("err/dupDotted", "def A.f : Nat := Nat.zero\nnamespace A\ndef f : Nat := Nat.zero"),
  ("err/elimViaOpen", "open Nat\ndef f : Nat → Nat := casesOn"),
  ("err/protectedRecOn", "open Nat\ndef f : Nat → Nat := recOn"),
  ("err/renamedAway", "open Scope0 renaming shown → sh\ndef f : Nat := shown"),
  ("err/openRenamingMissing", "open Scope0 renaming nope → n"),
  ("err/hidingMissing", "open Scope0 hiding nope"),
  ("err/thmNotPropNs", "namespace A\ntheorem t : Nat := Nat.zero"),
  ("err/inScoped", "open Scope0 in\ndef f : Nat := shown\ndef g : Nat := shown"),
  ("overload/argType", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t := f Nat.zero"),
  ("overload/argBool", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t := f Bool.true"),
  ("overload/argNumeral", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t := f 0"),
  ("overload/expectedType", "namespace A\ndef c : Nat := Nat.zero\nend A\nnamespace B\ndef c : Bool := Bool.true\nend B\nopen A B\ndef t : Bool := c"),
  ("overload/coe", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t : Int := f Nat.zero"),
  ("overload/coeBoth", "namespace A\ndef g : Nat := Nat.zero\nend A\nnamespace B\ndef g : Int := Int.ofNat Nat.zero\nend B\nopen A B\ndef t : Int := g"),
  ("overload/ambiguous", "namespace A\ndef g : Nat := Nat.zero\nend A\nnamespace B\ndef g : Nat := pick Nat.zero Nat.zero\nend B\nopen A B\ndef t : Nat := g"),
  ("overload/ambiguousNoType", "namespace A\ndef g : Nat := Nat.zero\nend A\nnamespace B\ndef g : Nat := pick Nat.zero Nat.zero\nend B\nopen A B\ndef t := g"),
  ("overload/binderNames", "namespace A\ndef k (n : Nat) : Nat := n\nend A\nnamespace B\ndef k (b : Bool) : Bool := b\nend B\nopen A B\ndef t := fun y => k y"),
  ("overload/allFail", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t := f Unit.unit"),
  ("overload/binder", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t (x : Nat) := f x"),
  ("overload/binderBool", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t (x : Bool) := f x"),
  ("overload/localShadows", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t (f : Nat) := f"),
  ("overload/fields", "def Nat.dbl (n : Nat) : Nat := n\nnamespace A\ndef n : Nat := Nat.zero\nend A\nnamespace B\ndef n : Bool := Bool.true\nend B\nopen A B\ndef t := n.dbl"),
  ("overload/lvals", "def Nat.dbl (n : Nat) : Nat := n\nnamespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t := (f Nat.zero).dbl"),
  ("overload/pipeLvals", "def Nat.dbl (n : Nat) : Nat := n\nnamespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t := f Nat.zero |>.dbl"),
  ("overload/explicitAt", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t := @f Nat.zero"),
  ("overload/namedArg", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t := f (n := Nat.zero)"),
  ("overload/explicitUniv", "namespace A\ndef u.{w} (a : Sort w) : Sort w := a\nend A\nnamespace B\ndef u (b : Bool) : Bool := b\nend B\nopen A B\ndef t := u.{1} Nat"),
  ("overload/delayedCoeStuck", "namespace A\ndef g {a : Type} : List a := List.nil\nend A\nnamespace B\ndef g : Int := Int.ofNat Nat.zero\nend B\nopen A B\ndef t : Int := g"),
  ("overload/delayedCoeArg", "namespace A\ndef g {a : Type} (x : a) : List a := List.nil\nend A\nnamespace B\ndef g (n : Nat) : Int := Int.ofNat n\nend B\nopen A B\ndef t (x : Nat) : Int := g x"),
  ("overload/delayedCoeStage2", "namespace A\ndef g {a : Type} [Dflt a] : List a := List.nil\nend A\nnamespace B\ndef g : Int := Int.ofNat Nat.zero\nend B\nopen A B\ndef t : Int := g"),
  ("overload/delayedCoeControl", "namespace A\ndef g {a : Type} [Dflt a] : List a := List.nil\nend A\ndef t : Int := A.g"),
  ("overload/stage3", "namespace A\ndef h {a : Type} [NoInst a] : Nat := Nat.zero\nend A\nnamespace B\ndef h : Nat := Nat.zero\nend B\nopen A B\ndef t : Nat := h"),
  ("overload/stage3Default", "namespace A\ndef h {a : Type} [Dflt a] : Nat := Nat.zero\nend A\nnamespace B\ndef h : Nat := Nat.zero\nend B\nopen A B\ndef t : Nat := h"),
  ("overload/pendingInst", "namespace A\ndef w {a : Type} [Wrap a] (x : a) : a := x\nend A\nnamespace B\ndef w {a : Type} [NoInst a] (x : a) : a := x\nend B\nopen A B\ndef t := w Nat.zero"),
  ("overload/rootAndOpen", "def shown : Nat := Nat.zero\nopen Scope0\ndef f : Nat := shown"),
  ("overload/exportAlias", "def Scope0.ex : Nat := Nat.zero\nopen Scope0\ndef f : Nat := ex"),
  ("overload/nestedArg", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t := pick (f Nat.zero) Nat.zero"),
  ("overload/argExpected", "namespace A\ndef c : Nat := Nat.zero\nend A\nnamespace B\ndef c : Bool := Bool.true\nend B\nopen A B\ndef t := pick c Nat.zero"),
  ("overload/underFun", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\ndef t : Nat → Nat := fun x => f x"),
  ("overload/inType", "namespace A\ndef c : Nat := Nat.zero\nend A\nnamespace B\ndef c : Bool := Bool.true\nend B\nopen A B\ndef t (h : Eq c Nat.zero) : Nat := Nat.zero"),
  ("overload/twoOverloads", "namespace A\ndef f (n : Nat) : Nat := n\nend A\nnamespace B\ndef f (b : Bool) : Bool := b\nend B\nopen A B\nnamespace A\ndef c : Nat := Nat.zero\nend A\nnamespace B\ndef c : Bool := Bool.true\nend B\nopen A B\ndef t := f c"),
  ("overload/dotIdentPick", "namespace A\ndef Nat.two : Nat := Nat.zero\nend A\nnamespace B\ndef Nat.two (b : Bool) : Nat := Nat.zero\nend B\nopen A B\ndef t : Nat := .two"),
  ("overload/dotIdentArgs", "namespace A\ndef Nat.two : Nat := Nat.zero\nend A\nnamespace B\ndef Nat.two (b : Bool) : Nat := Nat.zero\nend B\nopen A B\ndef t : Nat := .two Bool.true"),
  ("overload/dotIdentAmbig", "namespace A\ndef Nat.two : Nat := Nat.zero\nend A\nnamespace B\ndef Nat.two : Nat := pick Nat.zero Nat.zero\nend B\nopen A B\ndef t : Nat := .two"),
  ("overload/dotIdentAllFail", "namespace A\ndef Nat.two : Nat := Nat.zero\nend A\nnamespace B\ndef Nat.two (b : Bool) : Nat := Nat.zero\nend B\nopen A B\ndef t : Nat := .two Unit.unit"),
  ("ambig/fieldName", "namespace A\ndef S1.g (s : S1) : Nat := Nat.zero\nend A\nnamespace B\ndef S1.g (s : S1) : Nat := Nat.zero\nend B\nopen A B\ndef t (s : S1) : Nat := s.g"),
  ("ambig/openHiding", "namespace A.X\ndef p : Nat := Nat.zero\nend A.X\nnamespace B.X\ndef p : Nat := Nat.zero\nend B.X\nopen A B\nopen X hiding p"),
  ("ambig/openRenaming", "namespace A.X\ndef p : Nat := Nat.zero\nend A.X\nnamespace B.X\ndef p : Nat := Nat.zero\nend B.X\nopen A B\nopen X renaming p → q"),
  ("ambig/openFailed", "namespace A.X\ndef p : Nat := Nat.zero\nend A.X\nnamespace B.X\ndef p : Nat := Nat.zero\nend B.X\nopen A B\nopen X (r)"),
  ("ambig/openFailedOne", "namespace A.X\ndef p : Nat := Nat.zero\nend A.X\nopen A\nopen X (r)")
]

/-- The first error-severity message `s` logged, from `messages` and the
async `snapshotTasks` (see the module doc), as its first line. -/
def firstErr? (s : Command.State) : IO (Option String) := do
  let snapMsgs := s.snapshotTasks.toList.flatMap fun t =>
    t.get.getAll.toList.flatMap fun snap => snap.diagnostics.msgLog.toList
  match ((s.messages.toList ++ snapMsgs).filter (·.severity == .error)).head? with
  | some m => return some (((← m.data.toString).splitOn "\n").headD "")
  | none => return none

/-- Elaborate `src` command by command over ONE threaded `Command.State`.
Returns `(results, nCommands)`: one `{"consts"}`/`{"err"}` per command up to
and including the first error, and the number of commands the source
parses into (the commands after an error are parsed, not elaborated). -/
def runFile (env : Environment) (opts : Options) (src : String) :
    IO (Except String (Array Json × Nat)) := do
  let inputCtx := Parser.mkInputContext src "<dump_decls>"
  let ctx : Command.Context :=
    { fileName := "<dump_decls>", fileMap := inputCtx.fileMap, snap? := none, cancelTk? := none }
  let mut st := Command.mkState env {} opts
  let mut ps : Parser.ModuleParserState := {}
  let mut out : Array Json := #[]
  let mut n := 0
  let mut stopped := false
  repeat
    let scope := st.scopes.head!
    let pmctx : Parser.ParserModuleContext :=
      { env := st.env, options := scope.opts, currNamespace := scope.currNamespace,
        openDecls := scope.openDecls }
    let (stx, ps', pmsgs) := Parser.parseCommand inputCtx pmctx ps {}
    ps := ps'
    if pmsgs.hasErrors then return .error "parse error"
    if stx.isOfKind ``Parser.Command.eoi then break
    n := n + 1
    if stopped then continue
    let before : NameSet :=
      st.env.constants.map₂.toList.foldl (fun s (c, _) => s.insert c) {}
    let r ← (((Command.elabCommandTopLevel stx).run ctx).run
      { st with messages := {}, snapshotTasks := #[] }).toBaseIO
    match r with
    | .error ex =>
      out := out.push (Json.mkObj [("err", ((← ex.toMessageData.toString).splitOn "\n").headD "")])
      stopped := true
    | .ok ((), s) =>
      match ← firstErr? s with
      | some e =>
        out := out.push (Json.mkObj [("err", e)])
        stopped := true
      | none =>
        let news := ((s.env.constants.map₂.toList.map (·.1)).filter (!before.contains ·)).toArray.qsort Name.lt
        out := out.push (Json.mkObj [("consts", Json.arr (news.filterMap fun c => (s.env.find? c).map constJ))])
        st := s
  return .ok (out, n)

unsafe def main (args : List String) : IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Elab0 }] {} (trustLevel := 0) (loadExts := true)
  let opts : Options := Elab.async.set {} true
  if args == ["files"] then
    for (id, src) in fileQueries do
      match ← runFile env opts src with
      | .error msg => IO.eprintln s!"dump_decls files: {id}: {msg}"
      | .ok (cmds, n) =>
        if cmds.size != n then
          IO.eprintln s!"dump_decls files: {id}: an error before the last command ({cmds.size}/{n}); dropped"
        else
          IO.println <| Json.compress <| Json.mkObj [("id", id), ("src", src), ("cmds", Json.arr cmds)]
    return
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
