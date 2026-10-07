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
  ("np/nestedTwice", "def npn (n : Nat) : PProd Nat (PProd Nat (Eq (Nat.succ n) (Nat.succ n))) := PProd.mk n (PProd.mk n rfl)"),
  -- `mkBinding` head-betas each binder domain (`MetavarContext.lean:1319`);
  -- a return type, a nested redex and an `→` domain (`Binders.lean:297`,
  -- plain `mkForall`) keep theirs.
  ("beta/thm", "theorem bt1 (n : Nat) (h : (fun (m : Nat) => Eq m m) n) : Eq n n := h"),
  ("beta/axiom", "axiom bt2 (n : Nat) (h : (fun (m : Nat) => Eq m m) n) : Eq n n"),
  ("beta/def", "def bt3 (n : Nat) (k : (fun (_ : Nat) => Nat) n) : Nat := k"),
  ("beta/fun", "def bt4 : Nat → Nat := fun (x : (fun (_ : Nat) => Nat) Nat.zero) => x"),
  ("beta/forall", "def bt5 : Prop := ∀ (n : Nat) (h : (fun (m : Nat) => Eq m m) n), Eq n n"),
  ("beta/retNot", "def bt6 (n : Nat) : (fun (_ : Nat) => Nat) n := n"),
  ("beta/nestedNot", "def bt7 (n : Nat) (p : PProd ((fun (_ : Nat) => Nat) n) Nat) : Nat := n"),
  ("beta/arrowNot", "def bt8 : (fun (_ : Nat) => Nat) Nat.zero → Nat := fun x => x"),
  ("beta/multi", "def bt11 (n : Nat) (k : (fun (_ : Nat) (_ : Nat) => Nat) n n) : Nat := k"),
  ("beta/implicit", "def bt12 {n : (fun (_ : Nat) => Nat) Nat.zero} : Nat := n")
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
  ("ambig/openFailedOne", "namespace A.X\ndef p : Nat := Nat.zero\nend A.X\nopen A\nopen X (r)"),
  ("universe/def", "universe u\ndef uf1 (α : Sort u) (a : α) : α := a"),
  ("universe/thm", "universe u\ntheorem ut1 (α : Sort u) (a : α) : Eq a a := rfl"),
  ("universe/axiom", "universe u\naxiom ua1 (α : Sort u) : α"),
  ("universe/order", "universe u v\ndef uo.{w} (a : Sort w) (b : Sort v) (c : Sort u) : Sort u := c"),
  ("universe/thmOrder", "universe u v\ntheorem uto (α : Sort v) (β : Sort u) (a : α) (b : β) : Eq a a := rfl"),
  ("universe/unusedScope", "universe u v\ndef uu (α : Sort u) : Sort u := α"),
  ("universe/unusedExplicit", "universe u\ndef ue.{w} (α : Sort u) : Sort u := α"),
  ("universe/dup", "universe u\nuniverse u"),
  ("universe/dupSame", "universe u u"),
  ("universe/declClash", "universe u\ndef uc.{u} (α : Sort u) : Sort u := α"),
  ("universe/sectionDrop", "section\nuniverse u\nend\nuniverse u\ndef us (α : Sort u) : Sort u := α"),
  ("universe/withHole", "universe u\ndef uh (α : Sort u) (β : Sort _) : Sort u := α"),
  ("universe/thmWithHole", "universe u\ntheorem uth (α : Sort u) (β : Sort _) (b : β) : Eq b b := rfl"),
  ("universe/axiomUnusedScope", "universe u v\naxiom aus (α : Sort v) : α"),
  ("universe/inNamespace", "namespace A\nuniverse u\ndef un (α : Sort u) : Sort u := α\nend A"),
  ("universe/thmBodyOnlyScope", "universe u\ntheorem ra : Eq Nat.zero Nat.zero := (fun (_ : Sort u) => rfl) PUnit"),
  -- Doubly broken: `elabAsync` runs `addPreDefinitions` (its unassigned-
  -- mvar check) before `commitConst`, so the mvar error wins.
  ("universe/thmBodyOnlyScopeLevelMVar", "universe u\ntheorem rb : Eq Nat.zero Nat.zero := (fun (_ : Sort u) (_ : Sort _) => rfl) PUnit PUnit"),
  ("universe/thmBodyOnlyScopeHole", "universe u\ntheorem rc : Eq Nat.zero Nat.zero := (fun (_ : Sort u) (_ : Nat) => rfl) PUnit _"),
  ("var/defBody", "variable (n : Nat)\ndef vf1 : Nat := n"),
  ("var/defUnused", "variable (n : Nat)\ndef vf2 : Nat := Nat.zero"),
  ("var/defHeader", "variable (n : Nat)\ndef vf3 (m : Nat) (h : Eq n m) : Nat := m"),
  ("var/order", "variable (m : Nat) (n : Nat)\ndef vf4 : Nat := pick n m"),
  ("var/instDefUnref", "variable {a : Type} [Dflt a] (x : a)\ndef vf5 : a := x"),
  ("var/instDefRef", "variable {a : Type} [Dflt a] (x : a)\ndef vf6 : a := dpair x"),
  ("var/abbrev", "variable (n : Nat)\nabbrev vf7 : Nat := n"),
  ("var/example", "variable (n : Nat)\nexample : Nat := n"),
  ("var/auxProof", "variable (n : Nat)\ndef vf8 : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl"),
  ("var/multiCmd", "variable (m : Nat)\nvariable (n : Nat)\ndef vf9 : Nat := pick n m"),
  ("var/shadowBinder", "variable (n : Nat)\ndef vf10 (n : Nat) : Nat := n"),
  ("var/redeclare", "variable (n : Nat)\nvariable (n : Nat)\ndef vf11 : Nat := n"),
  ("var/sectionDrop", "section\nvariable (n : Nat)\nend\ndef vf12 : Nat := n"),
  ("var/namespace", "namespace A\nvariable (n : Nat)\ndef vf13 : Nat := n\nend A\ndef vf14 : Nat := A.vf13 Nat.zero"),
  ("var/implicitBody", "variable {n : Nat}\ndef vf15 : Nat := n"),
  ("var/strictImplicit", "variable ⦃n : Nat⦄\ndef vf16 : Nat := n"),
  ("var/typeVarOnlyViaHeader", "variable {a : Type} (x : a)\ndef vf17 (y : a) : a := y"),
  ("var/errType", "variable (n : Nat)\nvariable (x : Nat.zero)"),
  ("var/errLaterDecl", "variable (n : Nat)\ndef vf18 : Nat := m"),
  ("var/noType", "variable (n : Nat)\ndef vf19 := n"),
  ("var/levelMVar", "variable (α : Sort _)\ndef vf20 (a : α) : α := a"),
  ("var/typeDepDef", "variable {a : Type} (f : a → Nat) (x : a)\ndef sg : Nat := f x"),
  ("varThm/header", "variable (n : Nat)\ntheorem vt1 : Eq n n := rfl"),
  ("varThm/unused", "variable (n : Nat)\ntheorem vt2 : Eq Nat.zero Nat.zero := rfl"),
  ("varThm/bodyOnly", "variable (n : Nat)\ntheorem vt3 : Eq Nat.zero Nat.zero := (fun (_ : Nat) => rfl) n"),
  ("varThm/inst", "variable {a : Type} [Dflt a] (x : a)\ntheorem vt4 : Eq x x := rfl"),
  ("varThm/instNotCovered", "variable {a : Type} {b : Type} [Pair a b] (x : a)\ntheorem vt5 : Eq x x := rfl"),
  ("varThm/instInProof", "variable {a : Type} [Wrap a] (x : a)\ntheorem vt6 : Eq (useWrap x) (useWrap x) := rfl"),
  ("varThm/instUsedInProofOnly", "variable {a : Type} {b : Type} [Pair a b] (x : a) (y : b)\ntheorem vt7 : Eq x x := (fun (_ : a) => rfl) (usePair x y)"),
  ("varThm/instCoveredByBinder", "variable {a : Type} {b : Type} [Pair a b] (x : a)\ntheorem vt8 (y : b) : Eq x x := rfl"),
  ("varAxiom/include", "variable (n : Nat)\ninclude n\naxiom va1 : Eq Nat.zero Nat.zero"),
  ("varAxiom/inst", "variable {a : Type} [Dflt a] (x : a)\naxiom va2 : Eq x x"),
  ("varAxiom/used", "variable (n : Nat) (m : Nat)\naxiom va3 : Eq m m"),
  ("varAxiom/typeDep", "variable {a : Type} (f : a → Nat) (x : a)\naxiom sh : Eq (f x) (f x)"),
  ("varLevel/typeHole", "variable (α : Type _)\ndef vl1 (a : α) : α := a"),
  ("varLevel/twoHoles", "variable (α : Type _) (β : Type _)\ndef vl2 (b : β) (a : α) : β := b"),
  ("varLevel/thmHole", "variable (α : Type _)\ntheorem vl3 (a : α) : Eq a a := rfl"),
  ("varLevel/scopeUniv", "universe u\nvariable (α : Type u)\ndef vl4 (a : α) : α := a"),
  ("varLevel/axiomHole", "variable (α : Sort _)\naxiom vl5 (a : α) : α"),
  ("varLevel/holeAndExplicit", "variable (α : Type _)\ndef vl6.{v} (β : Sort v) (a : α) : α := a"),
  ("varLevel/twoDecls", "variable (α : Type _)\ndef vl7 (a : α) : α := a\ndef vl8 (a : α) : α := a"),
  ("varLevel/scopeAndExplicitThm", "universe u\nvariable (α : Sort u)\ntheorem vt9.{v} (β : Sort v) (a : α) (b : β) : Eq a a := rfl"),
  ("varLevel/thmBodyPinsHole", "variable (α : Type _) (P : α → Prop) (x : α)\ntheorem vl9 (h : P x) : P x := (fun (_ : Type) => h) α"),
  ("include/basic", "variable (n : Nat)\ninclude n\ntheorem vi1 : Eq Nat.zero Nat.zero := rfl"),
  ("include/in", "variable (n : Nat)\ninclude n in\ntheorem vi2 : Eq Nat.zero Nat.zero := rfl\ntheorem vi3 : Eq Nat.zero Nat.zero := rfl"),
  ("include/undeclared", "variable (n : Nat)\ninclude m"),
  ("include/def", "variable (n : Nat)\ninclude n\ndef vi4 : Nat := Nat.zero"),
  ("include/transitive", "variable {a : Type} (x : a)\ninclude x\ntheorem vi5 : Eq Nat.zero Nat.zero := rfl"),
  ("include/order", "variable (m : Nat) (n : Nat)\ninclude n m\ntheorem vi6 : Eq Nat.zero Nat.zero := rfl"),
  ("include/instClosure", "variable {a : Type} [Dflt a] (x : a)\ninclude x\ntheorem vi7 : Eq Nat.zero Nat.zero := rfl"),
  ("include/twice", "variable (n : Nat)\ninclude n n\ntheorem vi8 : Eq Nat.zero Nat.zero := rfl"),
  ("include/instByName", "variable {a : Type} [inst : Dflt a]\ninclude inst\ntheorem vi9 : Eq Nat.zero Nat.zero := rfl"),
  ("include/proofUsesIncluded", "variable (n : Nat)\ninclude n\ntheorem vi10 : Eq Nat.zero Nat.zero := (fun (_ : Nat) => rfl) n"),
  ("omit/inst", "variable {a : Type} [Dflt a] (x : a)\nomit [Dflt a] in\ntheorem vo1 : Eq x x := rfl"),
  ("omit/name", "variable {a : Type} [inst : Dflt a] (x : a)\nomit inst in\ntheorem vo2 : Eq x x := rfl"),
  ("omit/namedInstForm", "variable {a : Type} [inst : Dflt a] (x : a)\nomit [inst : Dflt a] in\ntheorem vo3 : Eq x x := rfl"),
  ("omit/referenced", "variable (n : Nat)\nomit n in\ntheorem vo4 : Eq n n := rfl"),
  ("omit/unmatchedName", "variable (n : Nat)\nomit m"),
  ("omit/unmatchedInst", "variable (n : Nat)\nomit [Wrap Nat]"),
  ("omit/thenInclude", "variable (n : Nat)\nomit n\ninclude n\ntheorem vo5 : Eq Nat.zero Nat.zero := rfl"),
  ("omit/includeThenOmit", "variable (n : Nat)\ninclude n\nomit n\ntheorem vo6 : Eq Nat.zero Nat.zero := rfl"),
  ("omit/def", "variable (n : Nat)\nomit n\ndef vo7 : Nat := n"),
  ("omit/axiom", "variable (n : Nat)\nomit n\naxiom vo8 : Eq n n"),
  ("omit/instDefeq", "variable {a : Type} [Dflt a] (x : a)\nomit [Dflt _] in\ntheorem vo9 : Eq x x := rfl"),
  ("omit/twoMatch", "variable {a : Type} {b : Type} [Dflt a] [Dflt b] (x : a) (y : b)\nomit [Dflt _] in\ntheorem vo10 : Eq (PProd.mk x y) (PProd.mk x y) := rfl"),
  ("omit/referencedOrder", "variable (m : Nat) (n : Nat)\nomit m n in\ntheorem vo11 : Eq n m := rfl"),
  ("omit/referencedAnonInst", "variable {a : Type} [Dflt a]\nomit [Dflt a] in\ntheorem vo12 : Eq (Dflt.val : a) Dflt.val := rfl"),
  ("auto/identDef", "def ai1 (x : α) : α := x"),
  ("auto/identTwoOrder", "def ai2 (x : β) (y : α) : β := x"),
  ("auto/identRetOnly", "def ai3 : α → α := fun x => x"),
  ("auto/identThm", "theorem ai4 (x : α) : Eq x x := rfl"),
  ("auto/identAxiom", "axiom ai5 (x : α) : Eq x x"),
  ("auto/identFn", "def ai6 (f : α → β) (x : α) : β := f x"),
  ("auto/identList", "def ai7 (xs : List α) : List α := xs"),
  ("auto/identNoRetTy", "def ai12 (x : α) := x"),
  ("auto/identExample", "example (x : α) : Eq x x := rfl"),
  ("auto/identInst", "def ai11 [Wrap α] (x : α) : α := x"),
  ("auto/identAssigned", "def ai13 (x : Nat) (h : Eq x y) : Nat := y"),
  ("auto/identRepeat", "def ai14 (x : α) (y : α) : α := y"),
  ("auto/identLater", "def ai1b (x : α) : α := x\ndef ai1c : Nat := ai1b Nat.zero"),
  ("auto/namedArgIdent", "def ai1d (x : α) : α := x\ndef ai1e : Nat := ai1d (α := Nat) Nat.zero"),
  ("auto/mvarThm", "theorem am1 : Eq a a := rfl"),
  ("auto/mvarExample", "example : Eq a a := rfl"),
  ("auto/mvarTwo", "def am2 (h : Eq a b) : Eq a b := h"),
  ("auto/mvarAxiom", "axiom am4 (h : Eq a b) : Eq b a"),
  ("auto/namedArgMvar", "theorem am3 : Eq a a := rfl\nexample : Eq Nat.zero Nat.zero := am3 (α := Nat)"),
  ("auto/namedArgMvarFvar", "theorem am5 : Eq a a := rfl\nexample : Eq Nat.zero Nat.zero := am5 (a := Nat.zero)"),
  ("auto/mvarHEq", "axiom am6 (h : HEq a b) : Nat"),
  ("auto/mvarDep", "axiom am7 (h : dep a) : Nat"),
  ("auto/levelDef", "def al1 (α : Sort u) (a : α) : α := a"),
  ("auto/levelTwo", "def al2 (α : Sort v) (β : Sort u) (a : α) (b : β) : α := a"),
  ("auto/levelExplicit", "def al3.{v} (α : Sort u) (β : Sort v) (a : α) : α := a"),
  ("auto/levelType", "def al4 (α : Type u) : Type u := α"),
  ("auto/levelThm", "theorem al5 (α : Sort u) (a : α) : Eq a a := rfl"),
  ("auto/levelAxiom", "axiom al6 (α : Sort u) : α"),
  ("auto/levelScope", "universe v\ndef al7 (α : Sort u) (β : Sort v) (a : α) : α := a"),
  ("auto/levelBody", "def al8 : Nat := (fun (_ : Sort u) => Nat.zero) Nat"),
  ("auto/levelWithIdent", "def al9 (x : α) (β : Sort u) : α := x"),
  ("auto/levelExplicitArg", "def al10 (α : Sort u) (a : α) : α := a\ndef al11 : Nat := al10.{1} Nat Nat.zero"),
  ("auto/levelThmUnused", "theorem al12 (α : Sort u) : Eq Nat.zero Nat.zero := rfl"),
  ("auto/negDotted", "def an1 (x : Foo.bar) : Nat := Nat.zero"),
  ("auto/negForbidden", "def an2 (x : an2) : Nat := Nat.zero"),
  ("auto/negBody", "def an3 : Nat := zz"),
  ("auto/negFnApp", "def an4 (x : F Nat) : Nat := Nat.zero"),
  ("auto/negForbiddenNs", "namespace N\ndef an5 (x : an5) : Nat := Nat.zero"),
  ("auto/negForbiddenDotted", "def N2.an6 (x : an6) : Nat := Nat.zero"),
  ("auto/negForbiddenAxiom", "axiom an7 (x : an7) : Nat"),
  ("auto/negDependsExplicit", "def ad1 (β : Type) (h : Eq (x : β) x) : Nat := Nat.zero"),
  ("auto/negDependsExplicitAx", "axiom ad2 (β : Type) (h : Eq (x : β) x) : Nat"),
  ("coeStuck/ascription", "def cs1 (n : Nat) : Nat := (fun (_ : Wrapper _) => Nat.zero) (n : Wrapper _)"),
  ("coeStuck/ascriptionAx", "axiom cs2 (n : Nat) (h : Eq (n : Wrapper _) (n : Wrapper _)) : Nat"),
  ("coeStuck/arg", "axiom cs3 (n : Nat) (h : Eq (pairW n) (pairW n)) : Nat"),
  ("coeStuck/argDef", "def cs4 (n : Nat) : Nat := (fun (_ : Wrapper _) => Nat.zero) (pairW n)"),
  ("coeStuck/variable", "variable (β : Type) (h : @Eq β a a)"),
  ("coeStuck/explicitAt", "axiom cs6 (β : Type) (h : @Eq β x x) : Nat"),
  ("coeStuck/argAfterAscription", "axiom cs7 (β : Type) (h : @Eq _ x (x : β)) : Nat"),
  ("coeStuck/lastArg", "axiom cs9 (β : Type) (h : @HEq _ x β x) : Nat"),
  ("coeStuck/lastArgDef", "def cs10 (β : Type) (h : @HEq _ x β x) : Nat := Nat.zero"),
  ("coeStuck/explicitMotiveNamed", "axiom ce1 (β : Type) (e : Eq x x) (z : True) (h : Eq (Eq.subst' (α := β) (a := x) (b := x) (motive := fun _ => True) e z) z) : Nat"),
  ("coeStuck/explicitMotivePre", "axiom ce2 (β : Type) (z : True) (f : β → Nat) (h : Eq (preElim (f x) (motive := fun _ => True) z Nat.zero) z) : Nat"),
  ("coeStuck/explicitMotiveMajor", "axiom ce3 (β : Type) (g : β → Nat) (h : Eq (natElim (motive := fun _ => Nat) Nat.zero (fun _ ih => ih) (g x)) Nat.zero) : Nat"),
  ("coeStuck/explicitMotiveOk", "axiom ce4 (β : Type) (h : Eq (preElim x (motive := fun _ => True) True.intro Nat.zero) True.intro) : Nat"),
  ("coeStuck/explicitMotiveN", "axiom ce5 (β : Type) (k : β → Nat) (h : Eq (natElim (motive := fun _ => β) x (fun _ ih => ih) Nat.zero) x) : Nat"),
  ("coeStuck/elimNamed", "axiom ce6 (β : Type) (z : True) (h : Eq (Eq.subst' (α := β) (a := x) (b := x) rfl z : True) z) : Nat"),
  ("coeStuck/elimNamedDef", "def ce7 (β : Type) (z : True) (h : Eq (Eq.subst' (α := β) (a := x) (b := x) rfl z : True) z) : Nat := Nat.zero"),
  ("coeStuck/elimMajor", "axiom ce8 (β : Type) (z : True) (e : @Eq β y y) (h : Eq (Eq.subst' (a := x) e z : True) z) : Nat"),
  ("coeStuck/elimRefl", "axiom ce9 (β : Type) (z : True) (h : Eq (Eq.subst' (α := β) (a := x) (b := x) (Eq.refl x) z : True) z) : Nat"),
  ("auto/levelNegBody", "def an8 (α : Sort u) : Nat := (fun (_ : Sort v) => Nat.zero) Nat"),
  ("auto/catchOverload", "namespace A\ndef k (n : Nat) : Nat := n\nend A\nnamespace B\ndef k (b : Bool) : Bool := b\nend B\nopen A B\ndef ac1 (h : Eq (k x) (k x)) : Nat := Nat.zero"),
  ("auto/catchCoe", "axiom ac2 (h : Eq (takesInt x) (takesInt x)) : Nat"),
  ("auto/catchAnon", "axiom ac3 (h : Eq ⟨a, b⟩ c) : Nat"),
  ("auto/catchFun", "axiom ac4 (h : Eq (fun y => y) x) : Nat"),
  ("auto/catchInst", "axiom ac5 (h : Eq (Wrap.val (x : α)) x) : Nat"),
  ("auto/catchNum", "axiom ac6 (h : Eq 2 x) : Nat"),
  ("opt/offDef", "set_option autoImplicit false\ndef ao1 (x : α) : α := x"),
  ("opt/offIn", "set_option autoImplicit false in\ndef ao2 (x : α) : α := x"),
  ("opt/offInScoped", "set_option autoImplicit false in\ndef ao3 : Nat := Nat.zero\ndef ao4 (x : α) : α := x"),
  ("opt/offSection", "section\nset_option autoImplicit false\nend\ndef ao5 (x : α) : α := x"),
  ("opt/offNamespace", "namespace M\nset_option autoImplicit false\nend M\ndef ao5b (x : α) : α := x"),
  ("opt/offThenOn", "set_option autoImplicit false\nset_option autoImplicit true\ndef ao5c (x : α) : α := x"),
  ("opt/strictOk", "set_option relaxedAutoImplicit false\ndef ao6 (x : α₁) (y : X12) (z : β') : α₁ := x"),
  ("opt/strictBad", "set_option relaxedAutoImplicit false\ndef ao7 (x : foo) : Nat := Nat.zero"),
  ("opt/strictLevelUpper", "set_option relaxedAutoImplicit false\ndef ao8 (α : Sort U) : Nat := Nat.zero"),
  ("opt/strictLevelOk", "set_option relaxedAutoImplicit false\ndef ao8b (α : Sort u1) : Nat := Nat.zero"),
  ("opt/strictLevelLong", "set_option relaxedAutoImplicit false\ndef ao8c (α : Sort uv) : Nat := Nat.zero"),
  ("opt/offLevel", "set_option autoImplicit false\ndef ao9 (α : Sort u) : Nat := Nat.zero"),
  ("opt/offAxiom", "set_option autoImplicit false\naxiom ao10 (x : α) : Nat"),
  ("opt/offMvar", "set_option autoImplicit false\ntheorem ao11 : Eq a a := rfl"),
  ("opt/badValue", "set_option autoImplicit 1"),
  ("opt/offForbidden", "set_option autoImplicit false\ndef ao12 (x : ao12) : Nat := Nat.zero"),
  ("opt/offDotted", "set_option autoImplicit false\ndef ao13 (x : Foo.bar) : Nat := Nat.zero"),
  ("opt/strictOffBoth", "set_option autoImplicit false\nset_option relaxedAutoImplicit false\ndef ao14 (x : foo) : Nat := Nat.zero"),
  ("auto/levelThenIdent", "def al13 (α : Sort u) (x : β) (a : α) : α := a"),
  ("auto/levelThenIdentThm", "theorem al14 (α : Sort u) (x : β) (a : α) : Eq a a := rfl"),
  ("auto/identBodyUse", "def ai16 (x : α) : List α := List.cons x List.nil"),
  ("auto/identBodyLam", "def ai17 (x : α) : α := (fun (y : α) => y) x"),
  ("auto/withUnusedVar", "variable (n : Nat)\ntheorem ai19 (x : α) : Eq x x := rfl"),
  ("auto/withUsedVar", "variable {β : Type} (b : β)\ndef ai20 (x : α) : PProd α β := PProd.mk x b"),
  ("auto/withUsedVarThm", "variable {β : Type} (b : β)\ntheorem ai21 (x : α) : Eq (PProd.mk x b) (PProd.mk x b) := rfl"),
  ("auto/withScopeUniverse", "universe u\ndef ai22 (x : α) (β : Sort u) : α := x"),
  ("auto/levelSameAsScope", "universe u\ndef al15 (α : Sort u) (a : α) : α := a"),
  ("auto/mvarAndIdent", "axiom am8 (x : γ) (h : Eq a b) : Nat"),
  ("auto/mvarLevelThm", "theorem am9 (h : Eq a b) : Eq a b := h"),
  ("auto/identShadowGlobal", "def pick2 (x : pick) : Nat := Nat.zero"),
  ("opt/inThenScoped", "set_option autoImplicit false in\ntheorem ao15 : Eq Nat.zero Nat.zero := rfl\ntheorem ao16 : Eq a a := rfl"),
  ("opt/sectionOffInside", "section\nset_option autoImplicit false\ndef ao17 (x : α) : α := x"),
  ("opt/strictSubscript", "set_option relaxedAutoImplicit false\ndef ao18 (x : α_1) (y : αᵢ) : α_1 := x"),
  ("opt/strictDotted", "set_option relaxedAutoImplicit false\ndef ao19 (x : A.b) : Nat := Nat.zero"),
  ("opt/offRelaxedOff", "set_option relaxedAutoImplicit false\nset_option autoImplicit false\ndef ao20 (x : α) : Nat := Nat.zero"),
  ("auto/levelAxiomOrder", "axiom al16 (α : Sort v) (β : Sort u) : α"),
  ("auto/levelThmOrder", "theorem al17 (α : Sort v) (β : Sort u) (a : α) : Eq a a := rfl"),
  ("auto/levelDefOrderUnusedVal", "def al18 (α : Sort v) (β : Sort u) : Nat := Nat.zero"),
  ("auto/levelAxiomExplicit", "axiom al19.{w} (α : Sort v) (β : Sort w) : α"),
  ("auto/identNestedBinder", "axiom ai26 (g : ∀ (y : Nat), Eq y z) : Nat"),
  ("auto/negThmBody", "theorem an9 (x : α) : Eq x x := zz"),
  ("auto/withSectionShadow", "variable (α : Type)\ndef ai24 (x : α) : α := x"),
  ("auto/identThirty", "axiom ai27 (x0 : t0) (x1 : t1) (x2 : t2) (x3 : t3) (x4 : t4) (x5 : t5) (x6 : t6) (x7 : t7) (x8 : t8) (x9 : t9) (x10 : t10) (x11 : t11) (x12 : t12) (x13 : t13) (x14 : t14) (x15 : t15) (x16 : t16) (x17 : t17) (x18 : t18) (x19 : t19) (x20 : t20) (x21 : t21) (x22 : t22) (x23 : t23) (x24 : t24) (x25 : t25) (x26 : t26) (x27 : t27) (x28 : t28) (x29 : t29) : Nat"),
  ("auto/levelOverloadNamedLeak", "namespace A\ndef f.{w1, w2} (a : Type w1) (b : Type w2) : Type := Nat\nend A\nnamespace B\ndef f.{w2} (b : Type w2) : Type := Nat\nend B\nopen A B\ndef g (h : f (a := Sort u) (b := Sort v)) : Nat := Nat.zero"),
  ("auto/levelOverloadNamedLeakThm", "namespace A\ndef f.{w1, w2} (a : Type w1) (b : Type w2) : Type := Nat\nend A\nnamespace B\ndef f.{w2} (b : Type w2) : Type := Nat\nend B\nopen A B\ntheorem g (h : f (a := Sort u) (b := Sort v)) : Eq h h := rfl"),
  ("auto/levelOverloadMismatchLeak", "namespace A\ndef f.{w1, w2} (a : Type w1) (b : Type w2) : Type := Nat\nend A\nnamespace B\ndef f (b : Type 5) (a : Type 6) : Type := Nat\nend B\nopen A B\ndef g (h : f (a := Sort u) (b := Sort v)) : Nat := Nat.zero"),
  ("varAuto/def", "variable (x : α)\ndef va1 : α := x"),
  ("varAuto/afterExplicit", "variable (n : Nat) (x : α)\ndef va2 : PProd Nat α := PProd.mk n x"),
  ("varAuto/twoCmds", "variable (x : α)\nvariable (y : β)\ndef va3 : PProd α β := PProd.mk x y"),
  ("varAuto/interleave", "variable (x : α)\nvariable (n : Nat) (y : β)\ndef va4 : PProd α β := PProd.mk x y"),
  ("varAuto/interleaveN", "variable (x : α)\nvariable (n : Nat) (y : β)\ndef va5 : PProd Nat β := PProd.mk n y"),
  ("varAuto/share", "variable (x : α)\nvariable (y : α)\ndef va6 : PProd α α := PProd.mk x y"),
  ("varAuto/unused", "variable (x : α)\ndef va7 : Nat := Nat.zero"),
  ("varAuto/thmUnused", "variable (x : α)\ntheorem va8 : True := True.intro"),
  ("varAuto/thmViaDep", "variable (x : α)\ntheorem va9 : Eq x x := rfl"),
  ("varAuto/headerAutoAfter", "variable (x : α)\ndef va10 (y : β) : PProd α β := PProd.mk x y"),
  ("varAuto/headerSameName", "variable (x : α)\ndef va11 (y : α) : α := y"),
  ("varAuto/headerSameNameNew", "variable (x : α)\ndef va12 (y : α) (z : β) : β := z"),
  ("varAuto/thmHeaderAuto", "variable (x : α)\ntheorem va13 (y : γ) : Eq x x := rfl"),
  ("varAuto/inst", "variable [Wrap α] (x : α)\ndef va14 : α := x"),
  ("varAuto/sectionEnd", "section\nvariable (x : α)\nend\ndef va15 : Nat := Nat.zero"),
  ("varAuto/secShadow", "variable (α : Type)\nvariable (x : α)\ndef va16 : α := x"),
  ("varAuto/notClass", "variable [Foo α]"),
  ("varAuto/thirty", "variable (x0 : t0) (x1 : t1) (x2 : t2) (x3 : t3) (x4 : t4) (x5 : t5) (x6 : t6) (x7 : t7) (x8 : t8) (x9 : t9) (x10 : t10) (x11 : t11) (x12 : t12) (x13 : t13) (x14 : t14) (x15 : t15) (x16 : t16) (x17 : t17) (x18 : t18) (x19 : t19) (x20 : t20) (x21 : t21) (x22 : t22) (x23 : t23) (x24 : t24) (x25 : t25) (x26 : t26) (x27 : t27) (x28 : t28) (x29 : t29)\ndef va18 : Nat := Nat.zero"),
  ("varAuto/includeAuto", "variable (x : α)\ninclude α"),
  ("varAuto/includeX", "variable (x : α)\ninclude x\ntheorem va19 : True := True.intro"),
  ("varAuto/omitAuto", "variable (x : α)\nomit α"),
  ("varAuto/omitReferenced", "variable (x : α)\nomit x\ntheorem va21 : Eq x x := rfl"),
  ("varAuto/omitInstKept", "variable [inst : Wrap Nat]\nomit inst\nvariable (x : α)\ntheorem va22 : True := True.intro"),
  ("varAuto/omitTypeAuto", "variable [Wrap α] (x : α)\nomit [Wrap α]\ntheorem va60 (y : α) : True := True.intro"),
  ("varAuto/omitTypeUnknown", "variable (x : α)\nomit [Wrap β]"),
  ("varAuto/level", "variable (α : Sort u) (a : α)\ndef va23 : α := a"),
  ("varAuto/levelScope", "universe v\nvariable (α : Sort u) (β : Sort v) (a : α) (b : β)\ndef va24 : PProd α β := PProd.mk a b"),
  ("varAuto/levelThm", "variable (α : Sort u) (a : α)\ntheorem va25 : Eq a a := rfl"),
  ("varAuto/levelUnused", "variable (α : Sort u)\ndef va26 : Nat := Nat.zero"),
  ("varAuto/levelHeader", "variable (α : Sort u)\ndef va27 (β : Sort v) (a : α) (b : β) : α := a"),
  ("varAuto/levelAxiom", "variable (α : Sort u) (a : α)\naxiom va28 : Eq a a"),
  ("varAuto/off", "set_option autoImplicit false\nvariable (x : α)"),
  ("varAuto/offLevel", "set_option autoImplicit false\nvariable (α : Sort u)"),
  ("varAuto/strict", "set_option relaxedAutoImplicit false\nvariable (x : foo)"),
  ("varAuto/strictOk", "set_option relaxedAutoImplicit false\nvariable (x : α₁)\ndef va32 : α₁ := x"),
  ("varAuto/offAfter", "variable (x : α)\nset_option autoImplicit false\ndef va33 : α := x"),
  ("varAuto/offIn", "set_option autoImplicit false in\nvariable (x : α)"),
  ("varAuto/offInThenOn", "set_option autoImplicit false in\nvariable (n : Nat)\nvariable (x : α)\ndef va35 : α := x"),
  ("varAuto/dotted", "variable (x : Foo.bar)"),
  ("varAuto/rebuildBodyUnknown", "variable (h : Eq a a)\ntheorem va37 : Eq a a := h"),
  ("varAuto/rebuildHeaderUse", "variable (h : Eq a a)\ntheorem va38 (k : Eq h h) : True := True.intro"),
  ("varAuto/rebuildDef", "variable (h : Eq a a)\ndef va39 : Eq a a := h"),
  ("varAuto/rebuildDefUse", "variable (h : Eq a a)\ndef va40 (k : Eq h h) : Nat := Nat.zero"),
  ("varAuto/rebuildDefBody", "variable (h : Eq a a)\ndef va41 : Nat := (fun (_ : Eq a a) => Nat.zero) h"),
  ("varAuto/rebuildInclude", "variable (h : Eq a a) (n : Nat)\ninclude n\ntheorem va42 : True := True.intro"),
  ("varAuto/rebuildIncludeH", "variable (h : Eq a a)\ninclude h\ntheorem va43 : True := True.intro"),
  ("varAuto/rebuildOmitName", "variable (h : Eq a a) (n : Nat)\nomit n"),
  ("varAuto/rebuildOmitAutoName", "variable (h : Eq a a)\nomit a"),
  ("varAuto/rebuildOmitMvarName", "variable (h : Eq a a)\nomit α"),
  ("varAuto/rebuildOmitType", "variable (h : Eq a a) (n : Nat)\nomit [Wrap Nat]"),
  ("varAuto/rebuildOmitRefH", "variable (h : Eq a a) (n : Nat)\ninclude n\nomit h"),
  ("varAuto/rebuildOmitInstIgnored", "variable [inst : Wrap Nat]\nomit inst\nvariable (h : Eq a a)\ntheorem va49 : True := True.intro"),
  ("varAuto/rebuildInst", "variable (h : Eq a a) [Wrap Nat]\ntheorem va50 (k : Wrap Nat) : True := True.intro"),
  ("varAuto/rebuildInstAuto", "variable {β : Type} (h : Eq a a) [Wrap β] (y : β)\ntheorem va51 : Eq y y := rfl"),
  ("varAuto/rebuildTwoCmds", "variable (h : Eq a a)\nvariable (n : Nat)\ndef va52 : Nat := n"),
  ("varAuto/rebuildBadLater", "variable (h : Eq a a)\nvariable (n : zz.yy)"),
  ("varAuto/rebuildHEq", "variable (h : HEq a b)\ntheorem va54 (k : Eq h h) : True := True.intro"),
  ("varAuto/rebuildExample", "variable (h : Eq a a)\nexample : Nat := Nat.zero"),
  ("varAuto/rebuildAxiom", "variable (h : Eq a a)\naxiom va56 (k : Eq h h) : Nat"),
  ("varAuto/rebuildInstMvar", "variable (h : Eq a a) [Wrap α]"),
  ("varAuto/rebuildNamedMvar", "variable (h : Eq a a)\ntheorem va58 (k : Eq h h) : True := True.intro\nexample : True := va58 (α := Nat)"),
  ("varAuto/rebuildNamedAuto", "variable (h : Eq a a)\ntheorem va59 (k : Eq h h) : True := True.intro\nexample : True := va59 (a := Nat.zero) rfl rfl"),
  ("varAuto/rebuildSectionEnd", "section\nvariable (h : Eq a a)\nend\nvariable (n : Nat)\ninclude n\ntheorem va61 : True := True.intro"),
  ("varAuto/rebuildHeaderAlpha", "variable (h : Eq a a)\ndef va62 (x : α) : α := x"),
  ("varAuto/rebuildHeaderAlphaThm", "variable (h : Eq a a)\ntheorem va63 (x : α) (k : Eq h h) : Eq x x := rfl"),
  -- Meta's `Level.normalize` (Level.lean:382, pure Lean) is not the kernel's
  -- (level.cpp:439): left-nested `accMax` rebuild, `ctorToNat` order
  -- (param < imax), and `Name.lt`. `Eq`'s level is unified while PProd.mk's
  -- level mvars are still open (eqMk*), or after they are assigned (eqFVar*,
  -- nest3, imaxOrder, ...), and both paths go through isLevelDefEqAux's normalize.
  ("lvl/eqMk", "axiom lv1 {α : Sort u} {β : Type} (x : α) (b : β) : Eq (PProd.mk x b) (PProd.mk x b)"),
  ("lvl/eqMkThm", "theorem lv2 {α : Sort u} {β : Type} (x : α) (b : β) : Eq (PProd.mk x b) (PProd.mk x b) := rfl"),
  ("lvl/eqMkDef", "def lv3 {α : Sort u} {β : Type} (x : α) (b : β) : Eq (PProd.mk x b) (PProd.mk x b) := rfl"),
  ("lvl/eqMkHole", "theorem lv4 {α : Sort _} {β : Type} (x : α) (b : β) : Eq (PProd.mk x b) (PProd.mk x b) := rfl"),
  ("lvl/eqFVar", "axiom lv5 {α : Sort u} {β : Type} (p : PProd α β) : Eq p p"),
  ("lvl/eqFVarRev", "axiom lv6 {α : Sort u} {β : Type} (p : PProd β α) : Eq p p"),
  ("lvl/nest3", "axiom lv7 {α : Sort u} {β : Sort v} {γ : Sort w} (p : PProd α (PProd β γ)) : Eq p p"),
  ("lvl/nest3Mk", "axiom lv8 {α : Sort u} {β : Sort v} {γ : Sort w} (x : α) (y : β) (z : γ) : Eq (PProd.mk x (PProd.mk y z)) (PProd.mk x (PProd.mk y z))"),
  ("lvl/imaxOrder", "axiom lv9 {α : Sort u} {β : Sort v} (p : PProd (α → β) α) : Eq p p"),
  ("lvl/succSubsumes", "axiom lv10 {α : Type u} (p : PProd α α) : Eq p p"),
  ("lvl/paramOrder", "axiom lv11 {α : Sort v} {β : Sort u} (p : PProd α β) : Eq p p"),
  -- recursor (elab-as-elim) heads: `PProd.rec` has three level params
  ("lvl/elimRec3", "axiom lv12 {α : Sort u} {β : Sort v} {γ : Sort w} (p : PProd α (PProd β γ)) : Eq (PProd.rec (motive := fun _ => PProd β γ) (fun _ b => b) p) p.2"),
  ("lvl/elimRecHole", "axiom lv13 {α : Sort u} {β : Sort v} {γ : Sort w} (p : PProd α (PProd β γ)) : Eq (PProd.rec (motive := fun _ => _) (fun a b => PProd.mk b a) p) (PProd.mk p.2 p.1)"),
  ("lvl/elimRecSwap", "theorem lv14 {α : Sort u} {β : Sort v} (p : PProd α β) : Eq (PProd.rec (motive := fun _ => PProd β α) (fun a b => PProd.mk b a) p) (PProd.mk p.2 p.1) := Eq.refl _"),
  ("lvl/elimRecNest", "theorem lv15 {α : Sort u} {β : Sort v} {γ : Sort w} (p : PProd α (PProd β γ)) : Eq (PProd.rec (motive := fun _ => PProd (PProd γ β) α) (fun a b => PProd.mk (PProd.mk b.2 b.1) a) p) (PProd.mk (PProd.mk p.2.2 p.2.1) p.1) := Eq.refl _"),
  -- worktree A: unknown constant / synth / invalid field
  ("unkConst/structPrefix", "def uc1 : Nat := Tag.nope"),
  ("unkConst/classPrefix", "def uc2 : Nat := Wrap.val"),
  ("unkConst/inductivePrefix", "def uc3 : Nat := Nat.nope"),
  ("unkConst/boolPrefix", "def uc4 : Bool := Bool.nope"),
  ("unkConst/defPrefix", "def uc5 : Nat := pick.nope"),
  ("unkConst/polyPrefix", "def uc6 : Nat := PProd.nope"),
  ("unkConst/twoFields", "def uc7 : Nat := Nat.nope.more"),
  ("unkConst/applied", "def uc8 : Nat := Nat.nope Nat.zero"),
  ("unkConst/axiomBinder", "axiom uc9 (h : Wrap.val Nat) : Nat"),
  ("unkConst/thmType", "theorem uc10 : Nat.nope := rfl"),
  ("unkConst/ctorValue", "def uc11 : Nat := Nat.zero.nope"),
  ("unkConst/instValue", "def uc12 : Nat := instWrapNat.nope"),
  ("unkConst/localNat", "def uc13 (x : Nat) : Nat := x.nope"),
  ("unkConst/localType", "def uc14 (x : Type) : x := x.nope"),
  ("unkConst/unknownPrefix", "def uc15 : Nat := Foo.bar"),
  ("synthFail/noInst", "def sf1 : Nat := useNoInst Nat.zero"),
  ("synthFail/wrapBool", "def sf2 : Bool := Wrap.wrap (a := Bool) Bool.true"),
  ("synthFail/pairBoolNat", "def sf3 : Bool := usePair Bool.true Nat.zero"),
  ("synthFail/thm", "theorem sf4 : Eq (useNoInst Nat.zero) Nat.zero := rfl"),
  ("synthFail/binder", "def sf5 (h : Eq (useNoInst Nat.zero) Nat.zero) : Nat := Nat.zero"),
  ("synthFail/axiom", "axiom sf6 : Eq (useNoInst Nat.zero) Nat.zero"),
  ("synthFail/explicitHole", "def sf7 : Nat := @useNoInst Nat _ Nat.zero"),
  ("synthFail/afterOk", "def sf8 : Nat := Nat.zero\ndef sf9 : Nat := useNoInst sf8"),
  ("unkConst/parenSort", "def uc17 : Nat := (Nat).nope"),
  ("unkConst/parenFun", "def uc18 : Nat := (pick).nope"),
  -- worktree C: variable binder-annotation update (`replaceBinderAnnotation`,
  -- typed variables only; typeless binders wait on the `expandBinderType` hole)
  ("vu/implicit", "variable (x : Nat)\nvariable {x}\ndef u1 : Nat := x"),
  ("vu/explicit", "variable {x : Nat}\nvariable (x)\ndef u2 : Nat := x"),
  ("vu/strict", "variable (x : Nat)\nvariable ⦃x⦄\ndef u3 : Nat := x"),
  ("vu/instUp", "variable (a : Type) (w : Wrap a)\nvariable [w]\ndef u4 (y : a) : a := Wrap.wrap y"),
  ("vu/instDown", "variable (a : Type) [w : Wrap a]\nvariable (w)\ndef u5 (y : a) : a := Wrap.wrap y"),
  ("vu/redundant", "variable {x : Nat}\nvariable {x}"),
  ("vu/split", "variable (x y : Nat)\nvariable {x}\ndef u8 : PProd Nat Nat := PProd.mk x y"),
  ("vu/instInvalid", "variable (x : Nat)\nvariable [x]"),
  ("vu/section", "variable (x : Nat)\nsection\nvariable {x}\ndef u12a : Nat := x\nend\ndef u12b : Nat := x"),
  ("vu/shadow", "variable (x : Nat)\nvariable (x : Nat)\nvariable {x}\ndef u13 : Nat := x"),
  ("vu/dependent", "variable (a : Type) (x : a)\nvariable {a}\ndef u14 : a := x"),
  ("vu/autoBound", "variable (x : α)\nvariable {x}\ndef u15 : α := x"),
  ("vu/include", "variable (x : Nat)\ninclude x\nvariable {x}\ntheorem u16 : Eq Nat.zero Nat.zero := rfl"),
  ("vu/instTheorem", "variable (a : Type) (w : Wrap a)\nvariable [w]\ntheorem u17 (y : a) : Eq y y := rfl"),
  ("vu/mixed", "variable (x : Nat)\nvariable {x} (n : Nat)\ndef u18 : PProd Nat Nat := PProd.mk x n"),
  ("vu/twoBinders", "variable {x y : Nat}\nvariable (x) {y}"),
  ("vu/instToImplicit", "variable (a : Type) [w : Wrap a]\nvariable {w}\ndef u21 (y : a) : a := @Wrap.wrap a w y"),
  ("vu/omitThenUpdate", "variable (a : Type) [w : Wrap a]\nomit w\nvariable {w}\ntheorem u22 (y : a) : Eq y y := rfl"),
  ("vu/updateThenUse", "variable (x : Nat)\nvariable {x}\ndef u23 : Nat := x\ndef u24 : Nat := u23"),
  ("vu/instAnonUnaffected", "variable (a : Type) [Wrap a]\nvariable {a}\ntheorem u26 (y : a) : Eq y y := rfl"),
  ("vu/omitInst", "variable (a : Type) (w : Wrap a)\nomit w\nvariable [w]\ntheorem u28 (y : a) : Eq y y := rfl"),
  ("vu/order", "variable (x : Nat) (y : Nat)\nvariable {x}\ndef u30 : PProd Nat Nat := PProd.mk y x"),
  ("vu/instTwice", "variable (a : Type) (w : Wrap a)\nvariable [w]\nvariable [w]"),
  ("vu/strictToImplicit", "variable ⦃x : Nat⦄\nvariable {x}\ndef u31 : Nat := x"),
  ("vu/seqInCmd", "variable (x : Nat)\nvariable {x} (x)\ndef u32 : Nat := x"),
  ("vu/shadowRedundant", "variable {x : Nat}\nvariable (x : Nat)\nvariable {x}\ndef u33 : Nat := x"),
  ("vu/instDownTheorem", "variable (a : Type) [w : Wrap a]\nvariable (w)\ntheorem u34 (y : a) : Eq y y := rfl"),
  ("vu/updateDepInst", "variable (a : Type) [w : Wrap a]\nvariable {a}\ntheorem u35 (y : a) : Eq y y := rfl"),
  -- worktree B: term-level open … in (`elabOpen`, BuiltinTerm.lean:400-408)
  ("tOpen/simple", "def t1 : Nat := open Nat in zero"),
  ("tOpen/binderType", "namespace N\ndef T : Type := Nat\nend N\ndef t2 (x : open N in T) : Nat := x"),
  ("tOpen/only", "namespace A\ndef a1 : Nat := Nat.zero\ndef a2 : Nat := Nat.zero\nend A\ndef t3 : Nat := open A (a1) in a1"),
  ("tOpen/onlyOther", "namespace A\ndef a1 : Nat := Nat.zero\ndef a2 : Nat := Nat.zero\nend A\ndef t4 : Nat := open A (a1) in a2"),
  ("tOpen/hidingOk", "namespace A\ndef a1 : Nat := Nat.zero\ndef a2 : Nat := Nat.zero\nend A\ndef t5 : Nat := open A hiding a1 in a2"),
  ("tOpen/hidingHidden", "namespace A\ndef a1 : Nat := Nat.zero\ndef a2 : Nat := Nat.zero\nend A\ndef t6 : Nat := open A hiding a1 in a1"),
  ("tOpen/renaming", "namespace A\ndef a1 : Nat := Nat.zero\nend A\ndef t7 : Nat := open A renaming a1 → b in b"),
  ("tOpen/renamingOld", "namespace A\ndef a1 : Nat := Nat.zero\nend A\ndef t8 : Nat := open A renaming a1 → b in a1"),
  ("tOpen/scopeEnds", "def t9 : PProd Nat Nat := PProd.mk (open Nat in zero) zero"),
  ("tOpen/nested", "namespace A.B\ndef c : Nat := Nat.zero\nend A.B\ndef t10 : Nat := open A in open B in c"),
  ("tOpen/nestedNoOuter", "namespace A.B\ndef c : Nat := Nat.zero\nend A.B\ndef t11 : Nat := open B in c"),
  ("tOpen/ambiguous", "namespace A\ndef f : Nat := Nat.zero\nend A\nnamespace B\ndef f : Nat := Nat.zero\nend B\ndef t12 : Nat := open A B in f"),
  ("tOpen/unknownNs", "def t13 : Nat := open Foo in Nat.zero"),
  ("tOpen/postponed", "def sel {a : Type} (x y : a) : a := x\ndef t14 := sel (open Nat in ⟨zero, zero⟩) (PProd.mk Nat.zero Nat.zero)"),
  ("tOpen/postponedOutside", "def sel {a : Type} (x y : a) : a := x\ndef t15 := sel (open Nat in ⟨Nat.zero, Nat.zero⟩) (PProd.mk zero Nat.zero)"),
  ("tOpen/withCmdOpen", "namespace A\ndef a1 : Nat := Nat.zero\nend A\nopen A\ndef t16 : PProd Nat Nat := open Nat in PProd.mk a1 zero"),
  ("tOpen/inNamespace", "namespace A.B\ndef c : Nat := Nat.zero\nend A.B\nnamespace A\ndef t17 : Nat := open B in c\nend A"),
  ("tOpen/afterCmd", "def t19 : Nat := open Nat in zero\ndef t20 : Nat := zero"),
  ("tOpen/onlyAmbig", "namespace A\ndef f : Nat := Nat.zero\nend A\nnamespace B\ndef f : Nat := Nat.zero\nend B\ndef t21 : Nat := open A B in open A (f) in f"),
  ("tOpen/thm", "theorem t22 : Eq Nat.zero Nat.zero := open Nat in @rfl Nat zero"),
  ("tOpen/postponedBefore", "def sel {a : Type} (x y : a) : a := x\ndef t23 := sel ⟨zero, zero⟩ (open Nat in PProd.mk zero zero)"),
  ("tOpen/postponedBeforeOk", "def sel {a : Type} (x y : a) : a := x\ndef t24 := sel ⟨Nat.zero, Nat.zero⟩ (open Nat in PProd.mk zero zero)"),
  ("tOpen/postponedNested", "def sel {a : Type} (x y : a) : a := x\ndef t25 := open Nat in sel ⟨zero, zero⟩ (PProd.mk zero zero)"),
  ("tOpen/resumeNoLeak", "def sel {a : Type} (x y : a) : a := x\ndef t26 (h : Eq (sel (open Nat in ⟨zero, zero⟩) (PProd.mk Nat.zero Nat.zero)) (PProd.mk Nat.zero Nat.zero)) : Nat := zero"),
  ("tOpen/resumeNoLeakOk", "def sel {a : Type} (x y : a) : a := x\ndef t27 (h : Eq (sel (open Nat in ⟨zero, zero⟩) (PProd.mk Nat.zero Nat.zero)) (PProd.mk Nat.zero Nat.zero)) : Nat := Nat.zero"),
  ("tOpen/dotIdent", "def t28 : Nat := open Nat in .zero"),
  ("tOpen/dotIdentArg", "def t29 : PProd Nat Nat := PProd.mk (open Nat in .zero) Nat.zero"),
  ("tOpen/orderAmbig", "namespace A.X\ndef p : Nat := Nat.zero\nend A.X\nnamespace B.X\ndef p : Nat := Nat.zero\nend B.X\ndef t30 : Nat := open A B in open X hiding p in Nat.zero"),
  -- worktree D: letToHave (nondependent `let` → `have`; spec 2026-10-07-let-to-have-design.md)
  ("lth/defVal", "def d1 : Nat := let x := Nat.zero; x"),
  ("lth/defHave", "def d2 : Nat := have x := Nat.zero; x"),
  ("lth/defDep", "def d3 : Nat := let T := Nat; (Nat.zero : T)"),
  ("lth/defDepRfl", "def d4 : Eq Nat.zero Nat.zero := let x := Nat.zero; (rfl : Eq x Nat.zero)"),
  ("lth/defNested", "def d5 : Nat := let x := Nat.zero; let y := x; y"),
  ("lth/defNestedDep", "def d6 : Nat := let T := Nat; let y : T := Nat.zero; y"),
  ("lth/defLam", "def d7 : Nat -> Nat := fun n => let x := n; x"),
  ("lth/defLamDep", "def d8 : Nat -> Nat := fun n => let T := Nat; (n : T)"),
  ("lth/defType", "def d9 : (let T := Nat; T) := Nat.zero"),
  ("lth/defTypeArrow", "def d10 : (let T := Nat; T -> T) := fun x => x"),
  ("lth/thmVal", "theorem t1 : Eq Nat.zero Nat.zero := let x := Nat.zero; rfl"),
  ("lth/thmValDep", "theorem t2 : Eq Nat.zero Nat.zero := let x := Nat.zero; (rfl : Eq x x)"),
  ("lth/thmType", "theorem t3 : (let x := Nat.zero; Eq x x) := rfl"),
  ("lth/abbrev", "abbrev a1 : Nat := let x := Nat.zero; x"),
  ("lth/example", "example : Nat := let x := Nat.zero; x"),
  ("lth/opaque", "opaque o1 : Nat := let x := Nat.zero; x"),
  ("lth/opaqueType", "opaque o2 : (let T := Nat; T) := Nat.zero"),
  ("lth/propDef", "def p1 : Eq Nat.zero Nat.zero := let x := Nat.zero; rfl"),
  ("lth/axiomType", "axiom ax1 : (let T := Nat; T)"),
  ("lth/letProofVal", "def d11 : Nat := let h : Eq Nat.zero Nat.zero := rfl; Nat.zero"),
  ("lth/unusedLet", "def d12 : Nat := let x := Bool.true; Nat.zero"),
  ("lth/letInArg", "def d13 : Nat := pick (let x := Nat.zero; x) Nat.zero"),
  ("lth/depAfterNondep", "def d14 : Nat := let x := Nat.zero; let T := Nat; (x : T)"),
  ("lth/exampleType", "example : (let T := Nat; T) := Nat.zero"),
  ("lth/defLetTypeOnly", "def d15 : Nat := let x : Nat := Nat.zero; Nat.zero"),
  ("lth/nonPropDep", "def d17 : PProd (Eq Nat.zero Nat.zero) Nat := let x := Nat.zero; PProd.mk (rfl : Eq x Nat.zero) x"),
  ("lth/nonPropDepIdx", "def d19 : PProd Nat Nat := let x := Nat.zero; let y := x; PProd.mk x Nat.zero"),
  ("lth/lamBinderDep", "def d20 : Nat := let T := Nat; (fun (z : T) => z) Nat.zero"),
  ("lth/proofArgDep", "def d21 : Nat := let x := Nat.zero; PProd.fst (PProd.mk x (rfl : Eq x x))"),
  ("lth/proofArgNoDep", "def d22 : Nat := let x := Nat.zero; PProd.fst (PProd.mk x (rfl : Eq Nat.zero Nat.zero))"),
  ("lth/proofInLetVal", "def d23 : PProd Nat (Eq Nat.zero Nat.zero) := let p := PProd.mk Nat.zero (rfl : Eq Nat.zero Nat.zero); p"),
  ("lth/letInLetVal", "def d24 : Nat := let x := (let y := Nat.zero; y); x"),
  ("lth/letInBinderType", "def d25 : (n : (let T := Nat; T)) -> Nat := fun n => n"),
  ("lth/haveDep", "def d26 : Nat := have x := Nat.zero; let T := Nat; (x : T)"),
  ("lth/sameNameTwice", "def d27 : Nat := let x := Nat.zero; let x := x; x"),
  ("lth/thmHeaderAsync", "theorem t4 : (let x := Nat.zero; Eq x Nat.zero) := rfl"),
  ("lth/lamTypeDep", "def d32 : Nat -> Nat := let T := Nat; fun (z : T) => z"),
  ("lth/letTypeAnn", "def d33 : Nat := let T : Type := Nat; let y : T := Nat.zero; Nat.zero"),
  ("lth/auxProofHave", "def d35 : PProd Nat Nat := have x := Nat.zero; PProd.mk Nat.zero (PProd.fst (PProd.mk x (eq_of_heq (HEq.refl x))))"),
  ("lth/auxProofOutsideLet", "def d36 : PProd Nat (Eq Nat.zero Nat.zero) := PProd.mk (let x := Nat.zero; x) (eq_of_heq (HEq.refl Nat.zero))"),
  ("lth/letUnderLamTypeOnly", "def d37 : Nat -> Nat := fun (n : (let T := Nat; T)) => n"),
  ("lth/auxProofInLetValue", "def d38 : Nat := let p := PProd.mk Nat.zero (eq_of_heq (HEq.refl Nat.zero)); PProd.fst p"),
  -- C1 (final review): a numeral let value whose `OfNat` instance is still
  -- pending when the body unifies `x` (isDefEqOnFailure/synthPending, not
  -- the class-singleton `OfNat.mk` solution)
  ("lth/numLetRfl", "def e6 : Nat := let x := 1; PProd.fst (PProd.mk x (rfl : Eq x (Nat.succ Nat.zero)))"),
  ("lth/numLetRflPick", "def m5 : Eq Nat.zero Nat.zero := let x := 1; PProd.fst (PProd.mk (rfl : Eq Nat.zero Nat.zero) (rfl : Eq x (Nat.succ (pick Nat.zero Nat.zero))))"),
  ("lth/numLetThm", "theorem e12 : Eq (Nat.succ Nat.zero) (Nat.succ Nat.zero) := let x := 1; (rfl : Eq x (Nat.succ Nat.zero))"),
  ("lth/numLetTwo", "def e15 : Nat := let x := 2; PProd.fst (PProd.mk x (rfl : Eq x (Nat.succ (Nat.succ Nat.zero))))"),
  ("lth/numLetChain", "def e16 : Nat := let x := 1; let y := x; PProd.fst (PProd.mk y (rfl : Eq y (Nat.succ Nat.zero)))"),
  ("lth/numHaveRfl", "def e8 : Nat := have x := 1; PProd.fst (PProd.mk x (Eq.refl x))"),
  ("lth/numLetTyped", "def e9 : Nat := let x : Nat := 1; PProd.fst (PProd.mk x (rfl : Eq x (Nat.succ Nat.zero)))"),
  ("lth/numNoLet", "def e7 : Nat := PProd.fst (PProd.mk 1 (rfl : Eq 1 (Nat.succ Nat.zero)))"),
  -- worktree A: in-file abbrev reducibility (`mkDefViewOfAbbrev` adds
  -- `@[reducible]`, DefView.lean:143-144): class-ness and instance
  -- defeq must see through an `abbrev` elaborated earlier in the file;
  -- the `def` rows are the semireducible controls
  ("abbrevRed/re3", "abbrev W2 := Wrap\nvariable (w : W2 Nat)\ndef re3 : Nat := Wrap.wrap Nat.zero"),
  ("abbrevRed/appliedAbbrevVar", "abbrev W3 (a : Type) := Wrap a\nvariable (w : W3 Nat)\ndef ar1 : Nat := Wrap.wrap Nat.zero"),
  ("abbrevRed/re2", "abbrev W2 := Wrap\ndef re2 [W2 Nat] : Nat := Nat.zero"),
  ("abbrevRed/abbrevOfAbbrev", "abbrev W2 := Wrap\nabbrev W5 := W2\ndef r1 [W5 Nat] : Nat := Nat.zero"),
  ("abbrevRed/nsAbbrev", "namespace N\nabbrev W := Wrap\nend N\ndef r2 [N.W Nat] : Nat := Nat.zero"),
  ("abbrevRed/dottedAbbrev", "abbrev M.W := Wrap\ndef ar2 [M.W Nat] : Nat := Nat.zero"),
  ("abbrevRed/typedAbbrev", "abbrev W7 : Type → Type := Wrap\ndef r10 [W7 Nat] : Nat := Nat.zero"),
  ("abbrevRed/appliedAbbrev", "abbrev W3 (a : Type) := Wrap a\ndef ar3 [W3 Nat] : Nat := Nat.zero"),
  ("abbrevRed/outParamAbbrev", "abbrev G := Get\ndef r5 [G Cell Nat Unit] : Nat := Nat.zero"),
  ("abbrevRed/outParamAbbrevUse", "abbrev G2 (c : Type) := Get c Nat\ndef r6 {e : Type} [G2 Cell e] (c : Cell) : Cell := getFst c"),
  ("abbrevRed/varInst", "abbrev W2 := Wrap\nvariable [w : W2 Nat]\ndef ar4 : Nat := Wrap.wrap Nat.zero"),
  ("abbrevRed/varUpd", "abbrev W2 := Wrap\nvariable (w : W2 Nat)\nvariable [w]\ndef ar5 : Nat := Wrap.wrap Nat.zero"),
  ("abbrevRed/anonVarInst", "abbrev W2 := Wrap\nvariable [W2 Nat]\ndef r7 : Nat := useWrap Nat.zero"),
  ("abbrevRed/useWrap", "abbrev W2 := Wrap\ndef ar6 [W2 Nat] (x : Nat) : Nat := useWrap x"),
  ("abbrevRed/argSynth", "abbrev N2 := Nat\ndef r3 (x : N2) : N2 := useWrap x"),
  ("abbrevRed/localInstDefeq", "abbrev N2 := Nat\ndef r9 [Wrap N2] (x : Nat) : Nat := useWrap x"),
  ("abbrevRed/abbrevInstVar", "abbrev N2 := Nat\nvariable [Wrap N2]\ndef r11 (x : Nat) : Nat := useWrap x"),
  ("abbrevRed/openInAbbrev", "open Wrap in abbrev W8 := Wrap\ndef ar7 [W8 Nat] : Nat := Nat.zero"),
  ("abbrevRed/defNotAbbrev", "def W4 := Wrap\nvariable (w : W4 Nat)\ndef ar8 : Nat := Wrap.wrap Nat.zero"),
  ("abbrevRed/localInstDefeqDef", "def N3 := Nat\ndef r9b [Wrap N3] (x : Nat) : Nat := useWrap x"),
  -- worktree A neighbours: numerals, coercions, lazy-delta and theorem
  -- types through an in-file abbrev (and their `def` controls)
  ("abbrevNb/numeral", "abbrev N2 := Nat\ndef nb1 : N2 := 1"),
  ("abbrevNb/numeralDef", "def N3 := Nat\ndef nb2 : N3 := 1"),
  ("abbrevNb/coeArg", "abbrev N2 := Nat\ndef nb3 (x : N2) : Int := takesInt x"),
  ("abbrevNb/coeAscr", "abbrev N2 := Nat\ndef nb4 (x : N2) : Int := x"),
  ("abbrevNb/coeArgDef", "def N3 := Nat\ndef nb5 (x : N3) : Int := takesInt x"),
  ("abbrevNb/coeTarget", "abbrev WN := Wrapper Nat\ndef nb6 (n : Nat) : WN := n"),
  ("abbrevNb/coeTargetDef", "def WD := Wrapper Nat\ndef nb6b (n : Nat) : WD := n"),
  ("abbrevNb/defeqUnfold", "abbrev F (x : Nat) := pick x x\ntheorem nb7 : Eq (F Nat.zero) (pick Nat.zero Nat.zero) := rfl"),
  ("abbrevNb/defeqUnfoldDef", "def F2 (x : Nat) := pick x x\ntheorem nb7b : Eq (F2 Nat.zero) Nat.zero := rfl"),
  ("abbrevNb/lazyDeltaMix", "abbrev F (x : Nat) := pick x x\ndef G (x : Nat) := F x\ntheorem nb8 : Eq (G Nat.zero) (F Nat.zero) := rfl"),
  ("abbrevNb/thmTypeOnly", "abbrev P := Eq Nat.zero Nat.zero\ntheorem nb9 : P := rfl"),
  ("abbrevNb/thmTypeOnlyDef", "def P2 := Eq Nat.zero Nat.zero\ntheorem nb10 : P2 := rfl"),
  ("abbrevNb/fieldNotation", "abbrev WN := Wrapper Nat\ndef nb11 (w : WN) : Nat := w.val"),
  ("abbrevNb/argAscribed", "abbrev N2 := Nat\ndef nb12 : N2 := useWrap (Nat.zero : N2)"),
  ("abbrevNb/outParamCont", "abbrev C2 := Cell\ndef nb13 (c : C2) : C2 := getFst c"),
  ("abbrevNb/univAbbrev", "abbrev PP.{u} (a : Type u) := PProd a a\ndef nb14 (x : PP Nat) : Nat := x.fst"),
  ("abbrevNb/autoBoundInst", "abbrev W2 := Wrap\ndef nb15 [W2 α] (x : α) : α := useWrap x"),
  ("abbrevNb/exampleInst", "abbrev W2 := Wrap\nexample [W2 Nat] : Nat := Nat.zero"),
  ("abbrevNb/varThm", "abbrev W2 := Wrap\nvariable {a : Type} [W2 a] (x : a)\ntheorem nb16 : Eq (useWrap x) (useWrap x) := rfl"),
  ("abbrevNb/secVarAbbrev", "variable (n : Nat)\nabbrev nb17 := pick n n\ndef nb18 : Nat := nb17 Nat.zero"),
  ("abbrevNb/instArgExplicit", "abbrev W2 := Wrap\ndef nb19 (w : W2 Nat) : Nat := @useWrap Nat w Nat.zero"),
  ("abbrevNb/binderTypeUnify", "abbrev N2 := Nat\ndef nb20 (f : N2 -> Nat) : Nat := f Nat.zero"),
  ("abbrevNb/abbrevProp", "abbrev Q := Eq Nat.zero Nat.zero\ndef nb21 (h : Q) : Eq Nat.zero Nat.zero := h"),
  -- worktree C: inferType rebuild of let/lambda telescopes
  -- (`inferLambdaType`'s `mkForallFVars`, MkBinding.mkBinding: a binder's
  -- type/value is abstracted at its own depth, and an outer let used ONLY
  -- by an inner binder's type/value is still kept)
  ("inferLet/chain", "def lt2 : Nat := let T := Nat; let U := T; let y : U := Nat.zero; y"),
  ("inferLet/chain3", "def c3 : Nat := let T := Nat; let U := T; let V := U; let y : V := Nat.zero; y"),
  ("inferLet/chainFun", "def c13 : Nat := let T := Nat; let U := T; (fun (q : U) => q) Nat.zero"),
  ("inferLet/lamT", "def c14 : Nat → Nat := let T := Nat; fun (q : T) => Nat.zero"),
  ("inferLet/dropMid", "def c15 : (b : Type) → (a : Type) → a → a := fun (b : Type) (a : Type) => let L := Nat; fun (q : a) => q"),
  ("inferLet/dropMidNat", "def c16 (b : Type) (a : Type) : a → a := let L := Nat; fun (q : a) => q"),
  ("inferLet/chainNoUse", "def c4 : Nat := let T := Nat; let U := T; Nat.zero"),
  ("inferLet/chainAscr", "def c5 : Nat := let T := Nat; let U := T; (Nat.zero : U)"),
  ("inferLet/chainYT", "def c6 : Nat := let T := Nat; let U := T; let y : T := Nat.zero; y"),
  ("inferLet/chainNoY", "def c7 : Nat := let T := Nat; let U := T; let y : U := Nat.zero; Nat.zero"),
  ("inferLet/oneY", "def c8 : Nat := let T := Nat; let y : T := Nat.zero; y"),
  ("inferLet/thm", "theorem c9 : Eq Nat.zero Nat.zero := let T := Nat; let U := T; let y : U := Nat.zero; rfl"),
  ("inferLet/have", "def c10 : Nat := have T := Nat; have U := T; have y : U := Nat.zero; y"),
  ("inferLet/typePos", "def c11 : (let T := Nat; let U := T; U) := Nat.zero"),
  ("inferLet/chainUseU", "def c12 : Type := let T := Nat; let U := T; U"),
  -- the same telescopes with the decl type inferred (no header type)
  ("inferLet/noTypeChain", "def n10 := let T := Nat; let U := T; let y : U := Nat.zero; y"),
  ("inferLet/noTypeLamT", "def n14 := let T := Nat; fun (q : T) => Nat.zero"),
  ("inferLet/numChain", "def n7 : Nat := let T := Nat; let U := T; let y : U := 1; y"),
  -- worktree D: doc comments + private (`elabModifiers` slots 0/2, `applyVisibility`,
  -- `checkNotAlreadyDeclared`, `resolvePrivateName`); mainModule is anonymous here, so
  -- a private name is `_private.0.<n>`
  ("doc/def", "/-- doc -/ def c5a : Nat := Nat.zero"),
  ("doc/thm", "/-- doc -/ theorem c5b : Eq Nat.zero Nat.zero := rfl"),
  ("priv/def", "private def c5e : Nat := Nat.zero"),
  ("priv/use", "private def c5f : Nat := Nat.zero\ndef c5g : Nat := c5f"),
  ("priv/thm", "private theorem c5t : Eq Nat.zero Nat.zero := rfl"),
  ("priv/ns", "namespace Q\nprivate def pz : Nat := Nat.zero\nend Q\ndef c5q : Nat := Q.pz"),
  ("doc/private", "/-- d -/ private def c5p : Nat := Nat.zero"),
  ("priv/thmThenAux", "private theorem c5x (h : Eq Nat.zero Nat.zero) : Eq Nat.zero Nat.zero := h\nprivate def c5y : PProd Nat (Eq Nat.zero Nat.zero) := PProd.mk Nat.zero rfl"),
  ("priv/clashPriv", "private def p1 : Nat := Nat.zero\nprivate def p1 : Nat := Nat.zero"),
  ("priv/afterPub", "def p2 : Nat := Nat.zero\nprivate def p2 : Nat := Nat.zero"),
  ("priv/pubAfterPriv", "private def p3 : Nat := Nat.zero\ndef p3 : Nat := Nat.zero"),
  ("priv/afterImported", "private def Nat.succ : Nat := Nat.zero"),
  ("priv/otherNs", "namespace R\nprivate def p4 : Nat := Nat.zero\nend R\ndef c4 : Nat := p4"),
  ("priv/sameNs", "namespace Q\nprivate def pz2 : Nat := Nat.zero\ndef cz : Nat := pz2\nend Q"),
  ("priv/protOpen", "namespace S\nprivate protected def p6 : Nat := Nat.zero\nend S\nopen S\ndef c6 : Nat := p6"),
  ("priv/protQual", "namespace S\nprivate protected def p7 : Nat := Nat.zero\ndef c7 : Nat := S.p7\nend S"),
  ("priv/protInNs", "namespace S\nprivate protected def p8 : Nat := Nat.zero\ndef c8 : Nat := p8\nend S"),
  ("priv/protRoot", "private protected def p8c : Nat := Nat.zero"),
  ("priv/rootDecl", "namespace T\nprivate def _root_.p9 : Nat := Nat.zero\nend T\ndef c9 : Nat := p9"),
  ("priv/rootRef", "private def p10 : Nat := Nat.zero\ndef c10 : Nat := _root_.p10"),
  ("priv/open", "namespace U\nprivate def p11 : Nat := Nat.zero\nend U\nopen U\ndef c11 : Nat := p11"),
  ("priv/openExplicit", "namespace U\nprivate def p12 : Nat := Nat.zero\nend U\nopen U (p12)\ndef c12 : Nat := p12"),
  ("priv/openRenaming", "namespace U\nprivate def p12r : Nat := Nat.zero\nend U\nopen U renaming p12r → q12\ndef c12r : Nat := q12"),
  ("priv/openHiding", "namespace U\nprivate def p12h : Nat := Nat.zero\nend U\nopen U hiding p12h\ndef c12h : Nat := p12h"),
  ("priv/dotted", "private def V.p13 : Nat := Nat.zero\ndef c13 : Nat := V.p13"),
  ("priv/dottedNsOpen", "private def V.p14 : Nat := Nat.zero\nopen V\ndef c14 : Nat := p14"),
  ("priv/aux", "private def c15 (m : Nat) : PProd Nat (Eq (Nat.succ m) (Nat.succ m)) := PProd.mk m rfl"),
  ("priv/example", "private example : Nat := Nat.zero"),
  ("priv/axiom", "private axiom p16 : Nat"),
  ("priv/abbrev", "private abbrev p17 : Nat := Nat.zero"),
  ("priv/opaque", "private opaque p18 : Nat := Nat.zero"),
  ("priv/fieldDot", "private def Nat.p19 (n : Nat) : Nat := n\ndef c19 : Nat := Nat.zero.p19"),
  ("priv/fieldDotVar", "private def Nat.p19b (n : Nat) : Nat := n\ndef c19b (k : Nat) : Nat := k.p19b"),
  ("priv/autoBound", "private def p20 (x : α) : α := x"),
  ("priv/msg", "private def pb : Nat := Nat.zero\ndef cb : Bool := pb"),
  ("priv/at", "private def pu : Nat := Nat.zero\ndef cu : Nat := @pu"),
  ("priv/reopenNs", "namespace Q2\nprivate def pz3 : Nat := Nat.zero\nend Q2\nnamespace Q2\ndef cz3 : Nat := pz3\nend Q2"),
  ("priv/variable", "variable (n : Nat)\nprivate def p21 : Nat := n"),
  ("priv/universe", "universe u\nprivate def p22 (α : Sort u) (a : α) : α := a"),
  ("doc/axiom", "/-- d -/ axiom d1 : Nat"),
  ("doc/example", "/-- d -/ example : Nat := Nat.zero"),
  ("doc/protected", "namespace W\n/-- d -/ protected def d2 : Nat := Nat.zero\nend W"),
  ("doc/abbrev", "/-- d -/ abbrev d3 : Nat := Nat.zero"),
  ("doc/opaque", "/-- d -/ opaque d4 : Nat := Nat.zero"),
  -- worktree D neighbours: private beyond the slice's shape (pre-PR probe)
  ("priv/autoUniv", "private def q1 (α : Sort u) (a : α) : α := a"),
  ("priv/varUse", "private def q2 : Nat := Nat.zero\nvariable (h : Eq q2 q2)\ntheorem q3 : Eq q2 q2 := h"),
  ("priv/auxReusePrivFirst", "private def q4 (m : Nat) : PProd Nat (Eq (Nat.succ m) (Nat.succ m)) := PProd.mk m rfl\ndef q5 (m : Nat) : PProd Nat (Eq (Nat.succ m) (Nat.succ m)) := PProd.mk m rfl"),
  ("priv/auxReusePubFirst", "def q4b (m : Nat) : PProd Nat (Eq (Nat.succ m) (Nat.succ m)) := PProd.mk m rfl\nprivate def q5b (m : Nat) : PProd Nat (Eq (Nat.succ m) (Nat.succ m)) := PProd.mk m rfl"),
  ("priv/fieldStruct", "private def PProd.q6 (p : PProd Nat Nat) : Nat := PProd.fst p\ndef q7 (p : PProd Nat Nat) : Nat := p.q6"),
  ("priv/overloadPick", "namespace A1\nprivate def q8 : Nat := Nat.zero\nend A1\nnamespace B1\ndef q8 : Bool := Bool.true\nend B1\nopen A1 B1\ndef q9 : Nat := q8"),
  ("priv/overloadAmbig", "namespace A1\nprivate def q8 : Nat := Nat.zero\nend A1\nnamespace B1\ndef q8 : Nat := Nat.zero\nend B1\nopen A1 B1\ndef q9 : Nat := q8"),
  ("priv/unknownField", "private def q13 : Nat := Nat.zero\ndef q14 : Nat := q13.foo"),
  ("priv/clashDotted", "namespace A2\nprivate def q16 : Nat := Nat.zero\nend A2\nprivate def A2.q16 : Nat := Nat.zero"),
  ("priv/rootRegister", "private def _root_.W3.p : Nat := Nat.zero\nopen W3\ndef cw3 : Nat := p"),
  ("priv/rootRegisterInNs", "namespace T4\nprivate def _root_.W4.p : Nat := Nat.zero\nend T4\nnamespace W4\ndef cw4 : Nat := p\nend W4"),
  ("priv/univVariable", "universe v\nvariable (β : Sort v)\nprivate def q18 (b : β) : β := b"),
  ("priv/thmUsesPrivThm", "private theorem q19 : Eq Nat.zero Nat.zero := rfl\ntheorem q20 : Eq Nat.zero Nat.zero := q19"),
  ("priv/protQualOutside", "namespace S9\nprivate protected def q21 : Nat := Nat.zero\nend S9\ndef cs9 : Nat := S9.q21"),
  ("priv/rootQualInNs", "namespace Z\nprivate def q23 : Nat := Nat.zero\ndef cz : Nat := _root_.Z.q23\nend Z"),
  ("priv/explicitUniv", "private def q24.{w} (α : Sort w) : Sort w := α"),
  ("priv/varPrivType", "private def q26 : Type := Nat\nvariable (x : q26)\ndef q27 : q26 := x"),
  ("priv/nsChild", "private def q28 : Nat := Nat.zero\ndef q28.x : Nat := q28"),
  ("priv/thenPrivDotted", "private def q29 : Nat := Nat.zero\nprivate def q29.y : Nat := q29\ndef cq29 : Nat := q29.y"),
  ("priv/appMismatch", "private def q30 (n : Nat) : Nat := n\ndef cq30 : Nat := q30 Bool.true"),
  ("priv/atExplicit", "private def q31 {α : Type} (a : α) : α := a\ndef cq31 : Nat := @q31 Nat Nat.zero"),
  ("priv/pubThenPrivSameNsOpen", "namespace A3\ndef q33 : Nat := Nat.zero\nend A3\nnamespace B3\nprivate def q33 : Bool := Bool.true\nend B3\nopen A3 B3\ndef cq33 : Bool := q33"),
  ("priv/typeFieldOwn", "private def T7 : Type := Nat\nprivate def T7.f (x : T7) : Nat := Nat.zero\ndef r36 (x : T7) : Nat := x.f"),
  ("priv/typePubField", "private def T8 : Type := Nat\ndef T8.f (x : T8) : Nat := Nat.zero\ndef r37 (x : T8) : Nat := x.f"),
  ("priv/typeDotIdent", "private def T9 : Type := Nat\ndef T9.z : T9 := Nat.zero\ndef r38 : T9 := .z"),
  -- private names in messages: `.ofConstName` prints the user name, a plain
  -- `Name` (theorem type, `c ++ suffix`) the private one
  ("priv/msgThmNotProp", "private theorem t1 : Nat := Nat.zero"),
  ("priv/msgSortField", "private def q36 : Type := Nat\ndef r15 : Nat := q36.foo"),
  ("priv/msgNamedArg", "private def q37 (n : Nat) : Nat := n\ndef r16 : Nat := q37 (m := Nat.zero)"),
  ("priv/msgAxiomTypeField", "private axiom T14 : Type\ndef r17 (x : T14) : Nat := x.foo"),
  ("priv/msgFieldAmbig", "namespace A5\ndef Nat.g (n : Nat) : Nat := n\nend A5\nnamespace B5\nprivate def Nat.g (n : Nat) : Nat := n\nend B5\nopen A5 B5\ndef r11 (k : Nat) : Nat := k.g"),
  ("priv/msgOpenUnknown", "namespace U5\nprivate def p5 : Nat := Nat.zero\nend U5\nopen U5 (p6)"),
  ("priv/msgAlreadyRoot", "private def q35 : Nat := Nat.zero\nprivate def _root_.q35 : Nat := Nat.zero"),
  ("priv/msgUnivDup", "private def q39.{u, u} : Nat := Nat.zero"),
  ("priv/msgPiField", "private def q40 : Nat → Nat := fun n => n\ndef r18 : Nat := q40.foo"),
  -- `private abbrev`: the reducible overlay holds the private (mangled) name
  ("priv/abbrevClass", "private abbrev PW := Wrap\ndef r19 [PW Nat] : Nat := Wrap.wrap Nat.zero"),
  -- worktree B: isDefEqOffset + UnitLike fall-through (Offset.lean:118-163;
  -- isDefEqApp -> projInst/stringLit/unitLike/onFailure tail, ExprDefEq.lean:2166-2232)
  ("unitLike/u1", "def u1 (a b : Nat) (f : Nat → Unit) : Eq (f a) (f b) := rfl"),
  ("unitLike/u2punit", "def u2 (a b : Nat) (f : Nat → PUnit.{1}) : Eq (f a) (f b) := rfl"),
  ("unitLike/u4OE", "def u4 (a b : Nat) (f : Nat → OE) : Eq (f a) (f b) := rfl"),
  ("unitLike/u7heads", "def u7 (f g : Nat → Unit) (a : Nat) : Eq (f a) (g a) := rfl"),
  ("unitLike/t6", "def t6 (f : Tag → Unit) (a : Tag) : Eq (f a) (f 0) := rfl"),
  ("offset/n7", "def n7 : Eq 0 Nat.zero := rfl"),
  ("offset/n7rev", "def n8 : Eq Nat.zero 0 := rfl"),
  ("offset/n22h", "def n22 (x : Nat) (h : Eq x 0) : Eq x Nat.zero := h"),
  ("offset/n23h", "def n23 (h : Eq Nat.zero Nat.zero) : Eq 0 0 := h"),
  ("offset/t1tag", "def t1 : Eq (0 : Tag) (Tag.mk Nat.zero) := rfl"),
  ("offset/t4tagof", "def t4 : Eq (OfNat.ofNat 0 : Tag) (Tag.mk Nat.zero) := rfl"),
  ("offset/ty1", "def ty1 (f : Nat → Type) (h : f 0) : f Nat.zero := h"),
  ("offset/ty2", "def ty2 (f : Nat → Type) (h : f Nat.zero) : f 0 := h"),
  ("offset/pick0", "def pk : Eq (pick 0 Nat.zero) Nat.zero := rfl"),
  ("offset/li1", "def li1 : Eq (Wrap.wrap 0) Nat.zero := rfl"),
  ("offset/rflx0", "def lt3 : Eq Nat.zero Nat.zero := let x := 0; (rfl : Eq x 0)"),
  ("offset/rflxZero", "def lt4 : Eq Nat.zero Nat.zero := let x := 0; PProd.fst (PProd.mk (rfl : Eq x Nat.zero) x)"),
  ("offset/rflx5", "def lt5 : Eq Nat.zero Nat.zero := let x := Nat.zero; (rfl : Eq x 0)"),
  ("offset/rflx6", "def lt6 : Eq 0 0 := let x := Nat.zero; (rfl : Eq x x)"),
  ("offset/m1", "def m1 : Eq (Nat.succ 1) 2 := (rfl : Eq (Nat.succ _) 2)"),
  ("offset/m3", "def m3 := (rfl : Eq (Nat.succ _) 2)"),
  ("offset/m4", "def m4 := (rfl : Eq 3 (Nat.succ (Nat.succ _)))"),
  ("offset/m5", "def m5 := (rfl : Eq (Add.add _ 1) 3)"),
  ("offset/m7", "def m7 := (rfl : Eq (Nat.succ _) (Nat.succ (Nat.succ Nat.zero)))"),
  ("offset/n13neg", "def n13 : Eq 0 (Nat.succ Nat.zero) := rfl"),
  ("offset/n14neg", "def n14 : Eq 1 Nat.zero := rfl"),
  ("offset/n17neg", "def n17 (x : Nat) : Eq (Nat.succ x) 0 := rfl"),
  ("offset/n18neg", "def n18 (x : Nat) : Eq (Nat.succ x) 1 := rfl"),
  ("offset/n21addneg", "def n21 : Eq (Add.add 1 0) 0 := rfl"),
  ("offset/t3tagneg", "def t3 : Eq (1 : Tag) (Tag.mk Nat.zero) := rfl"),
  ("offset/m6neg", "def m6 := (rfl : Eq (Nat.succ _) Nat.zero)"),
  ("offset/n16neg", "def n16 (x : Nat) : Eq (Nat.succ x) (Nat.succ (Nat.succ x)) := rfl"),
  ("offset/m8", "def m8 (y : Nat) := (rfl : Eq (Nat.succ _) (Nat.succ (Nat.succ y)))"),
  ("offset/n19add", "def n19 (x : Nat) : Eq (Add.add x 1) (Nat.succ x) := rfl"),
  ("offset/n20add", "def n20 : Eq (Add.add 0 1) 1 := rfl")
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
