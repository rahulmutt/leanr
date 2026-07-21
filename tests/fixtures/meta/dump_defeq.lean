/- Emits the tier-1 meta query corpus as canonical JSONL (plan-2 spec
§ Acceptance harness). Runs with LEAN_PATH set to this directory so
`import Meta0` resolves to the committed fixture and NOTHING else —
Meta0 is prelude-mode, so the oracle environment here is exactly the
environment leanr replays. Query ids are constant/kind/index (stable
across regen); mvars/fvars are numbered per query in first-occurrence
order; binder names and mdata are erased (canonicalization rules
below).

Canonical expr scheme (the contract task 9's Rust side implements
against, byte-for-byte):
  {"k":"sort","u":<L>}
  {"k":"const","n":"N.succ","us":[<L>...]}
  {"k":"app","f":<E>,"a":<E>}
  {"k":"lam","bi":"d|i|s|c","t":<E>,"b":<E>}
  {"k":"pi","bi":...,"t":<E>,"b":<E>}
  {"k":"let","t":<E>,"v":<E>,"b":<E>,"nd":true|false}
  {"k":"bvar","i":N}
  {"k":"lit","n":"<decimal>"}
  {"k":"str","v":"..."}
  {"k":"proj","s":"S","i":N,"e":<E>}
  {"k":"mvar","i":N}
  {"k":"fvar","i":N}
Levels <L>:
  {"k":"zero"}
  {"k":"succ","u":<L>}
  {"k":"max","a":<L>,"b":<L>}
  {"k":"imax","a":<L>,"b":<L>}
  {"k":"param","n":"u"}

Canonicalization rules: binder names are ERASED (only `bi` survives);
`MData` is ERASED on both sides (recurse straight through it); mvars/
fvars are numbered in first-occurrence order WITHIN one query record
(shared across that record's `in` and `out`, so a value shared between
them gets the same number); literals print as decimal strings (no i64
truncation); binder-info kinds map `default`->d, `implicit`->i,
`strictImplicit`->s, `instImplicit`->c.

Boilerplate reconciliation against the in-repo precedents:
`tests/fixtures/dump_decls.lean` reads a `.olean` directly via
`readModuleData` (no elaboration, no `Lean.Meta`) so its only
contribution here is the general `def main : IO Unit := do ... ;
IO.println` shape and `Name.toString (escape := false)`.
`tests/fixtures/syntax/dump_syntax_elab.lean` is closer: it shows the
`Lean.enableInitializersExecution`-before-import pitfall (needed here
too, since we import with `loadExts := true` so the reducibility
environment extension — `@[reducible]`/`@[irreducible]` — is actually
populated; without it the extension entries `redId`/`irredId` need
would silently read as absent) and `Lean.initSearchPath (←
Lean.findSysroot)`. Neither precedent drives `MetaM`, so the
`Core.Context`/`Core.State`/`MetaM.toIO` plumbing below was written
fresh against the pinned toolchain's `Lean/CoreM.lean` and
`Lean/Meta/Basic.lean` (`MetaM.toIO` exists directly there and is
simpler than manually composing `CoreM.run'`/`EIO.toIO`).
-/
-- NOT `import Meta0`: Meta0 is prelude-mode and declares its own
-- `PProd`/`Prod`/`Eq`/`HEq`/... scaffold, which collides with the
-- real `Init` this file needs for the `Lean`/`Lean.Meta` API (`import
-- Lean failed: environment already contains 'PProd.rec' from
-- Init.Prelude`, confirmed empirically). The dumper never needs Meta0
-- as a compile-time dependency — `mkConst`/`mkApp` build references by
-- plain `Name`, and the query environment is loaded purely at RUNTIME
-- via `importModules` in `main` below (LEAN_PATH=$PWD point at this
-- directory resolves `Meta0` there and nowhere else — the hermetic
-- contract).
import Lean
open Lean Lean.Meta

-- ===== canonical expr/level encoder =====

/-- `default`->d, `implicit`->i, `strictImplicit`->s, `instImplicit`->c
(binder NAMES are erased everywhere; only this kind letter survives). -/
def biStr : BinderInfo → String
  | .default => "d"
  | .implicit => "i"
  | .strictImplicit => "s"
  | .instImplicit => "c"

/-- Levels never carry mvars in a fully-elaborated corpus (every level
in Meta0's constants and in the handwritten query builders below is
either a concrete `zero`/`succ` chain or a declared universe param) —
the canonical scheme has no `lmvar` case, so an actual `Level.mvar`
here would be a real gap; fail loudly rather than silently emit a
wrong-but-well-formed record. -/
partial def encLevel : Level → Json
  | .zero => Json.mkObj [("k", "zero")]
  | .succ u => Json.mkObj [("k", "succ"), ("u", encLevel u)]
  | .max a b => Json.mkObj [("k", "max"), ("a", encLevel a), ("b", encLevel b)]
  | .imax a b => Json.mkObj [("k", "imax"), ("a", encLevel a), ("b", encLevel b)]
  | .param n => Json.mkObj [("k", "param"), ("n", n.toString (escape := false))]
  | .mvar _ => panic! "dump_defeq: unexpected Level.mvar (not in the canonical scheme)"

/-- Per-query numbering state for mvars/fvars, first-occurrence order.
Shared across one query's `in` and `out` encode calls (see `encPair`
below) so a value referenced on both sides gets one stable number. -/
structure EncSt where
  fvars : Std.HashMap FVarId Nat := {}
  fNext : Nat := 0
  mvars : Std.HashMap MVarId Nat := {}
  mNext : Nat := 0

abbrev EncM := StateM EncSt

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
  | .sort u => pure <| Json.mkObj [("k", "sort"), ("u", encLevel u)]
  | .const n us =>
    pure <| Json.mkObj
      [("k", "const"), ("n", n.toString (escape := false)),
       ("us", Json.arr (us.map encLevel).toArray)]
  | .app f a => do
    let fj ← encExpr f
    let aj ← encExpr a
    pure <| Json.mkObj [("k", "app"), ("f", fj), ("a", aj)]
  | .lam _ t b bi => do
    -- binder name erased (`_`); only `bi`'s kind letter survives.
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

/-- Encode an `(in, out)` pair sharing one first-occurrence numbering
state (the canonicalization rule: numbering is per QUERY, not per
side). -/
def encPair (a b : Expr) : Json × Json :=
  let (aj, st) := (encExpr a).run {}
  let bj := (encExpr b).run' st
  (aj, bj)

-- ===== query corpus =====

def transparencies : List (String × TransparencyMode) :=
  [("reducible", .reducible), ("default", .default), ("all", .all)]

def one : Expr := mkApp (mkConst `N.succ) (mkConst `N.zero)

/-- Handwritten whnf queries: (constant, index, expr-builder). The
index is per-CONSTANT (never a global counter) and is shared by all
three transparency records the query produces below — those are
disambiguated by `tr`, not by `id`, matching the header contract's
literal `constant/kind/index` id shape. This list is the corpus'
growth point — extend it alongside Meta0.lean. -/
def whnfQueries : List (Name × Nat × Expr) :=
  [ (`redId,   0, mkApp (mkConst `redId) one)
  , (`semiDouble, 0, mkApp (mkConst `semiDouble) (mkConst `N.zero))
  , (`irredId, 0, mkApp (mkConst `irredId) one)
  , (`letChain, 0, mkConst `letChain)
  , (`useFst,  0, mkApp (mkConst `useFst) (mkConst `mkP))
  , (`add,     0, mkApp (mkApp (mkConst `add) one) one)
  , (`count,   0, mkApp (mkConst `count) one)
  , (`count,   1, mkApp (mkConst `count) (mkConst `N.zero))
  ]

def emit (id : String) (q : String) (tr : String) (inE outE : Json) : IO Unit :=
  IO.println <| Json.compress <| Json.mkObj
    [("id", id), ("q", q), ("tr", tr), ("in", inE), ("out", outE)]

unsafe def main : IO Unit := do
  -- Must run before any `importModules (loadExts := true)` or the
  -- import throws internally (dump_syntax_elab.lean's module doc, same
  -- pitfall, confirmed here empirically).
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  -- `loadExts := true`: without it the reducibility environment
  -- extension (`@[reducible]`/`@[irreducible]`) is not populated, so
  -- `redId`/`irredId`'s attribute status would silently read as
  -- default/semireducible instead of what Meta0.lean actually
  -- declares — a correctness bug in the oracle itself, not a
  -- cosmetic gap.
  let env ← Lean.importModules #[{ module := `Meta0 }] {} (trustLevel := 0) (loadExts := true)
  let coreCtx : Core.Context := { fileName := "<dump_defeq>", fileMap := default }
  let coreState : Core.State := { env }
  let go : MetaM Unit := do
    for (name, i, e) in whnfQueries do
      for (trName, tr) in transparencies do
        let r ← withTransparency tr <| whnf e
        let (inJ, outJ) := encPair e r
        emit s!"{name}/whnf/{i}" "whnf" trName inJ outJ
    -- Constant loop: NOT filtered to "module Meta0" — Meta0 is
    -- import-free, so the environment here IS exactly Meta0's own
    -- constants and nothing else; a module filter would be a no-op.
    -- Elaborator-generated auxiliaries (`count._sunfold`, matchers,
    -- `.brecOn`/`.rec`-adjacent defs) DO appear via `.value?` when
    -- they carry a value, and are wanted: real reduction-relevant
    -- constants. Anything whose `inferType` fails is skipped with a
    -- stderr log, never silently dropped.
    for (cname, cinfo) in (← getEnv).constants.toList do
      if let some v := cinfo.value? then
        try
          let t ← inferType v
          let (inJ, outJ) := encPair v t
          emit s!"{cname.toString (escape := false)}/infer/0" "infer" "default" inJ outJ
        catch ex =>
          let msg ← ex.toMessageData.toString
          IO.eprintln s!"dump_defeq: skipping infer for {cname.toString (escape := false)}: {msg}"
  discard <| go.toIO coreCtx coreState
