/- Emits the M4b-1 tier-1 elaboration query corpus as canonical JSONL
(design spec § The differential oracle harness). Runs with LEAN_PATH set
to this directory so `import Elab0` resolves to the committed fixture
and NOTHING else — Elab0 is prelude-mode, so the oracle environment here
is exactly the environment leanr replays.

Unlike `dump_defeq.lean` (Expr -> Expr queries built directly against a
fixed environment), this dumper's queries are `(id, src)` pairs of Lean
SOURCE TEXT: for each, `Lean.Parser.runParserCategory env `term src`
parses it, then `Lean.Elab.Term.elabTerm stx (expectedType? := none)`
elaborates it. leanr parses the SAME source text through its own
`leanr_syntax::parse_term`, so a parse divergence is caught by that
crate's own oracle gate (`oracle_golden.rs`) upstream of this one —
this dumper's job is to isolate the ELABORATOR.

**Slice 1 does NO postponement**: this dumper calls exactly `elabTerm`
then `instantiateMVars` — no `synthesizeSyntheticMVarsNoPostponing`, no
other scheduling pass. This is a DELIBERATE, pinned choice (design
spec's "Universe defaulting divergence" risk note): the entry point
must match what `crates/leanr_elab`'s `elab_term_ensuring_type` models
(`elab_term` then `instantiate_mvars`, nothing else), or a universe-
defaulting or postponement-related pass on the oracle side would appear
as a spurious regression instead of an intentional non-goal. Later
slices (M4b-2's postponement/synthetic-mvar ladder) will need a richer
entry point here; that is out of scope for this dumper today.

Canonical expr scheme: IDENTICAL to `dump_defeq.lean`'s (documented
there), extended with the `lmvar` node (M4b-1 Task 2 / this design
spec's "Universe metavariables in the output" section) for a level
metavariable `instantiateMVars` did not close:
  {"k":"lmvar","i":N}
numbered in first-occurrence order per query record, exactly like
`mvar`/`fvar`. Every other node/level shape and canonicalization rule
(binder names erased, MData erased, literals as decimal strings,
binder-info d/i/s/c) is unchanged from `dump_defeq.lean`.

Record shape: `{"id":<string>,"src":<string>,"exp":<canonical Expr>}`
(no `q`/`tr`/`in`/`out` fields — those are `dump_defeq.lean`'s meta-
query shape, not this one's).

Boilerplate reconciliation: the `Lean.enableInitializersExecution`-
before-import pitfall and `Core.Context`/`Core.State`/`MetaM.toIO`
plumbing are copied verbatim from `dump_defeq.lean` (see that file's own
doc comment for the citations); this file adds `Lean.Parser.
runParserCategory` (`Lean/Parser/Extension.lean`) for the parse step and
`Lean.Elab.Term.TermElabM.run'`/`Lean.Elab.Term.elabTerm`
(`Lean/Elab/Term/TermElabM.lean`, `Lean/Elab/Term.lean`) for the
elaboration step, both read directly from the pinned toolchain source
before writing this file (never guessed).
-/
-- NOT `import Elab0`: same reason as `dump_defeq.lean`'s own note —
-- Elab0 is prelude-mode and declares its own `PProd`/`Prod`/`Eq`/`HEq`/
-- `String`/... scaffold, which collides with the real `Init` this file
-- needs for the `Lean`/`Lean.Meta`/`Lean.Elab` API. The dumper never
-- needs Elab0 as a compile-time dependency — the query environment is
-- loaded purely at RUNTIME via `importModules` in `main` below
-- (LEAN_PATH=$PWD point at this directory resolves `Elab0` there and
-- nowhere else — the hermetic contract).
import Lean
open Lean Lean.Meta

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

/-- `(id, src)`: `id` is a stable label (`str/<name>`), `src` is Lean
source text for a single term, parsed via `runParserCategory .. `term`.
Covers: a plain literal, the empty string, the four single-letter
escapes (`\n \t \\ \"`), the `\'` escape, a `\xHH` byte escape, a
`\uHHHH` code-point escape, and a literal (unescaped) non-ASCII
character — every `decodeQuotedChar` case
(`Init/Meta/Defs.lean:1089-1108`) except the string-gap
(`"\" whitespace+`, a line-continuation feature with no bearing on a
single-line corpus entry) and raw string literals (`r"..."`, a
DIFFERENT token shape `Syntax.decodeStrLit` branches on separately —
out of scope for this slice's plain-string-literal elaborator). -/
def strQueries : List (String × String) :=
  [ ("str/hello", "\"hello\"")
  , ("str/empty", "\"\"")
  , ("str/newline", "\"a\\nb\"")
  , ("str/tab", "\"a\\tb\"")
  , ("str/backslash", "\"a\\\\b\"")
  , ("str/quote", "\"a\\\"b\"")
  , ("str/apostrophe", "\"a\\'b\"")
  , ("str/hexEscape", "\"\\x41\\x42\"")
  , ("str/unicodeEscape", "\"\\u00e9\"")
  , ("str/nonAscii", "\"héllo\"")
  ]

/-- Task 5: the identifier leaf elaborator. `Nat` has zero universe
params (`const Nat []`, no fresh level mvar); `List` has exactly one
(`const List [?u]`, one fresh level mvar per `levelParams` — the first
query to exercise `lmvar` end-to-end). -/
def identQueries : List (String × String) :=
  [ ("ident/Nat", "Nat")
  , ("ident/List", "List")
  ]

def emit (id src : String) (expJ : Json) : IO Unit :=
  IO.println <| Json.compress <| Json.mkObj [("id", id), ("src", src), ("exp", expJ)]

unsafe def main : IO Unit := do
  -- Must run before any `importModules (loadExts := true)` or the
  -- import throws internally (dump_syntax_elab.lean's module doc, same
  -- pitfall, confirmed here empirically by `dump_defeq.lean`).
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Elab0 }] {} (trustLevel := 0) (loadExts := true)
  let coreCtx : Core.Context := { fileName := "<dump_elab>", fileMap := default }
  let coreState : Core.State := { env }
  let go : MetaM Unit := do
    for (id, src) in strQueries ++ identQueries do
      match Lean.Parser.runParserCategory env `term src with
      | .error msg => IO.eprintln s!"dump_elab: parse error for {id}: {msg}"
      | .ok stx =>
        try
          -- Slice 1's pinned entry point (module doc above): elabTerm,
          -- then instantiateMVars, nothing else.
          let e ← (Lean.Elab.Term.elabTerm stx none).run'
          let e ← instantiateMVars e
          let expJ := (encExpr e).run' {}
          emit id src expJ
        catch ex =>
          let msg ← ex.toMessageData.toString
          IO.eprintln s!"dump_elab: elaboration failed for {id}: {msg}"
  discard <| go.toIO coreCtx coreState
