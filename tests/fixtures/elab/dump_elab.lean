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

**M4b-3 P2a: the entry point now runs the fixpoint.** This dumper's
elaboration step matches `crates/leanr_elab`'s
`TermElabM::elab_term_and_synthesize` (`elab.rs`) exactly: `elabTerm`,
then `synthesizeSyntheticMVarsNoPostponing`, then `instantiateMVars` —
the oracle's own `elabTermAndSynthesize` (`SyntheticMVars.lean:696-698`)
at the top level, where `withSynthesize`'s saved/restored pending list
is always empty. `crates/leanr_elab/tests/oracle_elab.rs`'s
`oracle_elab_gate` is what now enforces this alignment: it calls
`elab_term_and_synthesize` directly (M4b-3 P2a final-review fix), so a
future edit to either this dumper's pipeline or that method's body
that de-synchronizes the two will show up as a corpus diff there,
rather than as a doc claim nothing checks. The fixpoint is what forces
a stuck typeclass problem (an instance goal no candidate solves, or
whose own type is still a metavariable) to be REPORTED rather than
silently emitted as a term with a dangling instance mvar in it.

Measured empty-diff over the whole corpus (M4b-3 P2a task 9): every
one of the 81 committed records is byte-identical under the new
pipeline, including `hole/bare`'s `{"k":"mvar","i":0}` — that mvar is a
bare `_`'s NATURAL hole, not a synthetic one, so `reportStuckSyntheticMVars`
never looks at it and it survives instantiation untouched exactly as
before. This does NOT mean the fixpoint is a no-op in general: `useWrap`
(a bare instance goal with no expected type) and `fun f => f Nat.zero`
(an application whose function type is never pinned down) both go from
elaborating to a term, under the OLD entry point, to reporting an error
under this one — which is exactly why neither is a corpus record here.

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
query shape, not this one's). M4b-4c P2 adds a second shape for a query
the oracle REJECTS: `{"id":<string>,"src":<string>,"err":<string>}`,
where `err` is the first line of the first logged message (or, if
nothing was logged, of the thrown exception). Only `elimErrQueries`
emit it; a query there that elaborates is reported on stderr.

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

/-- Task 6: `Prop`/`Type`/`Sort e`, `(e)`/`(e : T)`, and `_`.
`sort/Prop` = `Sort 0`; `sort/Type` (bare, no level argument) = `Sort
(succ zero)`, NOT a fresh level mvar (`elabOptLevel`'s `isNone` branch
returns `Level.zero` directly — confirmed against the pinned toolchain
source, `Lean/Elab/BuiltinTerm.lean`); `sort/TypeN`/`sort/SortN`
exercise a `num` level argument (`Level.ofNat`, decimal digits -> that
many `succ`s); `sort/SortHole` exercises `Sort _`'s level-hole branch
(`Lean.Parser.Level.hole` -> a fresh level mvar, canonicalizing to an
`lmvar` node) — confirmed standalone-reachable by a throwaway probe
against the real oracle (unlike `Sort u`, which hits an uncaught
auto-bound-implicit signal even in the real elaborator with no
enclosing declaration — see `crates/leanr_elab/src/builtin/sort.rs`'s
own module doc). `paren/nat` and `asc/natInType` exercise `(e)` and
`(e : T)` respectively (real tree shape: `typeAscription` is NOT
`paren` wrapping a nested node — see `crates/leanr_elab/src/builtin/
ascription.rs`'s own module doc for the parse-dump correction).
`hole/bare` exercises `_` with `expectedType? := none` (this dumper's
own pinned entry point), which mints a fresh TYPE mvar first
(`mkFreshExprMVarImpl`'s `none` arm) and the hole itself second — only
the hole's own index shows up in the canonical `mvar` encoding, the
type mvar it points at is never walked. -/
def sortAscHoleQueries : List (String × String) :=
  [ ("sort/Prop", "Prop")
  , ("sort/Type", "Type")
  , ("sort/TypeN", "Type 3")
  , ("sort/SortN", "Sort 3")
  , ("sort/SortHole", "Sort _")
  , ("paren/nat", "(Nat)")
  , ("asc/natInType", "(Nat : Type)")
  , ("hole/bare", "_")
  ]

/-- Task 5 (M4b-2 plan1): the three universal-quantifier binder
elaborators — `elab_arrow` (non-dependent `Nat -> Nat`, right-
associated `Nat -> Nat -> Nat`), `elab_forall` (`forall (x : Nat),
Nat` non-dependent, `forall (a : Type), a` dependent — the bound
variable escapes into the body as a `bvar` — plus a two-name binder
group `forall (x y : Nat), Nat` and two separate binder groups
`forall (x : Nat) (y : Nat), Nat`), and `elab_dep_arrow` (`(x : Nat)
-> Nat` non-dependent, `(a : Type) -> a` dependent). Every term here
references only `Nat`/`Type`, both already in scope (`Elab0.lean`);
no new constant needed. -/
def binderQueries : List (String × String) := [
  ("arrow/natNat",        "Nat -> Nat"),
  ("arrow/rightAssoc",    "Nat -> Nat -> Nat"),
  ("forall/nondep",       "forall (x : Nat), Nat"),
  ("forall/dep",          "forall (a : Type), a"),
  ("forall/twoNames",     "forall (x y : Nat), Nat"),
  ("forall/twoGroups",    "forall (x : Nat) (y : Nat), Nat"),
  ("depArrow/nondep",     "(x : Nat) -> Nat"),
  ("depArrow/dep",        "(a : Type) -> a")
]

def funQueries : List (String × String) := [
  ("fun/explicitBinder",   "fun (x : Nat) => x"),
  ("fun/elidedBinder",     "fun x => x"),
  ("fun/twoBinders",       "fun (x : Nat) (y : Nat) => x"),
  ("fun/ascribedElided",   "(fun x => x : Nat -> Nat)"),
  ("fun/ascribedExplicit", "(fun (x : Nat) => x : Nat -> Nat)")
]

def letQueries : List (String × String) := [
  ("let/typed",       "let x : Nat := Nat.zero; x"),
  ("let/elided",      "let x := Nat.zero; x"),
  ("let/unused",      "let x : Nat := Nat.zero; Nat"),
  ("let/anon",        "let _ : Nat := Nat.zero; Nat"),
  ("let/nested",      "let x : Nat := Nat.zero; let y : Nat := x; y"),
  ("let/typeValue",   "let a : Type := Nat; a"),
  ("let/funValue",    "let f : Nat -> Nat := fun y => y; f"),
  ("let/binders",     "let f (y : Nat) : Nat := y; f"),
  ("let/twoBinders",  "let f (y : Nat) (z : Nat) : Nat := y; f"),
  ("let/binderIdent", "let f y : Nat := y; f"),
  ("let/inFun",       "fun (z : Nat) => let x : Nat := z; x"),
  ("let/ascribed",    "(let x : Nat := Nat.zero; x : Nat)"),
  ("let/depBinders",  "let f (a : Type) (z : a) : a := z; f"),
  ("let/holeBinder",  "let f _ : Nat := Nat.zero; f")
]

def haveQueries : List (String × String) := [
  ("have/typed",    "have h : Nat := Nat.zero; h"),
  ("have/elided",   "have h := Nat.zero; h"),
  ("have/unused",   "have h : Nat := Nat.zero; Nat"),
  ("have/hygiene",  "have : Nat := Nat.zero; this"),
  ("have/nested",   "have h : Nat := Nat.zero; have g : Nat := h; g"),
  ("have/funValue", "have f : Nat -> Nat := fun y => y; f"),
  ("have/ascribed", "(have h : Nat := Nat.zero; h : Nat)")
]

/-- M4b-3 P1 task 4: EXPLICIT-argument applications only. `Nat.succ`
takes one explicit `Nat` and no implicit/instance parameters, so these
exercise `ElabAppArgs.main`'s `processExplicitArg` arm, `addNewArg`, and
`finalize` with an empty `etaArgs`/`instMVars` — no implicit insertion
(task 5), no expected-type propagation (task 6), no instance synthesis
(P2). `app/nested` checks that the inner application elaborates through
the same path as an argument. -/
def appExplicitQueries : List (String × String) :=
  [ ("app/succZero",  "Nat.succ Nat.zero")
  , ("app/nested",    "Nat.succ (Nat.succ Nat.zero)")
  , ("app/ascribed",  "(Nat.succ Nat.zero : Nat)")
  ]

/-- M4b-3 P1 task 5: IMPLICIT argument insertion. `id {α : Sort u} (a :
α) : α` (Elab0's own `id`) is the minimal shape: elaborating `id
Nat.zero` inserts a fresh mvar for `α`, which the explicit argument's
`ensureArgType` then assigns — so the emitted term is `@id Nat
Nat.zero`, NOT `id Nat.zero`. `app/implicitBareIdent` is the case the
retired leaf `ident` elaborator got wrong by construction: a bare
polymorphic constant against an expected type gets its implicit
arguments inserted too. -/
def appImplicitQueries : List (String × String) :=
  [ ("app/implicitId",        "id Nat.zero")
  , ("app/implicitIdAscribed", "(id Nat.zero : Nat)")
  , ("app/implicitBareIdent", "(List.nil : List Nat)")
  ]

/-- M4b-3 P1 task 6: expected-type propagation
(`propagateExpectedType`, App.lean:563-609). The expected type reaches
the state machine through SOURCE ASCRIPTION — `(e : T)` — which is the
only way this dumper's pinned `expectedType? := none` entry point can
supply one (design spec § Verification). `app/propagatePi` is the shape
the heuristic exists for: the expected type determines an implicit
argument BEFORE the explicit argument is elaborated, so a divergence
here shows up as a different mvar assignment, not an error.

The plan's third query (`app/propagateId`, `"(id Nat.zero : Nat)"`) is
NOT here: it has the same `src` as task 5's committed
`app/implicitIdAscribed`, and two records with the same source under
different ids are noise, not coverage.

`app/propagateAbbrev` is the one query in this corpus that OBSERVABLY
distinguishes propagation-on from propagation-off, and it is here
because `app/propagateCons`/`app/propagatePi` — measured, not assumed —
do not: in a coercion-free environment every mvar the early unification
would assign is assigned anyway by `ensureArgType`/`finalize`, so both
orders converge on the same instantiated term. `Unit` is a REDUCIBLE
abbreviation of `PUnit`, which breaks that convergence:
  - propagating: `?α := Unit` first, so the emitted implicit argument is
    `Unit` and `PUnit.unit`'s own type is unified against it afterwards;
  - not propagating: `PUnit.unit` is elaborated first and assigns
    `?α := PUnit.{1}`, and `finalize`'s later `Unit =?= PUnit.{1}`
    succeeds by unfolding without ever rewriting the assignment.
Both terms are definitionally equal; only the first is the oracle's.
Without this record the whole `propagateExpectedType` implementation
could be deleted and this gate would stay green. -/
def appPropagateQueries : List (String × String) :=
  [ ("app/propagateCons",   "(List.cons Nat.zero List.nil : List Nat)")
  , ("app/propagatePi",     "(id id : Nat -> Nat)")
  , ("app/propagateAbbrev", "(id PUnit.unit : Unit)")
  ]

/-- M4b-3 P1 task 7: named arguments and eta-expansion. `app/namedBoth`
supplies both parameters by name (no eta). `app/namedEta` supplies only
the LATER one, so the earlier missing parameter becomes an eta argument
and the result is a LAMBDA (App.lean:191-205). `app/namedDep` supplies
a named argument that depends on the missing parameter, which becomes
IMPLICIT instead of eta (findNamedArgDependsOnCurrent?,
App.lean:340-348) — the two paths emit structurally different terms, so
both are corpus entries, not one.

`app/namedDepPropagate2` covers the SAME dependency test in its OTHER
oracle call site: `getResultingTypeCore?`'s `if (← findNamedArgDependsOn?
fType' namedArgs).isSome then processImplicit'` escape (App.lean:477-479),
which lets expected-type propagation continue past a missing parameter a
named argument determines, instead of postponing. It needs an ascription
(propagation's only P1 source), an explicit argument elaborated before the
escape point, and a result type that is itself a metavariable — see
`Elab0.lean`'s own comment on `dpick` for why each piece is required, and
the task-7 fix report for the measured before/after. The plan's simpler
`(dep2 Nat.zero (z := Nat.zero) : Nat)` was tried first and REJECTED: it
reaches the escape, but its resulting type is the closed `Nat`, so
propagating early and propagating one parameter later converge on the
same term and the record cannot tell the escape from the postponement. -/
def appNamedQueries : List (String × String) :=
  [ ("app/namedBoth",  "pick (x := Nat.zero) (y := Nat.zero)")
  , ("app/namedFirst", "pick (x := Nat.zero) Nat.zero")
  , ("app/namedEta",   "pick (y := Nat.zero)")
  , ("app/namedDep",   "dep (z := Nat.zero)")
  , ("app/namedDepPropagate2", "(dpick PUnit.unit (z := Nat.zero) : Unit)")
  ]

/-- M4b-3 P1 task 8: `@` and `.{u}`. Under `@`, implicit parameters are
supplied positionally (`processImplicitArg` delegates to
`processExplicitArg`, App.lean:879-885) and `resultIsOutParamSupport`
is forced off (App.lean:1355). `.{u}` supplies explicit universe levels
so `mkConst` mints FEWER fresh level mvars (TermElabM.lean:2117-2126) —
`app/univList` should carry a concrete `zero`, not an `lmvar`. -/
def appExplicitModeQueries : List (String × String) :=
  [ ("app/atId",     "@id Nat Nat.zero")
  , ("app/atBare",   "@Nat.succ")
  , ("app/univList", "List.{0}")
  ]

/-- M4b-3 P2a: instance-implicit arguments. Every term here SUCCEEDS in
the oracle under the current entry point — instance synthesis runs
eagerly in `synthesizeAppInstMVars` at `finalize`, not in the fixpoint
(measured during planning) — so these records land before the
entry-point change and stay byte-identical across it.

  * `tc/useWrapNat` — the base shape: one instance-implicit parameter
    solved from the explicit argument's type.
  * `tc/useWrapAscribed` — the same under an induced expected type, so
    `propagateExpectedType`'s `trySynthesizeAppInstMVars` call runs
    before the unification rather than after.
  * `tc/atUseWrap` — `@` with the instance supplied POSITIONALLY, the
    `processInstImplicitArg` branch that does NOT synthesize.
  * `tc/atUseWrapHole` — `@` with `_` in the instance position, which
    the oracle still resolves by synthesis (`nextArgHole?`,
    App.lean:905-911). The two `@` records together are the only
    coverage of that arm's split.
  * `tc/atWrapImplicit` — `@` with `_` in the ordinary IMPLICIT position
    too, so the explicit-mode arm is exercised for both binder kinds.
  * `tc/pairBoth` — a two-parameter class.
  * `tc/wrapWrap` — nested, so an instance goal is solved while another
    application is mid-flight.
  * `tc/wrapUnderFun`, `tc/funWrapElided`, `tc/letWrapElided` — an
    instance argument under each binder form M4b-2 shipped, so the
    Task 6 rewires are exercised by real records rather than by
    inspection. -/
def instImplicitQueries : List (String × String) :=
  [ ("tc/useWrapNat",      "useWrap Nat.zero")
  , ("tc/useWrapAscribed", "(useWrap Nat.zero : Nat)")
  , ("tc/atUseWrap",       "@useWrap Nat instWrapNat Nat.zero")
  , ("tc/atUseWrapHole",   "@useWrap Nat _ Nat.zero")
  , ("tc/atWrapImplicit",  "@useWrap _ instWrapNat Nat.zero")
  , ("tc/pairBoth",        "usePair Nat.zero Nat.zero")
  , ("tc/wrapWrap",        "useWrap (useWrap Nat.zero)")
  , ("tc/wrapUnderFun",    "fun (n : Nat) => useWrap n")
  , ("tc/funWrapElided",   "(fun x => useWrap x : Nat -> Nat)")
  , ("tc/letWrapElided",   "let x := useWrap Nat.zero; x")
  ]

/-- M4b-3 P3 task 6: numerals. `num/bare` is the whole point — a
numeral with NO expected type reaches the oracle's answer only through
the default-instance rung, so it is the first corpus record for which
`synthesizeSyntheticMVarsNoPostponing` does real work. It defaults to
`Nat` via `instOfNatNat` (priority 100), exactly as in real Lean;
`Elab0.lean` deliberately puts `instOfNatTag` BELOW it at 50 so that a
bare numeral cannot default to a fixture-only carrier while three
distinct priorities (1000 / 100 / 50) still keep the descending walk
differentially observable.

  * `num/ascribedNat` — an expected type that the default rung would
    have reached anyway, so it AGREES with `num/bare`. Kept as the
    control half of the ascription pair: it pins that propagating an
    expected type does not perturb the answer when the two coincide.
  * `num/ascribedTag` — an expected type reachable ONLY by ascription
    (`instOfNatTag` loses the priority walk). This is the record that
    discriminates propagation from defaulting: the expected type pins
    `?α` inside `mkFreshTypeMVarFor`, so the goal is ground, eager
    synthesis at `mkInstMVar` closes it, and the default rung never
    fires.
  * `num/hex`, `num/binary`, `num/octal`, `num/underscores` — token
    decoding, same elaborated shape as `num/bare` but a different
    `decodeNatLitVal?` radix path each. `0b`/`0o` had decoder unit
    tests (`builtin/lit/decode.rs`) but no differential record until
    the P3 fix wave, unlike `0x` and `_`, which had both; the four
    together now cover every radix prefix `decodeNatLitVal?` accepts.
    Each value is chosen to differ from its own decimal reading
    (`0b1010` is 10, not 1010; `0o52` is 42, not 52), so a decoder that
    ignored the prefix would change the emitted `rawNatLit` and the
    record would move;
  * `num/inApp` — a numeral as an APPLICATION ARGUMENT, where the
    parameter type fixes the carrier before the fixpoint runs, so
    eager synthesis at `mkInstMVar` closes the instance goal and the
    default rung never fires here either. The contrast with `num/bare`
    is what shows the ladder escalating only when it must;
  * `num/zero` — the `decodeNatLitVal?` single-`0` special case.
  * `num/zeroUnderBinder` (elimMVarDeps task 11 fix round 1) — `num/bare`'s
    default-instance walk with a BINDER around it, and the record that
    keeps rung 3's `mvarId.withContext` (`SyntheticMVars.lean:114`,
    `synthetic/default_inst.rs`) honest. `?α` and its `OfNat ?α 0` goal
    are minted in a context holding `n` and are still unassigned when
    `mkLambdaFVars` runs, so `elimMVarDeps`' plain-assign branch rewrites
    them to `?aux n`; rung 3's `isDefEq` against the default candidate
    then has to dereference `n` AFTER its binder has closed, which it can
    do only under the goal's own local context. Measured kill: drop the
    scoping and this record — with `dflt/polyInstImplicitUnderBinder` and
    nothing else — fails with `unknown free variable`. It elaborated
    correctly before `elimMVarDeps` was wired into `mk_binding` and
    regressed silently when it was, with no record to notice; this is
    that regression's executable memory. -/
def numQueries : List (String × String) :=
  [ ("num/bare",        "42")
  , ("num/zero",        "0")
  , ("num/hex",         "0x2A")
  , ("num/binary",      "0b1010")
  , ("num/octal",       "0o52")
  , ("num/underscores", "1_000_000")
  , ("num/ascribedNat", "(42 : Nat)")
  , ("num/ascribedTag", "(42 : Tag)")
  , ("num/inApp",       "pick 1 2")
  , ("num/zeroUnderBinder", "fun (n : Nat) => 0")
  ]

/-- M4b-3 P3 task 7: `char` and `scientific`.

`char/*` pins `elabCharLit`'s two decode paths (plain and escaped); the
elaborated shape is `Char.ofNat` applied to a raw literal in every case,
with no instance, no expected type and no universe level, so the
discrimination is entirely in the decoded code point. `Char`/`Char.ofNat`
are deliberate OPAQUE CARRIERS in `Elab0.lean` — `elabCharLit` never
reads `Char`'s shape, so the emitted `Expr` is byte-identical either
way. -/
def charQueries : List (String × String) :=
  [ ("char/plain",   "'a'")
  , ("char/newline", "'\\n'")
  , ("char/hex",     "'\\x41'")
  , ("char/unicode", "'\\u00e9'")
  ]

/-- `sci/*` pins `decodeScientificLitVal?`'s three exponent combinations
— dot only, positive written exponent, negative written exponent — since
those are what decide the emitted `sign`/`exponent` pair, plus the
mantissa/dot-digit accumulation that feeds them.

Every record is ascribed to `Tag`: `OfScientific` has exactly one
instance in the fixture and NO default instance, so an unascribed
scientific literal is a stuck typeclass problem the fixpoint reports and
the dumper drops. The ascription pins `?α` inside `mkFreshTypeMVarFor`,
so the goal is ground and eager synthesis at `mkInstMVar` closes it. -/
def scientificQueries : List (String × String) :=
  [ ("sci/dot",       "(1.5 : Tag)")
  , ("sci/dotTwo",    "(1.25 : Tag)")
  , ("sci/expPos",    "(121e100 : Tag)")
  , ("sci/expNeg",    "(1e-3 : Tag)")
  , ("sci/dotExpPos", "(1.5e2 : Tag)")
  , ("sci/dotExpNeg", "(1.5e-2 : Tag)")
    -- The THIRD arm of `decodeScientificLitVal?`'s exponent combination
    -- (`Init/Meta/Defs.lean:1023-1024`, the `else` of the `exp >= e`
    -- test at `:1021`): a positive written exponent
    -- SMALLER than the number of digits after the dot, which flips the
    -- sign back to negative — `1.25e1 -> (125, true, 1)`. The other two
    -- arms are covered by `sci/dotExpPos` (`exp >= e`) and
    -- `sci/dotExpNeg` (a negative written exponent); this one had a unit
    -- test in `builtin/lit/decode.rs` but no differential record, so the
    -- arm was measured against the decoder and not against the oracle.
    -- Added by M4b-3 P3 task 8.
  , ("sci/dotExpBelow", "(1.25e1 : Tag)")
  ]

/-- M4b-3 P2b-ii task 1: the fourth-priority default instance (design
spec § Follow-ups items 1-2, § Amendment 4 item 9). `useFresh` alone
leaves `Fresh ?α` pending with nothing else constraining `?α`, so the
default-instance walk descends 1000 → 100 → 75 and applies
`instFreshSeed`, which is universe-polymorphic AND carries an
`instImplicit` binder. The record therefore pins both the fresh-level
refresh (a rigid `param u` here instead of `lmvar` means
`mk_default_instance_candidate` built at the empty level list) and the
nested `synthesizePending` fixpoint (an `mvar` in the `Seed` argument
position means the candidate's instance-implicit binders were not
collected).

`dflt/polyInstImplicitUnderBinder` (elimMVarDeps task 11 fix round 1) is
the same walk under a binder, and is the SECOND half of rung 3's
`mvarId.withContext` gate — see `num/zeroUnderBinder` above for the full
diagnosis. It is kept alongside `num/zeroUnderBinder` rather than folded
into it because the two reach rung 3 by different routes: the numeral's
goal is `OfNat ?α 0` with a literal argument and a THREE-priority
descending walk behind it, while `Fresh ?α` descends to priority 75 and
its candidate carries an `instImplicit` binder of its own, so the
scoping has to survive the nested `synthesizePending` too. -/
def defaultPolyQueries : List (String × String) :=
  [ ("dflt/polyInstImplicit", "useFresh")
  , ("dflt/polyInstImplicitUnderBinder", "fun (n : Nat) => useFresh")
  ]

/-- M4b-3 P2b-ii: the elaborator outParam branch. The list below now
holds five records; the first three land BEFORE `Lean.Internal.coeM`
is declared (task 2 of the plan) and must stay byte-identical when it
is (task 5): in a one-term dump the
entry point's own fixpoint runs the same default instances the
`finalize` branch runs eagerly, so on these shapes the branch changes
WHEN `?elem` is assigned, not WHAT it is assigned. The two records that
DO change — `outParam/getElemUnderDflt` and `outParam/getElemAscribed`
— are appended by task 5 once the branch exists on both sides.

  * `outParam/getFst` — `getFst cell`: the `Get Cell Nat ?elem` goal at
    `finalize` has its only mvar in an OUTPUT-PARAMETER position. The
    oracle answers it (`preprocessOutParam` / `assignOutParams`); leanr
    needed the ladder pre-test's positional exemption. Without it the
    goal postpones forever and the fixpoint reports it stuck.
  * `outParam/getElem` — `Get.get cell 0`, the oracle's own worked
    example (App.lean:150-166). `?idx` is fixed by the `OfNat` default
    instance, then `Get Cell Nat ?elem` is solved with `?elem := Unit`
    assigned as a RESULT of synthesis.
  * `outParam/getElemIdxNat` — `Get.get cell (0 : Nat)`: the index is
    ground before `finalize`, so `synthesizeAppInstMVars` solves the
    instance goal there and the outParam is ALREADY ASSIGNED when the
    branch's guard runs — the else arm (App.lean:645-646).
  * `outParam/getElemUnderDflt` — `dpair (Get.get cell 0)`: THE record
    that makes the branch observable (design spec § Amendment 4 items
    10-11). With the branch, the inner application finalizes with
    `?elem := Unit`, so `dpair`'s `a := Unit` and `Dflt Unit` is
    `instDfltUnit`. Without it — including on the ORACLE, whenever
    `Lean.Internal.coeM` is absent from this fixture — `a := ?elem`
    stays open, the entry point's fixpoint reaches `Dflt ?elem` at
    priority 1000 FIRST and applies `instDfltNat`, and `Get Cell Nat
    Nat` has no instance: an error, and the dumper drops the query.
  * `outParam/getElemAscribed` — `(Get.get cell 0 : Unit)`: the
    producer disables expected-type propagation and the branch returns
    before `finalize`'s own unification, so `?elem` is fixed by the
    default rung and the ascription's `ensureHasType` merely checks it.
    The emitted term coincides with `outParam/getElem`; the MECHANISM
    is pinned by `tests/app_smoke.rs`'s walk-log test instead. -/
def outParamQueries : List (String × String) :=
  [ ("outParam/getFst",        "getFst cell")
  , ("outParam/getElem",       "Get.get cell 0")
  , ("outParam/getElemIdxNat", "Get.get cell (0 : Nat)")
  , ("outParam/getElemUnderDflt", "dpair (Get.get cell 0)")
  , ("outParam/getElemAscribed",  "(Get.get cell 0 : Unit)")
  ]

/-- M4b-3 P4 (design spec § P4, § Amendment 5 items 9-10): coercion
insertion. The dumper elaborates closed terms only, so a coerced value
that must be a local is written as a `fun` binder.
  * `coe/natToInt` — `(n : Int)` with `n : Nat`: `ensureHasType` →
    `mkCoe` → `CoeT Nat n Int` → `expandCoe` → `Int.ofNat n`. Dies if
    `expand_coe` is the identity (the term would carry `CoeT.coe`).
  * `coe/twoStep` — `(n : Big)`: solvable only through `CoeTC`'s
    transitive instance; emits `Big.ofInt (Int.ofNat n)`.
  * `coe/argPosition` — `takesInt n`: the `ensureArgType` site
    (`App.lean:54-62`), not the ascription site. Dies if `args.rs`'s
    rewire is reverted (`TypeMismatch`).
  * `coe/postponedThenResumed` — `pairW Nat.zero Nat.zero`: `CoeT Nat
    Nat.zero (Wrapper ?a)` is `.undef` at the first argument (`?a`
    unassigned), so `mkCoe` registers a `.coe` mvar; the second argument
    assigns `?a := Nat`; the entry point's fixpoint resumes the
    coercion (`SyntheticMVars.lean:552-560`). Dies if the ladder's `Coe`
    arm is reverted to its seam. Deliberately binder-FREE, unlike its
    three siblings: the same query under a `fun` (`fun (n : Nat) =>
    pairW n Nat.zero`) is a coercion resumed AFTER its binder closed,
    which the oracle handles inside `mkLambdaFVars` via
    `MkBinding.elimMVarDeps` (`MetavarContext.lean`). leanr's
    `mk_lambda` did not model that for two milestones and leaked the
    free variable where the oracle emits `bvar 0`; the elimMVarDeps
    slice ported it (`leanr_meta/src/mk_binding.rs`, wired into
    `MetaCtx::mk_binding`), so the under-a-binder form is now a record
    of its own — `coe/postponedThenResumedUnderBinder` below — instead
    of a carried gap. Full diagnosis in the M4b-3 P4 task-7 report.
  * `coe/funApp` (task 8) — `g Nat.zero` with `g : Fn`:
    `coerceToFunction?` in `synthesizePendingAndNormalizeFunType`.
  * `coe/sortDomain` (task 9) — `fun (c : Carrier) (x : c) => x`:
    `ensureType` → `coerceToSort?` on the binder domain.
  * `coe/postponedThenResumedUnderBinder` (elimMVarDeps task 11) — the
    same postpone-then-resume as `coe/postponedThenResumed`, but UNDER a
    binder: `CoeT Nat n (Wrapper ?a)` is `.undef` while `?a` is
    unassigned, so `mkCoe` registers a `.coe` mvar in a local context
    that contains `n`; `mkLambdaFVars` closes the binder BEFORE the
    fixpoint resumes the coercion. The oracle absorbs that inside
    `MkBinding.elimMVarDeps`, whose DELAYED branch (`:1216-1228`) is the
    only reason `n` comes back as `bvar 0` rather than a leaked `fvar`.
    Measured kill: make `elimMVar` take the plain-assign branch for
    `syntheticOpaque` too and this record is the one that moves. For two
    milestones leanr answered this shape wrongly and it could not be a
    record at all — `leanr_elab`'s `seam_audit.rs` carried the oracle's
    answer inline instead. -/
def coeQueries : List (String × String) :=
  [ ("coe/natToInt",             "fun (n : Nat) => (n : Int)")
  , ("coe/twoStep",              "fun (n : Nat) => (n : Big)")
  , ("coe/argPosition",          "fun (n : Nat) => takesInt n")
  , ("coe/postponedThenResumed", "pairW Nat.zero Nat.zero")
  , ("coe/funApp",               "fun (g : Fn) => g Nat.zero")
  , ("coe/sortDomain",           "fun (c : Carrier) (x : c) => x")
  , ("coe/postponedThenResumedUnderBinder", "fun (n : Nat) => pairW n Nat.zero")
  ]

/-- elimMVarDeps task 11: the differential record for the
`MkBinding.elimMVarDeps` mechanism that
`coe/postponedThenResumedUnderBinder` does NOT reach.

  * `elimMVarDeps/pendingInstanceUnderBinder` — the PLAIN-ASSIGN branch
    (`elimMVar`, `:1214-1215`). A two-binder telescope closed by ONE
    `mkLambdaFVars` call, with `x`'s domain ELIDED: `Wrap ?t` is
    therefore still `.undef` at `elabAppArgs`' finalization, and the
    instance argument survives to `mkLambdaFVars` as an unassigned
    NON-opaque (`MetavarKind.synthetic`) metavariable whose context
    holds both binders. `elimMVar` assigns it outright,
    `?inst := ?new n x`; the ascription then pins `?t := Nat` and the
    fixpoint solves `Wrap Nat` through that assignment. Measured kill:
    take the DELAYED branch for every kind and this record — and only
    this record — moves, because a `syntheticOpaque` delayed assignment
    is never resolved here: the elaborator that created `?inst` assigns
    `?inst` itself.

Two mechanisms named in the task-11 brief got NO record, deliberately,
because no source term can make them observable at this tier (both
measured; both keep the `crates/leanr_meta/src/mk_binding.rs` unit
tests that DO kill their mutations):

  * `getInScope`'s filter (`:1070-1077`) is subsumed by
    `collectForwardDeps` (`:1037-1062`), which iterates the
    METAVARIABLE's own local context and so re-drops anything
    `getInScope` would have dropped. Replacing `getInScope` with `xs`
    unfiltered leaves all 117 records byte-identical — re-measured at
    the shipped corpus size, including the two under-a-binder
    default-instance records, which are among the several that reach
    `elimMVar` with an EMPTY `getInScope` result, the one path where the
    two filters could differ. The only tests that fail workspace-wide
    are `get_in_scope_keeps_only_the_fvars_the_mvar_can_see` and
    `elim_mvar_deps_leaves_an_out_of_scope_metavariable_alone`.
  * `collectForwardDeps`' closure never adds anything here. leanr's
    elaborator only ever abstracts a CONTIGUOUS, most-recently-pushed
    telescope, so `to_revert` is always a suffix of the metavariable's
    own context and there is no later, unreverted declaration to pull
    in. A non-suffix reversion is the tactic framework's `revert`,
    which leanr has no producer for — the same reason
    `collect_forward_deps` does not model `preserveOrder`. Making it
    the identity leaves all 117 records byte-identical — re-measured at
    the shipped corpus size. The only tests that fail workspace-wide
    are `collect_forward_deps_pulls_in_a_dependent_later_decl` and
    `collect_forward_deps_closes_transitively_through_a_chain`. -/
def elimMVarDepsQueries : List (String × String) :=
  [ ("elimMVarDeps/pendingInstanceUnderBinder",
      "(fun (n : Nat) x => useWrap x : Nat -> Nat -> Nat)")
  ]

/-- M4b-3 P5 binder family: implicit / strict-implicit / instance-implicit
`fun` binders, multi-name groups, type-less binders, `optType`, and
expected-type propagation into binder domains. The `optType` queries are
amendment 4's replacements: `fun bs : T => e` maps `T` over the BINDERS
(`expandSimpleBinderWithType`), not the body — a non-ident/`_` binder makes
the real elaborator throw "unexpected type ascription", so the plan's
original `fun (x : Nat) : Nat => x` / `fun (a : Type) (x : a) : a => x`
forms are dropped in favour of the two that actually elaborate.

Type-less binders are queried only for the implicit case
(`fun {a} => a`, `p5/fun-implicit-untyped`); explicit/strict/instance
type-less variants are out of scope here — the brief's form list did not
call for them, and adding them is a separate decision, not an oversight
of this task.

`p5/propagate-short` is retained deliberately even though it produces NO
record: the oracle rejects `(fun x y => Nat.zero : Nat -> Nat)` with a
genuine type mismatch — two `fun` binders against a one-arrow expected
type leave the second binder's domain an unresolved metavariable, and
`(x : Nat) → ?m x → Nat` does not unify with `Nat → Nat`. Confirmed
independently against a full-Init environment, which renders the same
failure as a readable "Type mismatch ... but is expected to have type
Nat → Nat" rather than this file's opaque `internal exception #3`. Kept
here (not dropped) so the gap in `elab-queries.jsonl` reads as intentional
rather than a regen bug; every `fixtures:regen-elab` run re-emits this
query's `eprintln` for the same reason. -/
def p5BinderQueries : List (String × String) :=
  [ ("p5/fun-implicit",         "fun {a : Type} => a")
  , ("p5/fun-implicit-untyped", "fun {a} => a")
  , ("p5/fun-implicit-group",   "fun {a b : Type} => a")
  , ("p5/fun-strict",           "fun ⦃a : Type⦄ => a")
  , ("p5/fun-inst-named",       "fun [inst : Add Nat] => inst")
  , ("p5/fun-inst-anon",        "fun [Add Nat] => Nat.zero")
  , ("p5/fun-opttype",          "fun x : Nat => x")
  , ("p5/fun-opttype-group",    "fun x y : Nat => x")
  , ("p5/forall-inst",          "forall [inst : Add Nat], Nat")
  , ("p5/propagate-fn",         "(fun f => f Nat.zero : (Nat -> Nat) -> Nat)")
  , ("p5/propagate-two",        "(fun x y => x : Nat -> Nat -> Nat)")
    -- Oracle-rejected; see doc comment above. No record — do not "fix"
    -- this by editing the query.
  , ("p5/propagate-short",      "(fun x y => Nat.zero : Nat -> Nat)")
  ]

/-- M4b-3 P5 implicit-lambda insertion (`TermElabM.lean:1806-1820`). -/
def p5ImplicitLambdaQueries : List (String × String) :=
  [ ("p5/implam-one",    "(Nat.zero : {a : Type} -> Nat)")
  , ("p5/implam-inst",   "(Nat.zero : [inst : Add Nat] -> Nat)")
  , ("p5/implam-nested", "(Nat.zero : {a : Type} -> {b : Type} -> Nat)")
  ]

/-- M4b-3 P5 argument family: `optParam` defaults and an explicitly
supplied `autoParam` argument. An OMITTED autoParam is a reported seam,
not a record — executing the tactic is a later M4 slice. -/
def p5ArgQueries : List (String × String) :=
  [ ("p5/optparam-default",   "withDefault")
  , ("p5/optparam-explicit",  "@withDefault Nat.zero")
  , ("p5/autoparam-supplied", "withTactic Nat.zero")
  ]

/-- M4b-3 close-out: implementation-detail binders. The oracle gives a
user-written binder whose name's root component starts with `__` the kind
`.implDetail` (`LocalDeclKind.ofBinderName`, `Elab/BindersUtil.lean:21-25`),
and `withNewLocalInstanceImp` (`Meta/Basic.lean:1383-1388`) never installs
it as a local instance. Each `__` query below therefore elaborates against
the GLOBAL `instAddNat`; each `-twin` against the local binder.

The `let`/`have` twins landed after the close-out: until `elab_let_like`
instantiated the body before `mk_let_expr` (the oracle's `>>=
instantiateMVars`, `Elab/Binders.lean:824`), the local instance leaked an
unabstracted fvar, which `oracle_elab`'s leaked-fvar assertion rejects
(close-out spec § Amendment 2). -/
def closeoutImplDetailQueries : List (String × String) :=
  [ ("closeout/impl-detail-fun",           "fun (__i : Add Nat) => (Add.add Nat.zero Nat.zero : Nat)")
  , ("closeout/impl-detail-fun-twin",      "fun (i : Add Nat) => (Add.add Nat.zero Nat.zero : Nat)")
  , ("closeout/impl-detail-fun-inst",      "fun [__i : Add Nat] => (Add.add Nat.zero Nat.zero : Nat)")
  , ("closeout/impl-detail-fun-inst-twin", "fun [i : Add Nat] => (Add.add Nat.zero Nat.zero : Nat)")
  , ("closeout/impl-detail-forall",        "forall (__i : Add Nat), Eq (Add.add Nat.zero Nat.zero) Nat.zero")
  , ("closeout/impl-detail-forall-twin",   "forall (i : Add Nat), Eq (Add.add Nat.zero Nat.zero) Nat.zero")
  , ("closeout/impl-detail-let",           "let __i : Add Nat := instAddNat; (Add.add Nat.zero Nat.zero : Nat)")
  , ("closeout/impl-detail-have",          "have __i : Add Nat := instAddNat; (Add.add Nat.zero Nat.zero : Nat)")
  , ("closeout/impl-detail-let-twin",      "let i : Add Nat := instAddNat; (Add.add Nat.zero Nat.zero : Nat)")
  , ("closeout/impl-detail-have-twin",     "have i : Add Nat := instAddNat; (Add.add Nat.zero Nat.zero : Nat)")
  ]

/-- M4b-3 close-out: instance-binder forms the oracle ACCEPTS
(`elabBinderViews`, `Elab/Binders.lean:216-219`;
`checkLocalInstanceParameters`, `:199-206`). They pass on leanr before the
check exists and are here to catch a check that over-rejects: a
forward-dependent parameter, an instance-implicit parameter, a non-instance
binder (never checked), the depArrow spelling, and `fun` (whose
`elabFunBinderViews` runs no check at all). Rejected forms emit no record;
`binder_smoke.rs` pins them. -/
def closeoutBinderCheckQueries : List (String × String) :=
  [ ("closeout/binder-check-forward-dep",   "forall [i : forall (a : Type), Add a], Nat")
  , ("closeout/binder-check-inst-param",    "forall [i : forall [Add Nat], Add Nat], Nat")
  , ("closeout/binder-check-explicit",      "forall (i : Nat -> Add Nat), Nat")
  , ("closeout/binder-check-dep-arrow",     "[i : forall (a : Type), Add a] -> Nat")
  , ("closeout/binder-check-fun-unchecked", "fun [i : Nat] => i")
  ]

/-- M4b-3 close-out: `let`/`have`'s OWN binder list with implicit,
strict-implicit and instance binders (`elabLetDeclAux` →
`elabBindersEx`, `Elab/Binders.lean:745`, `:751`). The value is
abstracted over the binders, so `f`'s type carries their binder infos and
the body's `f` gets its instance / implicit arguments inserted. -/
def closeoutLetBinderQueries : List (String × String) :=
  [ ("closeout/let-inst-named",       "let f [i : Add Nat] : Nat := Add.add Nat.zero Nat.zero; f")
  , ("closeout/let-inst-anon",        "let f [Add Nat] : Nat := Add.add Nat.zero Nat.zero; f")
  , ("closeout/let-inst-impl-detail", "let f [__i : Add Nat] : Nat := Add.add Nat.zero Nat.zero; f")
  , ("closeout/let-implicit",         "let f {a : Type} (x : a) : a := x; f Nat.zero")
  , ("closeout/let-strict",           "let f ⦃a : Type⦄ (x : a) : a := x; f")
  , ("closeout/have-inst-named",      "have f [i : Add Nat] : Nat := Add.add Nat.zero Nat.zero; f")
  , ("closeout/have-implicit",        "have f {a : Type} (x : a) : a := x; f Nat.zero")
  ]

/-- M4b-3 close-out: `@($t)` / `@$t` elaborate `t` with
`implicitLambda := false` (`Elab/App.lean:2269-2270`). The flag covers
`t` itself, not its subterms (`Elab/Term/TermElabM.lean:1876-1877`), but
it survives macro expansion (`:1837`) and `paren` is a macro
(`expandParen`, `Elab/BuiltinNotation.lean:410`), hence the nested-paren
and subterm queries. `(fun (a : Type) => a : {a : Type} -> Type)` without
the `@` is a type mismatch in the oracle; with it, it elaborates. -/
def closeoutExplicitQueries : List (String × String) :=
  [ ("closeout/explicit-paren",        "(@(fun (a : Type) => a) : {a : Type} -> Type)")
  , ("closeout/explicit-nested-paren", "(@((fun (a : Type) => a)) : {a : Type} -> Type)")
  , ("closeout/explicit-subterm",      "(@(fun (a : Type) => (Nat.zero : {b : Type} -> Nat)) : {a : Type} -> {b : Type} -> Nat)")
  , ("closeout/explicit-no-expected",  "@(fun (a : Type) => a)")
  , ("closeout/explicit-implicit-fun", "(@(fun {a : Type} => Nat.zero) : {a : Type} -> Nat)")
  , ("closeout/explicit-app",          "@(Nat.succ Nat.zero)")
  ]

/-- The nondep slice (spec `2026-09-29-nondep-local-decls-design.md`).

`*-coe`: a `.coe` metavariable postponed inside a `let`/`have` body is
still UNASSIGNED when the binder closes, so `mk_let_expr` must run
`elim_mvar_deps` (`mkLetFVars` → `mkBinding` → `abstractRange`) or the
resumed coercion leaks the let-bound fvar. The `fun` twin of these is
`coe/postponedThenResumedUnderBinder`.

`let-rfl` guards the other direction: `whnf` still zeta-delta expands a
GENUINE let, so `rfl` typechecks here. Its `have` twin is rejected by
the oracle and is pinned by `binder_smoke.rs`'s
`a_have_bound_variable_is_opaque_to_defeq` instead — a rejected term
emits no record. -/
def nondepQueries : List (String × String) :=
  [ ("nondep/let-coe",  "let n : Nat := Nat.zero; pairW n Nat.zero")
  , ("nondep/have-coe", "have n : Nat := Nat.zero; pairW n Nat.zero")
  , ("nondep/let-rfl",  "let n : Nat := Nat.zero; (rfl : Eq n Nat.zero)")
  ]

/-- M4b-4a P1 task 5: `projIdx` (one-constructor `inductive`,
`App.lean:1533-1540`) and `elabAppFn`'s generic arm
(`App.lean:2120-2138`). Every one checked against the pinned oracle.

`generic-ellipsis` is the only record reaching the generic arm with no
arguments and no LVals (`..` is stripped by `expandApp`), where the oracle
returns `elabTerm f expectedType?` AS IS (`:2124-2132`) rather than
re-applying it through `elabAppArgs`, which would fill `Nat.succ`'s
explicit argument with `_`. A bare `(fun (x : Nat) => x)` does NOT reach
that arm: a paren term is dispatched to `elabParen`, never `elabAppFn`. -/
def lvalIdxQueries : List (String × String) :=
  [ ("lval/idx-one-second",       "fun (o : One) => o.2")
  , ("lval/idx-one-first",        "fun (o : One) => o.1")
  , ("lval/generic-paren-head",   "(Nat.succ) Nat.zero")
  , ("lval/generic-fun-head",     "(fun (x : Nat) => x) Nat.zero")
  , ("lval/generic-ellipsis",     "(Nat.succ) ..")
  ]

/-- M4b-4a P1 task 6: `projFn` (`App.lean:1857-1872`) — structure
fields by index and by name, inherited through subobjects
(`mkBaseProjections`, `App.lean:1700-1710`), chained, with explicit
universes (on the LAST component only, `App.lean:2071`), after
`consumeImplicits`, and through `resolveLValLoop`'s unfold retry
(`App.lean:1687-1694`). -/
def lvalFnQueries : List (String × String) :=
  [ ("lval/prod-fst-idx",        "fun (p : Prod Nat Nat) => p.1")
  , ("lval/prod-snd-idx",        "fun (p : Prod Nat Nat) => p.2")
  , ("lval/prod-fst-name",       "fun (p : Prod Nat Nat) => (p).fst")
  , ("lval/prod-mk-idx",         "(Prod.mk Nat.zero Nat.zero).1")
  , ("lval/subobject-idx",       "fun (s : S3) => s.1")
  , ("lval/inherited-field",     "fun (s : S3) => (s).a")
  , ("lval/idx-then-name",       "fun (s : S3) => (s).1.b")
  , ("lval/chain-idx",           "fun (s : S3) => s.1.1.1")
  , ("lval/dotted-field-token",  "fun (s : S3) => (s).toS2.toS1")
  , ("lval/diamond-direct",      "fun (d : D3) => (d).z")
  , ("lval/diamond-subobject",   "fun (d : D3) => (d).x")
  -- NOT the plan's `(s).a`: on the non-structure `S3Alias` a field NAME
  -- goes through `findMethod?` (`App.lean:1568`) before the unfold retry,
  -- and that is P3's (leanr seams, never retries a seam — plan Review
  -- Focus 2). A field INDEX fails `matchConstStructure` with a genuine
  -- error, so it reaches the retry in P1.
  , ("lval/unfold-alias-idx",    "fun (s : S3Alias) => (s).1.a")
  , ("lval/poly-idx",            "fun (q : Poly Nat) => q.1")
  , ("lval/poly-univ",           "fun (q : Poly Nat) => (q).val.{0}")
  , ("lval/field-univ-partial",  "fun (p : Prod Nat Nat) => (p).fst.{0}")
  , ("lval/consume-implicits",   "(@dflt).1")
  , ("lval/dotted-field-univ",   "fun (p : Prod Type (Poly Nat)) => (p).snd.val.{0}")
  -- `OfNat.ofNat : {α} → (n : Nat) → [self : OfNat α n] → α` has an
  -- EXPLICIT structure parameter `n`. With no positional arguments the
  -- `self`-dependency path (`App.lean:858-866`) would make it implicit
  -- anyway; with one, only `(self := x)`'s `numImplicitParams`
  -- (`App.lean:767-802`, `:1866`) keeps `Nat.zero` from filling `n`.
  , ("lval/explicit-param-idx",  "fun (x : OfNat Nat Nat.zero) => x.1")
  , ("lval/explicit-param-args", "fun (x : OfNat (Nat -> Nat) Nat.zero) => (x).ofNat Nat.zero")
  -- `@` on a projection head (`App.lean:2112`/`:2264`): `elabExplicit`
  -- hands the whole `@..` node to `elabAtom`, and `elabAppFn` strips the
  -- `@` and re-enters on the `proj` with `explicit := true`.
  , ("lval/explicit-proj",       "@(Prod.mk Nat.zero Nat.zero).1")
  -- Parametric, universe-polymorphic chain `PD extends PC extends PB`:
  -- `mkBaseProjections` (`App.lean:1700-1710`) applies each parent
  -- projection to the value's type arguments at the TYPE's universe
  -- levels, so dropping either changes the term.
  , ("lval/param-chain-1",       "fun (x : PC Nat Nat) => (x).b")
  , ("lval/param-chain-2",       "fun (x : PD Nat) => (x).b")
  , ("lval/param-chain-univ",    "fun (x : PC.{1,0} Type Nat) => (x).b")
  , ("lval/param-chain-args",    "fun (x : PD (Nat -> Nat)) => (x).b Nat.zero")
  -- A guillemet-escaped field name is its unescaped component.
  , ("lval/escaped-field",       "fun (s : S3) => (s).«a»")
  -- `@` in FUNCTION position on a projection head (`App.lean:2112-2114`).
  , ("lval/explicit-proj-fn",    "@(Prod.mk Nat.succ Nat.zero).fst Nat.zero")
  , ("lval/explicit-proj-impl",  "fun (x : FI) => @(x).f Nat Nat.zero")
  ]

/- M4b-4a P2: term-level postponement. Every record here elaborates
only because a subterm is POSTPONED and RESUMED by the fixpoint once its
type is known. The postponement is registered either by
`elabUsingElabFnsAux`'s catch of `Exception.postpone`
(TermElabM.lean:1635-1651) or, for `p2/implicit-lambda-postpone`, by
`elabTermAux`'s `.postpone` arm calling `postponeElabTerm` directly
(`:1843-1850`). -/
def p2Queries : List (String × String) :=
  -- `useImplicitLambda` returns `.postpone` for `x` (a local of type
  -- `?α`, expected `{a : Type} → Nat`, TermElabM.lean:1753-1778). The
  -- resume at rung 1 postpones again; rung 2's `withoutPostponing`
  -- elaborates `x` WITHOUT the implicit lambda (`:1853-1854`) and
  -- `ensureHasType` assigns `?α`. Result: `fun x => x`, no wrap.
  [ ("p2/implicit-lambda-postpone", "fun x => (x : {a : Type} -> Nat)")
  -- `resolveLValLoop`'s `tryPostponeIfMVar eType` (App.lean:1680): `x`'s
  -- type is `?α` until the application unifies it with `Prod Nat Nat`.
  , ("p2/lval-idx-applied",        "(fun x => x.1) (Prod.mk Nat.zero Nat.zero)")
  , ("p2/lval-name-applied",       "(fun x => (x).fst) (Prod.mk Nat.zero Nat.zero)")
  -- The inner `x.1` is postponed, then the outer `.1` postpones on the
  -- inner mvar's type: the catch RESTORES (dropping the inner mvar) and
  -- postpones the whole `(x.1).1` (TermElabM.lean:1635-1651). Monomorphic
  -- `S2`/`S1`, not nested `Prod`: leanr leaves `Prod.{max 0 0, 0}`
  -- unnormalized for `Prod.mk (Prod.mk ..) ..` with or without
  -- postponement (a pre-existing level gap, not P2's).
  , ("p2/lval-chain",              "(fun x => (x.1).1) (S2.mk (S1.mk Nat.zero) Nat.zero)")
  -- Postponed as an ARGUMENT, resumed under `x`'s binder (Review Focus 3).
  -- In `lval-two-binders` `y`'s type is given: with both binder types
  -- holes leanr fails `(fun x y => y) Nat.zero Nat.zero` too (a
  -- pre-existing gap on `y`'s `?Y x` type, not P2's).
  , ("p2/lval-in-arg",             "(fun x => Nat.succ x.1) (Prod.mk Nat.zero Nat.zero)")
  , ("p2/lval-two-binders",        "(fun x (y : Prod Nat Nat) => Prod.mk x.2 y.1) (Prod.mk Nat.zero Nat.zero) (Prod.mk Nat.zero Nat.zero)")
  -- `(e :)` drains its own postponements (`withSynthesize (postpone :=
  -- .no)`, BuiltinNotation.lean:433-435) — Review Focus 4.
  -- TWO postponements, both resumed: `x.2` (outer binder) and `y.1`
  -- (inner binder), each waiting for its own application to assign
  -- its binder type. Restores the coverage `lval-two-binders` lost.
  , ("p2/lval-two-postponements",  "(fun x => (fun y => Prod.mk x.2 y.1) (Prod.mk Nat.zero Nat.zero)) (Prod.mk Nat.zero Nat.zero)")
  , ("p2/lval-nested-synthesize",  "((fun x => x.1) (Prod.mk Nat.zero Nat.zero) :)")
  -- `outParam` is reducible: `isMVarApp (outParam ?m)` is true only
  -- through `whnfR` (TermElabM.lean:1375-1376). Monomorphic `One`: with
  -- `Prod Nat Nat` leanr leaves `outParam.{max 1 1}` unnormalized (the
  -- same pre-existing level gap as `lval-chain`). This record does not
  -- pin `whnfR`: without it, `resolveLValLoop`'s `unfoldDefinition?`
  -- retry reaches `?m` anyway (postpone_smoke.rs pins `is_mvar_app`).
  , ("p2/lval-reducible-alias",    "(fun (x : outParam _) => x.1) (One.mk Nat.zero Nat.zero)")
  -- `elabAppArgs`' `unless namedArgs.isEmpty && args.isEmpty do
  -- tryPostponeIfMVar fType` (App.lean:1366-1367): `f : ?α` is applied
  -- before the outer application assigns `?α := Nat → Nat`.
  , ("p2/app-fn-applied",          "(fun f => f Nat.zero) Nat.succ")
  , ("p2/app-fn-two-args",         "(fun f x => f x) Nat.succ Nat.zero")
  -- Not recorded: `(fun x f => f x.1) (Prod.mk ..) Nat.succ`. `f : ?β' x`
  -- after `elimMVarDeps`, and `?β' a =?= Nat → Nat` needs `numScopeArgs`
  -- constant approximation (ExprDefEq.lean:1271-1278), which leanr_meta
  -- lacks (fails identically without postponement:
  -- `(fun (x : Nat) f => f) Nat.zero Nat.succ` is `StuckCoercion`).
  ]

-- M4b-4a P3: generalized field notation (`findMethod?`, `addLValArg`,
-- App.lean:1453-1477, :1735-1829). Every source was run on the pinned
-- oracle while planning (plan § Measured oracle behaviour).
def p3Queries : List (String × String) :=
  [ ("p3/nat-succ",            "(Nat.zero).succ")
  , ("p3/nat-succ-chain",      "(Nat.zero).succ.succ")
  , ("p3/alias-field",         "fun (s : S3Alias) => (s).a")
  , ("p3/inherited-method",    "fun (s : S3) => (s).get")
  , ("p3/diamond-method",      "fun (d : D3) => (d).zz")
  , ("p3/c3-first",            "fun (q : OQ) => (q).m")
  , ("p3/c3-nonsubobject",     "fun (q : OQ) => (q).n")
  , ("p3/c3-order",            "fun (q : OQ) => (q).k")
  , ("p3/c3-deep",             "fun (q : OQ) => (q).e")
  , ("p3/param-base",          "fun (x : PD Nat) => (x).get")
  , ("p3/param-base-univ",     "fun (x : PD Nat) => (x).get.{0}")
  , ("p3/function-arg",        "(Nat.succ).twice Nat.zero")
  , ("p3/function-partial",    "fun (f : Nat -> Nat) => (f).twice")
  , ("p3/positional",          "fun (s : S1) => (s).addTo Nat.zero")
  , ("p3/named-eta",           "fun (s : S1) => (s).addTo")
  , ("p3/named-with-named",    "fun (s : S1) => (s).addTo (n := Nat.zero)")
  , ("p3/implicit-named",      "fun (s : S1) => (s).imp Nat.zero")
  , ("p3/explicit-positional", "fun (s : S1) => @(s).imp Nat.zero")
  , ("p3/reducible-param",     "fun (s : S1) => (s).ab")
  , ("p3/proj-then-method",    "fun (p : Prod Nat Nat) => (p).1.succ")
  , ("p3/method-then-method",  "fun (s : S1) => (s).get.succ")
  , ("p3/field-then-method",   "fun (s : S2) => (s).toS1.get")
  , ("p3/whnf-continuation",   "fun (s : S1) => (s).viaDef")
  , ("p3/coe-fun",             "fun (s : S1) => (s).viaFn")
  , ("p3/whnf-then-named",     "fun (s : S1) => (s).viaDef3")
  , ("p3/explicit-unusable-name", "fun (s : S1) => @(s).bad Nat.zero")
  ]

-- M4b-4a P4: identifier forms (`resolveName`'s field split,
-- TermElabM.lean:2170-2192; `elabAppFnResolutions`, App.lean:1926-1950;
-- `pipeProj`, App.lean:2085-2097, :2250-2258; `resolveDottedIdentFn`,
-- App.lean:1985-2058). Every source was run through this file's own
-- entry point while planning (plan § Measured oracle behaviour).
def p4Queries : List (String × String) :=
  [ ("p4/local-field",          "fun (p : Prod Nat Nat) => p.fst")
  , ("p4/local-field-chain",    "fun (p : Prod Nat Nat) => p.fst.succ")
  , ("p4/local-inherited",      "fun (s : S3) => s.a")
  , ("p4/local-method",         "fun (x : Nat) => x.succ")
  , ("p4/local-method-arg",     "fun (s : S1) => s.addTo Nat.zero")
  , ("p4/local-method-eta",     "fun (s : S1) => s.addTo")
  , ("p4/local-univ-last",      "fun (x : Poly Nat) => x.val.{0}")
  , ("p4/local-alias",          "fun (x : S3Alias) => x.a")
  , ("p4/local-function",       "fun (f : Nat -> Nat) => f.twice")
  , ("p4/local-shadows-global", "fun (Nat : Nat) => Nat.succ")
  , ("p4/global-field",         "Nat.zero.succ")
  , ("p4/global-field-chain",   "Nat.zero.succ.succ")
  , ("p4/global-function",      "Nat.succ.twice")
  , ("p4/global-field-plain",   "polyZero.val")
  , ("p4/global-univ-last",     "polyZero.val.{0}")
  , ("p4/pipe-idx",             "fun (p : Prod Nat Nat) => p |>.2")
  , ("p4/pipe-idx-univ",        "fun (p : Prod Nat Nat) => p |>.1.{0}")
  , ("p4/pipe-args",            "fun (s : S1) => s |>.addTo Nat.zero")
  , ("p4/pipe-named",           "fun (s : S1) => s |>.addTo (n := Nat.zero)")
  , ("p4/pipe-eta",             "fun (s : S1) => s |>.addTo")
  , ("p4/pipe-global",          "Nat.zero |>.succ")
  , ("p4/pipe-univ",            "fun (x : Poly Nat) => x |>.val.{0}")
  , ("p4/pipe-chain",           "fun (p : Prod Nat Nat) => p |>.1 |>.succ")
  , ("p4/pipe-fields",          "fun (p : Prod Nat Nat) => p |>.fst.succ")
  , ("p4/pipe-postponed",       "(fun x => x |>.1) (Prod.mk Nat.zero Nat.zero)")
  , ("p4/dot-ascribed",         "(.zero : Nat)")
  , ("p4/dot-arg",              "Nat.succ .zero")
  , ("p4/dot-pi",               "Function.twice .succ Nat.zero")
  , ("p4/dot-pi-ascribed",      "(.succ : Nat -> Nat)")
  , ("p4/dot-unfold",           "(.zero : NatAlias)")
  , ("p4/dot-pi-unfold",        "(.succ : Nat -> NatAlias)")
  , ("p4/dot-optparam",         "withDefault .zero")
  , ("p4/dot-postponed",        "Eq .zero Nat.zero")
  , ("p4/dot-args",             "(.mk Nat.zero Nat.zero : Prod Nat Nat)")
  , ("p4/dot-explicit",         "(@.mk Nat Nat Nat.zero Nat.zero : Prod Nat Nat)")
  , ("p4/dot-univs",            "(.mk.{0,0} Nat.zero Nat.zero : Prod Nat Nat)")
  , ("p4/dot-univ-prefix",      "(.mk.{0} Nat.zero Nat.zero : Prod Nat Nat)")
  , ("p4/dot-partial",          "(.mk : Nat -> Nat -> Prod Nat Nat)")
  , ("p4/dot-nested",           "(.mk .zero .zero : Prod Nat Nat)")
  -- A `|>.` with arguments as the base of another `|>.`: `elabAppFn`'s
  -- pipeProj patterns (App.lean:2085-2097) have no `$args*`, so the inner
  -- node takes the generic arm (:2120-2138) and keeps its arguments.
  , ("p4/pipe-nested-args",     "fun (s : S1) => s |>.addTo Nat.zero |>.succ")
  , ("p4/pipe-nested-named",    "fun (s : S1) => s |>.addTo (n := Nat.zero) |>.succ")
  , ("p4/pipe-nested-deep",     "fun (s : S1) => s |>.addTo Nat.zero |>.succ |>.succ")
  ]

-- M4b-4b task 1: the anonymous constructor, exact arity (no flattening).
-- `elabAnonymousCtor`, BuiltinNotation.lean:43-102. Every source was run
-- through the pinned oracle while writing the design spec (§ Evidence).
def anonQueries : List (String × String) :=
  [ ("anon/prod",            "(⟨Nat.zero, Nat.zero⟩ : Prod Nat Nat)")
  , ("anon/nestedExplicit",  "(⟨Nat.zero, ⟨Nat.zero, Nat.zero⟩⟩ : Prod Nat (Prod Nat Nat))")
  , ("anon/implicitField",   "(⟨Nat.zero⟩ : ImpI)")
  , ("anon/exists",          "(⟨Nat.zero, Eq.refl Nat.zero⟩ : Exists (fun n : Nat => Eq n Nat.zero))")
  , ("anon/and",             "(⟨True.intro, True.intro⟩ : And True True)")
  , ("anon/punit",           "(⟨⟩ : PUnit)")
  , ("anon/unitAlias",       "(⟨⟩ : Unit)")
  , ("anon/postponed",       "sameAs ⟨Nat.zero, Nat.zero⟩ (Prod.mk Nat.zero Nat.zero)")
  , ("anon/nestedPostponed", "sameAs ⟨Nat.zero, ⟨Nat.zero, Nat.zero⟩⟩ (Prod.mk Nat.zero (Prod.mk Nat.zero Nat.zero))")
  , ("anon/arg",             "Prod.fst ⟨Nat.zero, Nat.zero⟩")
  , ("anon/implicitLambda",  "(⟨Nat.zero, Nat.zero⟩ : {α : Type} -> Prod Nat Nat)")
  , ("anon/trivia",          "(⟨Nat.zero /- c -/ ,   Nat.zero⟩ : Prod Nat Nat)")
  ]

-- M4b-4b task 2: flattening (`BuiltinNotation.lean:92-96`), including a
-- tail that postpones on `?β` and resumes as the tail
-- (`anon/tailPostponed`), and the same under a binder whose fvar the
-- resumed tail must see through its saved context.
def anonTailQueries : List (String × String) :=
  [ ("anon/flat1",            "(⟨Nat.zero, Nat.zero, Nat.zero⟩ : Prod Nat (Prod Nat Nat))")
  , ("anon/flat2",            "(⟨True.intro, True.intro, True.intro, True.intro⟩ : And True (And True (And True True)))")
  , ("anon/tailPostponed",    "sameAs (⟨Nat.zero, Nat.zero, Nat.zero⟩ : Prod Nat _) (Prod.mk Nat.zero (Prod.mk Nat.zero Nat.zero))")
  , ("anon/tailUnderBinder",  "fun (n : Nat) => sameAs (⟨n, n, n⟩ : Prod Nat _) (Prod.mk n (Prod.mk n n))")
  , ("anon/flatK1",           "(⟨Nat.zero, Nat.zero⟩ : PB (Prod Nat Nat))")
  ]

-- `expandFunBinders` (`Lean/Elab/Binders.lean:360-406`): `_` hole
-- binders, `(a b : T)` / `(_ : T)` / `(x :)` type-ascription groups, and
-- `(x y)` / `(x)` paren groups (hole-typed, taken as binders only when no
-- ident resolves to a global constant). The pattern fallback
-- (`processAsPattern`, a `match`) belongs to the match slice and has no
-- record here.
def funExpandQueries : List (String × String) :=
  [ ("funx/hole",           "(fun _ x => x : Nat → Nat → Nat)")
  , ("funx/holeElided",     "fun _ (x : Nat) => x")
  , ("funx/ascGroup",       "fun (a b : Nat) => a")
  , ("funx/ascGroupSecond", "fun (a b : Nat) => b")
  , ("funx/ascGroupHole",   "fun (_ b : Nat) => b")
  , ("funx/ascHole",        "fun (_ : Nat) => Nat.zero")
  , ("funx/ascGroupDep",    "fun (α β : Type) (x : α) (y : β) => x")
  , ("funx/ascNoType",      "(fun (x :) => x : Nat → Nat)")
  , ("funx/parenGroup",     "(fun (x y) => y : Nat → Bool → Bool)")
  , ("funx/parenSingle",    "(fun (x) => x : Nat → Nat)")
  , ("funx/parenHole",      "(fun (_) => Nat.zero : Bool → Nat)")
  , ("funx/mixed",          "fun {a} (b c : a) _ => b")
  ]

-- M4b-4c P2: eliminator-headed applications (`ElabElim`). Each row was
-- run on the pinned oracle at plan time. Spec § Evidence lists the
-- terms these exercise.
--
-- Binder spelling: these use `_` hole binders and `(a b : T)` groups as
-- originally planned. (M4b-4c P2 had respelled them, `hbN` and
-- `(a : T) (b : T)`, until `fun.rs` ported `expandFunBinders`.) `elim/namedMotiveBareIh` and `elim/explicitAtBareIh` are
-- `elim/namedMotive`/`elim/explicitAt` without the `(ih : Nat)`
-- annotation: `ih`'s binder type then comes from a redex nested under the
-- minor's arrow, which `instantiateBetaRevRange` must beta (it closed a
-- silent leanr divergence).
-- `elim/eqRecTwoDiscrs` exercises two discriminants. `elim/ndrec` and
-- `elim/ndrecExpected` take the standard app path (`Eq.ndrec` is not an
-- eliminator) and need `setElabConfig`'s foApprox: with
-- `foApprox := false` the oracle rejects them ("Application type
-- mismatch" / "Type mismatch"). The bare form unifies at the argument,
-- the ascribed form at the expected type.
def elimQueries : List (String × String) :=
  [ ("elim/rec",           "fun (n : Nat) => (Nat.rec Nat.zero (fun _ ih => Nat.succ ih) n : Nat)")
  , ("elim/casesOn",       "fun (n : Nat) => (Nat.casesOn n Nat.zero (fun m => m) : Nat)")
  , ("elim/recOn",         "fun (n : Nat) => (Nat.recOn n Nat.zero (fun _ ih => ih) : Nat)")
  , ("elim/brecOn",        "fun (n : Nat) => (Nat.brecOn n (fun _ _ => Nat.zero) : Nat)")
  , ("elim/namedMotive",   "fun (n : Nat) => Nat.rec (motive := fun _ => Nat) Nat.zero (fun _ (ih : Nat) => ih) n")
  , ("elim/explicitAt",    "fun (n : Nat) => @Nat.rec (fun _ => Nat) Nat.zero (fun _ (ih : Nat) => ih) n")
  , ("elim/namedMotiveBareIh", "fun (n : Nat) => Nat.rec (motive := fun _ => Nat) Nat.zero (fun _ ih => ih) n")
  , ("elim/explicitAtBareIh",  "fun (n : Nat) => @Nat.rec (fun _ => Nat) Nat.zero (fun _ ih => ih) n")
  , ("elim/ellipsis",      "Nat.rec ..")
  , ("elim/hRec",          "fun (h : False) => (h.rec : Nat)")
  , ("elim/hRecArg",       "fun (h : False) => Nat.succ h.rec")
  , ("elim/falseRecHole",  "fun (h : False) => (False.rec _ h : Nat)")
  , ("elim/falseRecMotive","fun (h : False) => (False.rec (fun _ => Nat) h : Nat)")
  , ("elim/subst",         "fun (a b : Nat) (h : Eq a b) (p : Eq a a) => (Eq.subst' h p : Eq a b)")
  , ("elim/natElimUnder",  "(natElim Nat.zero (fun _ ih => ih) : Nat → Nat)")
  , ("elim/natElimNamedMajor", "fun (m : Nat) => (natElim (n := m) Nat.zero (fun _ ih => ih) : Nat)")
  , ("elim/preElim",       "fun (n : Nat) (z : Eq Nat.zero Nat.zero) => (preElim Nat.zero z n : Eq n n)")
  , ("elim/dotRec",        "fun (n : Nat) => (.rec Nat.zero (fun _ ih => ih) n : Nat)")
  , ("elim/overApp",       "fun (n : Nat) => (Nat.rec (fun m => m) (fun _ ih m => ih m) n Nat.zero : Nat)")
  , ("elim/overAppDep",    "fun (n : Nat) => (Nat.rec (fun m => Eq.refl m) (fun _ ih m => ih m) n Nat.zero : Eq Nat.zero Nat.zero)")
  , ("elim/overPostponed", "fun (n : Nat) => (Nat.rec (fun m => m) (fun _ ih m => ih m) n (sameAs Nat.zero Nat.zero) : Nat)")
  , ("elim/postponed",     "fun (n : Nat) => sameAs (Nat.rec Nat.zero (fun _ ih => ih) n) n")
  , ("elim/argPos",        "fun (n : Nat) => Nat.succ (Nat.rec Nat.zero (fun _ ih => ih) n)")
  , ("elim/univ",          "fun (n : Nat) => (Nat.rec.{1} Nat.zero (fun _ ih => ih) n : Nat)")
  , ("elim/listRec",       "fun (l : List Nat) => (List.rec Nat.zero (fun _ _ ih => ih) l : Nat)")
  , ("elim/ndrec",         "fun (a : Nat) (p : Eq a a) (h : Eq a a) => Eq.ndrec p h")
  , ("elim/ndrecExpected", "fun (a b : Nat) (h : Eq a b) (p : Eq a a) => (Eq.ndrec p h : Eq a b)")
  , ("elim/eqRecTwoDiscrs", "fun (a b : Nat) (h : Eq a b) (p : Eq a a) => (Eq.rec p h : Eq a b)")
  , ("elim/letDiscr",      "fun (n : (let x := Nat.zero; Nat)) => (Nat.rec Nat.zero (fun _ ih => ih) n : Nat)")
  , ("elim/letDiscrUsed",  "fun (n : (let x := Nat; x)) => (Nat.rec Nat.zero (fun _ ih => ih) n : Nat)")
  , ("elim/letOver",       "fun (n : Nat) (m : (let x := Nat.zero; Nat)) => (Nat.rec (fun k => k) (fun _ ih k => ih k) n m : Nat)")
  ]

-- M4b-4c P2: queries the oracle REJECTS. Emitted as `{"id","src","err"}`,
-- where `err` is the first line of the first logged message. The oracle
-- logs through `errToSorry` and then aborts with an internal exception,
-- so the thrown exception's own text is only the fallback.
def elimErrQueries : List (String × String) :=
  [ ("elimErr/noExpected",          "fun (n : Nat) => Nat.rec Nat.zero (fun _ ih => ih) n")
  , ("elimErr/mvarExpected",        "fun (n : Nat) => (Nat.rec Nat.zero (fun _ ih => ih) n : _)")
  , ("elimErr/insufficient",        "(preElim : Nat)")
  , ("elimErr/insufficientExpected","fun (h : False) => (False.rec : Nat)")
  , ("elimErr/insufficientDomain",  "(natElim Nat.zero (fun _ ih => ih) : Bool → Nat)")
  , ("elimErr/unusedNamed",         "fun (n : Nat) => (Nat.rec (foo := Nat.zero) Nat.zero (fun _ ih => ih) n : Nat)")
  , ("elimErr/overAppIncorrect",    "fun (n : Nat) (p : Eq Nat.zero Nat.zero) => (Nat.rec (fun _ => p) (fun _ ih _ => ih Nat.zero) n Nat.zero : Eq p p)")
  , ("elimErr/motiveIncorrect",     "fun (n : Nat) (p : Eq n n) => (Nat.rec p (fun _ ih => ih) n : Eq p p)")
  , ("elimErr/invalidMotive",       "fun (a b : Nat) (h : Eq a b) (p : Eq a a) => (Eq.subst' h p : Nat)")
  ]

/-- macro/binop% P2: notations whose Init expansion is a plain
application (`∧ ∨ ¬ ↔ <->`), elaborated against `ElabOp`
(`lean --run dump_elab.lean ElabOp`). The `binop%`-family rows' records
land in P3. Every query here was checked against the oracle on
2026-10-02. -/
def opQueries : List (String × String) :=
  [ ("op/and",              "True ∧ False")
  , ("op/and-ascii",        "True /\\ False")
  , ("op/or",               "True ∨ False")
  , ("op/or-ascii",         "True \\/ False")
  , ("op/not",              "¬ True")
  , ("op/iff",              "True ↔ False")
  , ("op/iff-ascii",        "True <-> False")
  -- precedence: `∧` (35) binds tighter than `∨` (30)
  , ("op/prec",             "True ∧ False ∨ True")
  , ("op/nested-paren",     "¬ (True ∧ False) ∨ True")
  , ("op/under-binder",     "fun (p q : Prop) => p ∧ q → q ∧ p")
  , ("op/iff-of-and",       "fun (p q : Prop) => p ∧ q ↔ q ∧ p")
  , ("op/not-local",        "fun (p : Prop) => ¬ p")
  -- hygiene: the expansion's `And` is the global, not the local
  , ("op/hygiene",          "fun (And : Nat) => True ∧ False")
  -- implicit-lambda position: the wrap runs, then the expansion inside it
  , ("op/implicit-lambda",  "fun (g : ({α : Type} → Prop) → Prop) => g (True ∧ False)")
  -- … with no paren around the notation: `g (t)` above reaches the
  -- wrap as a `paren`, whose elaborator re-enters `elab_term` inside it,
  -- so only this one has the wrap dispatch the expansion directly
  , ("op/implicit-lambda-bare", "(True ∧ False : {α : Type} → Prop)")
  -- `@(t)`: elabTerm t (implicitLambda := false); the hook must still run
  , ("op/explicit-paren",   "@(True ∧ False)")
  -- an operand postponed (lval on an mvar-typed local) and resumed
  , ("op/postponed-operand", "(fun x => x.1 ∧ True) (PProd.mk True True)")
  , ("op/as-arg",           "And True (True ∨ False)")
  , ("op/ascribed",         "(True ∧ False : Prop)")
  -- macro/binop% P3 T3: the `binop%` elaborator (Extra.lean:154-482).
  -- `a + b * c`: one tree through the nested expansion
  , ("op/add-mul",          "fun (a b c : Nat) => a + b * c")
  -- leaf coercion to the max type, both orders
  , ("op/coe-left",         "fun (n : Nat) (z : Z) => n + z")
  , ("op/coe-right",        "fun (n : Nat) (z : Z) => z + n")
  -- unknown `0` becomes `(0 : Z)`, not `↑(0 : Nat)` (Extra.lean:286-287)
  , ("op/unknown-numeral",  "fun (n : Nat) (z : Z) => (n + 0) + z")
  -- `2` stays uncoerced; `has_homogeneous_instance` is false (no `HMul Arr³`).
  -- `op/hetero-default-homog` is the row that exercises
  -- `has_heterogeneous_default_instances`
  , ("op/hetero-default",   "fun (a : Arr Nat) => 2 * a")
  -- `rightact%` leaves the exponent a leaf, outside the analysis
  , ("op/rightact-pow",     "fun (n : Nat) (z : Z) => z ^ n")
  , ("op/rightact-pow-lit", "fun (z : Z) => z ^ 2")
  -- uncomparable `Nat`/`U`: plain elaboration through `HAdd Nat U U`
  , ("op/uncomparable",     "fun (n : Nat) (u : U) => n + u")
  -- depth/stuck rows, under `fun` binders (restored by the checkAssignment
  -- slice: they had been respelled over closed constants because of the
  -- elimMVarDeps / isSubPrefixOf gap). The `-closed` spellings over the
  -- suffix constants (`vx`, `k0`, `fx`, `z0`) are kept: same paths, no binder.
  -- depth: `V n =?= V ?m` must NOT assign the outer `?m` -> uncomparable
  , ("op/depth",            "fun (n k : Nat) (x : V n) => x + (V.mk : V _) + k")
  , ("op/depth-mid",        "fun (n k : Nat) (x : V n) => x + k + (V.mk : V _)")
  , ("op/depth-closed",     "vx + (V.mk : V _) + k0")
  , ("op/depth-mid-closed", "vx + k0 + (V.mk : V _)")
  -- isDefEqStuckEx: `F n =?= F ?m` stuck -> uncomparable
  , ("op/stuck",            "fun (n : Nat) (x : F n) (z : Z) => x + F.mk _ + z")
  , ("op/stuck-closed",     "fx + F.mk _ + z0")
  -- … and with no mvar the same types ARE comparable: `x` is coerced
  , ("op/coe-unfold",       "fun (n : Nat) (x : F n) (z : Z) => x + z")
  -- binop_lazy%: the rhs is `fun _ : Unit => b`
  , ("op/lazy-orelse",      "fun (a b : Z) => a <|> b")
  , ("op/lazy-andthen",     "fun (a b : Z) => a >> b")
  -- the remaining binop rows of the table
  , ("op/lor",              "fun (a b : Z) => a ||| b")
  , ("op/xor",              "fun (a b : Z) => a ^^^ b")
  , ("op/land",             "fun (a b : Z) => a &&& b")
  , ("op/sub",              "fun (a b : Z) => a - b")
  , ("op/div",              "fun (a b : Z) => a / b")
  , ("op/mod",              "fun (a b : Z) => a % b")
  , ("op/append",           "fun (a b : Z) => a ++ b")
  -- unop%, and a coerced operand under it
  , ("op/neg",              "fun (a : Z) => -a")
  , ("op/neg-coe",          "fun (n : Nat) (z : Z) => -n + z")
  -- leftact%: the lhs is a leaf
  , ("op/smul",             "fun (n : Nat) (a : Z) => n • a")
  -- the literal forms, and a literal head that is a LOCAL (resolveId?)
  , ("op/literal-binop",    "fun (a b : Nat) => binop% HAdd.hAdd a b")
  , ("op/literal-unop",     "fun (a : Z) => unop% Neg.neg a")
  , ("op/literal-local-head", "fun (f : Nat → Nat → Nat) (a b : Nat) => binop% f a b")
  -- the expected type seeds `max`
  , ("op/expected",         "fun (n : Nat) => (n + 1 : Z)")
  , ("op/nested-coe",       "fun (n : Nat) (z : Z) => n * n + z")
  -- hygiene: a local named like the head's namespace does not capture it
  , ("op/hygiene-op",       "fun (HAdd : Nat) (a b : Nat) => a + b")
  , ("op/numerals",         "2 + 3")
  -- an mvar expected type (the argument of `id`) and a beta-redex argument
  , ("op/id-arg",           "fun (a b : Nat) => id (a + b)")
  , ("op/beta-arg",         "fun (z : Z) => (fun x => x) (z + 1)")
  -- a leaf that postpones (lval on an mvar-typed local) and resumes in
  -- `toTree`'s `synthesizeSyntheticMVars (postpone := .yes)`
  , ("op/postponed-binop-operand", "(fun x => x.1 + 0) (PProd.mk 1 2)")
  -- checkAssignment slice (spec 2026-10-02 § Evidence): a binder-local
  -- mvar must not be assigned to an outer one (isSubPrefixOf + ctxApprox).
  , ("op/binder-F-hole",    "fun (n : Nat) (x : F n) => x + F.mk _")
  , ("meta/at-hadd-V",      "fun (n : Nat) => @HAdd.hAdd _ _ _ _ (V.mk : V n) (V.mk : V _)")
  , ("meta/beta-lt",        "(fun a => LT.lt a 2) z0")
  , ("meta/beta-add",       "(fun a => a + 2) z0")
  , ("meta/beta-beq",       "(fun a => BEq.beq a 2) z0")
  , ("op/rel-lt-beta",      "(fun a => a < 2) z0")
  -- eta slice: `mkLambdaFVarsWithLetDeps` eta-reduces (`etaReduce :=
  -- true`, ExprDefEq.lean:551,554). `?f a =?= g a` with `a` outside
  -- `?f`'s ctx is a Miller pattern: `?f := g`, not `fun a => g a`.
  , ("meta/eta-congrFun'",  "fun (g : Nat → Nat) => (congrFun' _ : ∀ (a : Nat), g a = g a)")
  , ("meta/eta-congrFun",   "fun (g : Nat → Nat) => (congrFun _ : ∀ (a : Nat), g a = g a)")
  , ("meta/eta-partial",    "fun (g : Nat → Nat → Nat) => (congrFun' _ : ∀ (a : Nat), g 0 a = g 0 a)")
  , ("meta/eta-blocked",    "fun (g : Nat → Nat → Nat) => (congrFun' _ : ∀ (a : Nat), g a a = g a a)")
  -- mutation-killing rows: `2` stays uncoerced behind a HOMOGENEOUS
  -- instance (`op/hetero-default` never reaches the leaves: no
  -- `HMul (Arr Nat)³`); a regular `binop%` whose max has no homogeneous
  -- instance (`HPow Z Z Z`) elaborates its sides separately; a `leftact%`
  -- lhs is a LEAF, so `n + z` gets its own analysis (coerce `n`)
  , ("op/hetero-default-homog", "fun (a : MArr Nat) => 2 * a")
  , ("op/homog-literal-pow", "fun (n : Nat) (z : Z) => binop% HPow.hPow z n")
  , ("op/smul-op-lhs",      "fun (n : Nat) (z a : Z) => (n + z) • a")
  -- macro/binop% P3 T4: `binrel%`/`binrel_no_prop%` (Extra.lean:497-562)
  -- coercion at the relation, `isPred := true`
  , ("op/eq-coe",           "fun (n : Nat) (z : Z) => n = z")
  , ("op/lt-coe",           "fun (n : Nat) (z : Z) => n < z")
  -- the rest of the relation rows of the table
  , ("op/ge",               "fun (a b : Z) => a ≥ b")
  , ("op/ge-ascii",         "fun (a b : Z) => a >= b")
  , ("op/le",               "fun (a b : Z) => a ≤ b")
  , ("op/le-ascii",         "fun (a b : Z) => a <= b")
  , ("op/gt",               "fun (a b : Z) => a > b")
  , ("op/beq-coe",          "fun (n : Nat) (z : Z) => n == z")
  , ("op/bne-coe",          "fun (n : Nat) (z : Z) => n != z")
  , ("op/ne-coe",           "fun (n : Nat) (z : Z) => n ≠ z")
  -- binrel_no_prop%: a `Prop` max type becomes `Bool` (decide)
  , ("op/beq-prop",         "True == False")
  , ("op/bne-prop",         "True != False")
  , ("op/beq-prop-bool",    "fun (b : Bool) => True == b")
  -- the uncomparable path's `toBoolIfNecessary` (no row above reaches it)
  , ("op/beq-uncomparable-prop", "fun (n : Nat) (u : U) => (binop% PU n u) == True")
  -- uncomparable operands: plain elaboration + `ensureHasType`
  , ("op/rel-uncomparable", "fun (n : Nat) (u : U) => (n + u) = u")
  -- an op tree under a relation, and an unknown numeral side
  , ("op/rel-nested",       "fun (n : Nat) (z : Z) => n + n < z")
  , ("op/rel-numeral",      "fun (z : Z) => 2 < z")
  , ("op/rel-id-arg",       "fun (a b : Nat) => id (a < b)")
  -- a KNOWN expected type, which the analysis must ignore (`analyze tree none`)
  , ("op/rel-expected",     "fun (n : Nat) (z : Z) => (n = z : Prop)")
  -- `withSynthesizeLight` (Extra.lean:499-528): no default instance inside the
  -- relation, so `2 : ?α` waits for the postponed `x.1` (fixed by the
  -- argument) instead of becoming `Nat`. The `(fun a => a < 2) z0`
  -- spelling is covered by `op/rel-lt-beta` (checkAssignment slice).
  , ("op/rel-no-default",   "(fun x => x.1 < 2) (PProd.mk z0 z0)")
  -- Review Focus #5: relation operands are LEAVES of the outer tree
  , ("op/rel-of-rels",      "fun (a b : Nat) => (a < b) = (b < a)")
  -- ... and only a coercing inner relation tells: as a binop subtree,
  -- `LT.lt` has no homogeneous instance, so `n` would go uncoerced
  , ("op/rel-of-coe-rels",  "fun (n : Nat) (z : Z) => (n < z) = (z < n)")
  -- the same through literal `binrel%` operands (`toTree.go`'s literal arm)
  , ("op/rel-of-literal-rels", "fun (n : Nat) (z : Z) => (binrel% LT.lt n z) = (binrel% LT.lt z n)") ]

/-- macro/binop% P3: op queries the ORACLE rejects (`{"id","src","err"}`). -/
def opErrQueries : List (String × String) :=
  [ ("op/unknown-binop",    "fun (a b : Nat) => binop% NoSuch a b")
  , ("op/unknown-binrel",   "fun (a b : Nat) => binrel% NoSuch a b") ]

def emitErr (id src err : String) : IO Unit :=
  IO.println <| Json.compress <| Json.mkObj [("id", id), ("src", src), ("err", err)]

def emit (id src : String) (expJ : Json) : IO Unit :=
  IO.println <| Json.compress <| Json.mkObj [("id", id), ("src", src), ("exp", expJ)]

unsafe def main (args : List String) : IO Unit := do
  -- `lean --run dump_elab.lean` → Elab0's corpus; `… ElabOp` → the op corpus.
  let (mod, queries, errQueries) : Name × List (String × String) × List (String × String) :=
    match args with
    | ["ElabOp"] => (`ElabOp, opQueries, opErrQueries)
    | _ => (`Elab0, strQueries ++ identQueries ++ sortAscHoleQueries ++ binderQueries ++ funQueries ++ letQueries ++ haveQueries ++ appExplicitQueries ++ appImplicitQueries ++ appPropagateQueries ++ appNamedQueries ++ appExplicitModeQueries ++ instImplicitQueries ++ numQueries ++ charQueries ++ scientificQueries ++ defaultPolyQueries ++ outParamQueries ++ coeQueries ++ elimMVarDepsQueries ++ p5BinderQueries ++ p5ImplicitLambdaQueries ++ p5ArgQueries ++ closeoutImplDetailQueries ++ closeoutBinderCheckQueries ++ closeoutLetBinderQueries ++ closeoutExplicitQueries ++ nondepQueries ++ lvalIdxQueries ++ lvalFnQueries ++ p2Queries ++ p3Queries ++ p4Queries ++ anonQueries ++ anonTailQueries ++ funExpandQueries ++ elimQueries, elimErrQueries)
  -- Must run before any `importModules (loadExts := true)` or the
  -- import throws internally (dump_syntax_elab.lean's module doc, same
  -- pitfall, confirmed here empirically by `dump_defeq.lean`).
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := mod }] {} (trustLevel := 0) (loadExts := true)
  let coreCtx : Core.Context := { fileName := "<dump_elab>", fileMap := default }
  let coreState : Core.State := { env }
  let go : MetaM Unit := do
    for (id, src) in queries do
      match Lean.Parser.runParserCategory env `term src with
      | .error msg => IO.eprintln s!"dump_elab: parse error for {id}: {msg}"
      | .ok stx =>
        try
          -- M4b-3 P2a: the entry point now matches
          -- `crates/leanr_elab`'s `elab_term_and_synthesize` —
          -- elabTerm, then the fixpoint, then instantiateMVars. The
          -- fixpoint is what forces stuck typeclass problems to be
          -- reported rather than emitted as dangling mvars.
          let e ← (do
            let e ← Lean.Elab.Term.elabTerm stx none
            Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
            instantiateMVars e).run'
          let expJ := (encExpr e).run' {}
          emit id src expJ
        catch ex =>
          let msg ← ex.toMessageData.toString
          IO.eprintln s!"dump_elab: elaboration failed for {id}: {msg}"
    for (id, src) in errQueries do
      match Lean.Parser.runParserCategory env `term src with
      | .error msg => IO.eprintln s!"dump_elab: parse error for {id}: {msg}"
      | .ok stx =>
        Core.resetMessageLog
        let thrown ← try
            discard <| (do
              let e ← Lean.Elab.Term.elabTerm stx none
              Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
              instantiateMVars e).run'
            pure none
          catch ex => pure (some (← ex.toMessageData.toString))
        let logged ← (← Core.getMessageLog).toList.mapM (·.data.toString)
        let first := fun (m : String) => (m.splitOn "\n").headD ""
        match logged.head?, thrown with
        | some m, _    => emitErr id src (first m)
        | none, some m => emitErr id src (first m)
        | none, none   => IO.eprintln s!"dump_elab: {id} was expected to fail but elaborated"
        Core.resetMessageLog
  discard <| go.toIO coreCtx coreState
