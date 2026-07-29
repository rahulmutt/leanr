-- M4b-1 tier-1 elaboration corpus (design spec § The differential
-- oracle harness). prelude-mode and import-free (the Prelude0/Meta0/
-- Synth0 pattern) so BOTH sides of the differential gate see exactly
-- this module and nothing else: the oracle imports only Elab0, leanr
-- replays only Elab0.olean. Grow deliberately, like Meta0.lean, as
-- later tasks' corpora reference more constants.
--
-- Same scaffold prefix as Meta0.lean (verbatim through `Prod`) — see
-- that file's own doc comment for the exact oracle citations
-- (`Init/Prelude.lean`, v4.33.0-rc1) each scaffold declaration is
-- copied from. Not every scaffold declaration is exercised by THIS
-- task's `str`-only corpus, but keeping the same base as Meta0 means
-- Tasks 5-6 (identifiers, sorts, ascription, hole) can grow this file
-- without re-deriving the scaffold from scratch.
prelude

unsafe axiom lcErased : Type
unsafe axiom lcAny : Type
unsafe axiom lcVoid : Type

set_option bootstrap.inductiveCheckResultingUniverse false in
inductive PUnit : Sort u where
  | unit : PUnit

abbrev Unit : Type := PUnit
@[match_pattern] abbrev Unit.unit : Unit := PUnit.unit

inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a

set_option linter.defProp false in
@[match_pattern] def rfl {α : Sort u} {a : α} : Eq a a := Eq.refl a

@[simp] abbrev Eq.ndrec.{u1, u2} {α : Sort u2} {a : α} {motive : α → Sort u1} (m : motive a) {b : α} (h : Eq a b) : motive b :=
  h.rec m

inductive HEq : {α : Sort u} → α → {β : Sort u} → β → Prop where
  | refl (a : α) : HEq a a

@[inline] def id {α : Sort u} (a : α) : α := a

def cast {α β : Sort u} (h : Eq α β) (a : α) : β :=
  h.rec a

theorem eq_of_heq {α : Sort u} {a a' : α} (h : HEq a a') : Eq a a' :=
  have : (α β : Sort u) → (a : α) → (b : β) → HEq a b → (h : Eq α β) → Eq (cast h a) b :=
    fun _ _ _ _ h₁ =>
      h₁.rec (fun _ => rfl)
  this α α a a' h rfl

theorem heq_of_eq {α : Sort u} {a a' : α} (h : Eq a a') : HEq a a' :=
  h.rec (HEq.refl a)

structure PProd (α : Sort u) (β : Sort v) where
  fst : α
  snd : β

structure Prod (α : Type u) (β : Type v) where
  fst : α
  snd : β

-- === Elab0-specific corpus below (M4b-1 Task 4) ===

-- `String`: needed by later slices (Tasks 5-6) that ascribe or name
-- it as a type. NOT consulted by the `str` slice itself: a string
-- literal elaborates straight to `Expr.lit (.strVal _)` and never
-- touches the `String` name at all — `Expr.lit`'s inferred type is
-- `String` only via a SEPARATE `inferType` call, and the M4b-1-
-- slice-1 harness (`dump_elab.lean`, `elab_term_ensuring_type`
-- called with `expected := none`) never makes that call: `elabTerm` +
-- `instantiateMVars` only, no `ensureHasType`, per the design spec's
-- "Universe defaulting divergence" risk note. A minimal opaque
-- stand-in suffices here — this fixture is prelude-mode with no
-- List/Char/UInt32 scaffold, so the real
-- `structure String where data : List Char` definition is out of
-- reach; grow to the real definition in whichever later task first
-- needs String's actual shape.
axiom String : Type

-- === Task 5 corpus: identifier leaf elaborator (`ident`) ===
--
-- `Nat` (zero universe params) and `List` (exactly one universe param,
-- `u`) exercise `elab_ident`'s two shapes: `const Nat []` (no fresh
-- level mvars minted) and `const List [?u]` (one fresh level mvar per
-- `levelParams`, canonicalizing to `lmvar` index 0) — the first task to
-- exercise `lmvar` end-to-end. Minimal but real inductives (Nat's own
-- constructors are never consulted by the `ident` slice — no
-- `inferType`/defeq call touches them, same "opaque stand-in is fine"
-- reasoning as `axiom String` above — but a real `inductive` is used
-- anyway per this task's own scope, rather than another axiom, so a
-- later slice needing Nat's actual constructors/recursor has less to
-- redo).
-- `genCtorIdx false`: Lean's `inductive` elaborator auto-generates
-- `T.ctorIdx`/`T.ctor.elim` for every multi-constructor inductive
-- IFF the environment already `.contains \`Nat` (`Lean/Elab/
-- MutualInductive.lean`'s `mkAuxConstructions`, `hasNat := env.contains
-- \`\`Nat`) — a purely name-based check, not a semantic one. The moment
-- THIS declaration brings a constant literally named `Nat` into scope
-- (itself, and after it, `List`), that generator activates and tries
-- to build a `Nat`-valued lookup table (`Lean.mkNatLookupTable`) using
-- the REAL `cond`/`Nat.ble`/`Nat.decEq` primitives — none of which
-- exist in this minimal prelude-mode fixture (confirmed empirically:
-- omitting this option fails with `unknown constant 'cond'`/
-- `'Nat.decEq'`). `set_option genCtorIdx false` (checked directly by
-- `mkCtorIdx`'s own guard) suppresses `T.ctorIdx`, which in turn makes
-- `mkCtorElim`'s own "does `T.ctorIdx` exist" precondition false, so
-- neither ever runs. Harmless here: the `ident` slice never calls
-- either.
set_option genCtorIdx false in
inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

universe u

-- `List`, universe-polymorphic in exactly one parameter `u` — the
-- minimal shape that produces a single fresh `lmvar` per `ident/List`
-- query. `genCtorIdx false`: same reasoning as `Nat` above (this
-- declaration is itself now past the `hasNat` tripwire).
set_option genCtorIdx false in
inductive List (α : Type u) where
  | nil : List α
  | cons : α → List α → List α

-- === M4b-3 P1 task 7 corpus: named arguments and eta-expansion ===
--
-- `pick` is the minimal shape that makes eta-expansion observable: TWO
-- explicit parameters, so `pick (y := Nat.zero)` leaves `x` missing and
-- the oracle emits `fun x => pick x Nat.zero` (App.lean:206's own
-- worked example) rather than an application. `dep` makes a named
-- argument's DEPENDENCY on an earlier parameter reachable
-- (`findNamedArgDependsOnCurrent?`, App.lean:340), which turns the
-- missing parameter implicit instead of eta.
def pick (x : Nat) (y : Nat) : Nat := x
def dep (a : Type) (z : a) : a := z

-- `dpick` exists for ONE record, `app/namedDepPropagate2`, and only that
-- shape makes `getResultingTypeCore?`'s `findNamedArgDependsOn?` ESCAPE
-- (App.lean:477-479) observable. Every part of the signature is
-- load-bearing:
--   * `{a : Type}` is the RESULT type, so propagating the expected type
--     assigns it — a resulting type with no metavariable makes the
--     escape emit the same term either way;
--   * `(w : a)` is an explicit argument elaborated BEFORE the escape's
--     parameter, and `PUnit.unit`'s own type is what assigns `a` when
--     propagation is postponed instead;
--   * `(x : Type) (z : x)` is the dependency itself — `z`'s type
--     mentions `x`, so `findNamedArgDependsOn?` returns `some` for the
--     missing `x` and the walk continues to the result type instead of
--     postponing.
-- The discrimination is the same `Unit`-is-a-reducible-abbrev-of-PUnit
-- mechanism `app/propagateAbbrev` documents: escaping assigns
-- `?a := Unit` first, postponing lets `PUnit.unit` assign
-- `?a := PUnit.{1}`. Measured, not assumed — see the task-7 fix report.
def dpick {a : Type} (w : a) (x : Type) (z : x) : a := w

-- === M4b-3 P2a corpus: classes, instances, instance-implicit args ===
--
-- Modelled on tests/fixtures/meta/Synth0.lean:86-136 (leanr_meta's own
-- synthesis corpus) but deliberately NOT a copy: only the shapes P2a's
-- records discriminate.
--
--   * `Wrap` — one parameter, one concrete instance. The minimal shape
--     that makes `processInstImplicitArg` observable.
--   * `Pair` — TWO parameters, so an instance goal with more than one
--     argument exercises `getArgExpectedType` past the first.
--   * `NoInst` — a class with NO instance, so `synthesizeInstMVarCore`'s
--     `.none` (real failure) arm is reachable and distinguishable from
--     its `.undef` (stuck) arm, which `useWrap` with no expected type
--     reaches instead. Both are error paths, so neither appears in the
--     JSONL: the dumper drops a throwing query. They are asserted in
--     crates/leanr_elab/tests/synthetic_smoke.rs.
--   * `Dflt` — DISTINCT from `Wrap`/`Pair`/`NoInst`, carrying a
--     `@[default_instance]`, so rung 3 (`synthesize_using_default`) has
--     a positive test. It named `synthesize_using_default_errors_when_a_
--     default_instance_is_registered` while rung 3 was P2a's shape
--     GUARD; M4b-3 P3 task 5 replaced that guard with the real body and
--     deleted the test. The successors are
--     `synthesize_using_default_applies_a_default_instance` and
--     `a_rejected_default_instance_is_rolled_back`, both in
--     crates/leanr_elab/tests/synthetic_smoke.rs. `Wrap`/`Pair`/`NoInst`
--     must NEVER gain a default instance: one on `Wrap` would make rung
--     3 fire for the stuck `useWrap` goal and break the stuck-path tests
--     (P2a tasks 5 and 9).
class Wrap (a : Type) where
  wrap : a -> a

instance instWrapNat : Wrap Nat where
  wrap := fun n => n

-- M4b-3 P3 task 2: a SECOND candidate instance per class. With exactly
-- one candidate, `tc/useWrapAscribed` and `tc/pairBoth` could reach the
-- oracle's answer by a different route than the oracle takes — leanr
-- resolving eagerly from the sole candidate where the oracle keeps the
-- goal stuck and lets the argument fix the type parameter. A second
-- candidate separates "right answer" from "right reason".
--
-- `Unit` (not `String`): `String` is an `axiom` here with no
-- constructor, so `Dflt String` has no inhabitant to give `val`.
-- `Unit`/`Unit.unit` are real and already in the scaffold.
--
-- `NoInst` deliberately keeps ZERO instances — `synthetic_smoke.rs`'s
-- `unsolvable_instance_is_a_synthesis_failure` asserts its `.none` arm.
-- None of the three gains a `@[default_instance]`: line 158-163 above
-- records why that would break the stuck-path tests.
instance instWrapUnit : Wrap Unit where
  wrap := fun u => u

class Pair (a : Type) (b : Type) where
  mk2 : a -> b -> a

instance instPairNatNat : Pair Nat Nat where
  mk2 := fun x _ => x

instance instPairNatUnit : Pair Nat Unit where
  mk2 := fun x _ => x

class NoInst (a : Type) where
  nope : a

class Dflt (a : Type) where
  val : a

@[default_instance]
instance instDfltNat : Dflt Nat where
  val := Nat.zero

instance instDfltUnit : Dflt Unit where
  val := Unit.unit

def useWrap {a : Type} [Wrap a] (x : a) : a := Wrap.wrap x
def usePair {a : Type} {b : Type} [Pair a b] (x : a) (y : b) : a := Pair.mk2 x y
def useNoInst {a : Type} [NoInst a] (x : a) : a := x

-- === M4b-3 P3 corpus: literals and default instances ===
--
-- Copied VERBATIM from `Init` where the shape is what the emitted
-- `Expr` references (`Bool`, `OfNat`, `instOfNatNat`, `OfScientific`);
-- opaque carriers where it is not (`Char`). See the design spec's § P3
-- for the reasoning behind each choice.

-- `Bool` is needed for `scientific`: `elabScientificLit` emits the
-- exponent SIGN as `toExpr sign` (`BuiltinTerm.lean:243`), a `Bool`
-- literal. Verbatim from `Init/Prelude.lean`.
-- `genCtorIdx false`: same tripwire as `Nat`/`List` above
-- (`Elab0.lean:93-108`) — `Bool` is a multi-constructor inductive and
-- `Nat` is already in scope, so `mkAuxConstructions`'s purely
-- name-based `hasNat` check fires and tries to build a
-- `Nat`-valued lookup table using primitives this prelude-mode
-- fixture does not have. Confirmed empirically: omitting this option
-- fails with `unknown constant 'cond'`.
set_option genCtorIdx false in
inductive Bool : Type where
  | false : Bool
  | true : Bool

-- Verbatim from `Init/Prelude.lean:1270-1279`, including the
-- `@[default_instance 100]` priority. That priority is load-bearing:
-- `instDfltNat` above carries a bare `@[default_instance]` (priority
-- 1000) and `instOfNatTag` below carries 50, so the environment has
-- THREE distinct default-instance priorities (1000 / 100 / 50) and
-- `synthesizeUsingDefault`'s descending-priority walk is
-- differentially observable rather than vacuous (design spec § P3).
--
-- `instOfNatNat` must OUTRANK `instOfNatTag`, and that is the whole
-- point of the 100-vs-50 gap: a bare numeral with no expected type
-- reaches its carrier only through the default-instance rung, and the
-- answer it must reach is `Nat` — exactly as in real Lean, where
-- `instOfNatNat` is the `OfNat` default. `tests/fixtures/elab/
-- dump_elab.lean`'s `num/bare` record is the committed evidence.
-- (M4b-3 P3 task 6 review: `instOfNatTag` originally sat at 500 and
-- therefore WON the walk, so bare `42` defaulted to the fixture-only
-- carrier `Tag` and `num/ascribedTag` was a byte-for-byte duplicate of
-- `num/bare`. Re-prioritised to 50, which keeps three distinct
-- priorities — the reason there were ever three — while making the
-- bare-numeral record demonstrate the behaviour the slice is about.)
class OfNat (α : Type u) (_ : Nat) where
  ofNat : α

@[default_instance 100]
instance instOfNatNat (n : Nat) : OfNat Nat n where
  ofNat := n

-- `Tag`: a fixture-local SECOND numeric type, standing in for the
-- design spec's original `(42 : Int)` corpus example. `Int` needs
-- `Init.Data.Int`, unreachable in prelude mode; what the record
-- actually tests is "a numeral against a non-default expected type",
-- which any second `OfNat` carrier provides. Its instance sits at a
-- THIRD priority so the priority walk has more than two rungs to order
-- — and BELOW `instOfNatNat`'s 100, so `Tag` is reachable only by
-- ASCRIPTION (`(42 : Tag)`) and never by defaulting. A `Tag` that won
-- the walk would make the bare-numeral record test a fixture artefact
-- instead of the real `Nat`-defaulting behaviour; see `instOfNatNat`'s
-- comment above.
structure Tag where
  raw : Nat

@[default_instance 50]
instance instOfNatTag (n : Nat) : OfNat Tag n where
  ofNat := Tag.mk n

-- Verbatim from `Init/Data/OfScientific/Basic.lean:20-30`.
class OfScientific (α : Type u) where
  ofScientific : Nat -> Bool -> Nat -> α

instance instOfScientificTag : OfScientific Tag where
  ofScientific := fun m _ _ => Tag.mk m

-- OPAQUE CARRIERS, deliberately (design spec § P3; plan § Measured
-- facts, item 8). `elabCharLit` emits `Char.ofNat (rawNatLit c)`
-- without ever reading `Char`'s shape, using no expected type and
-- performing no typecheck, so the emitted `Expr` is byte-identical to
-- what the real definition would produce. The real `Char` is a
-- structure over `UInt32` with a validity proof and the real
-- `Char.ofNat` is `dite` over `BitVec.ofNatLT` — `Fin`, `BitVec`,
-- `UInt32`, `Nat.lt`, `decide` and `Or` would all have to come with
-- them. Same "minimal opaque stand-in suffices" reasoning as
-- `axiom String` above; grow to the real definitions in whichever
-- later slice first needs `Char`'s actual shape.
axiom Char : Type
axiom Char.ofNat : Nat -> Char
