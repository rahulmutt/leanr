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
