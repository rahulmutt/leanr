-- Fixture for the `Lean.Meta.Match.Extension.extension` decode (M4a
-- plan 2, task 1). Each `match` below makes the elaborator register
-- one MatcherInfo entry in this module's extension array; `plainId`
-- uses no match and must contribute none.
--
-- `prelude`-mode, import-free (the Prelude0 pattern), for hermeticity:
-- later tasks replay this fixture from an empty environment (like
-- Prelude0), and the plan's tier-1 corpus asserts `imports.is_empty()`.
--
-- An earlier version of this fixture used a plain `import Init`
-- instead, on the (wrong) claim that `prelude` mode categorically
-- cannot support `match`: `Lean.Elab.Match`'s pattern-compiler
-- frontend unconditionally needs `Lean.PProd` (`packMatchTypePatterns`,
-- Match.lean ~line 590/743, fires for any match, even a single
-- wildcard alt), and `PProd` is a `Sort`-universe-polymorphic
-- structure, and declaring ANY `Sort`-polymorphic structure/inductive
-- under bare `prelude` fails with "unknown constant `lcAny`". That
-- last step was the error: `lcAny`/`lcErased`/`lcVoid` are not
-- built-in primitives outside `prelude`'s reach — they are ordinary
-- `unsafe axiom`s that Init/Prelude.lean itself declares (verified
-- against v4.33.0-rc1, `$(lean --print-prefix)/src/lean/Init/Prelude.lean`,
-- which is itself a `prelude`-mode file). A fixture can declare the
-- same minimal scaffold. The scaffold below is the minimum the match
-- elaborator needs: `PProd` for pattern-type packing, `Unit`/`PUnit`
-- for the artificial unit-thunk parameter alternatives with no real
-- fields get, and `Eq`/`HEq` (plus `rfl`/`cast`/`id`/`eq_of_heq`/
-- `heq_of_eq`) for the dependent-elimination machinery the `cases`-like
-- compilation of `match` relies on (`noConfusion`-style reasoning).
-- `Prod` is included so `inductive N`'s structural-recursion aux
-- construction (`.below`/`.brecOn`) gets generated at all — its gate is
-- `hasUnit && hasProd` (`Elab/MutualInductive.lean:1555`) — which a
-- later task (7) needs for a structurally recursive `count` appended
-- to this same file.
--
-- Each scaffold declaration below is copied from (or, where noted,
-- minimally adapted from) the oracle's own `prelude`-mode
-- `Init/Prelude.lean`, citing v4.33.0-rc1 line numbers: `lcErased` :27,
-- `lcAny` :30, `lcVoid` :33, `PUnit` :42-44, `Unit` :233, `Unit.unit`
-- :240, `Eq` :73-76, `rfl` :351-352 (kept as `def` + `set_option
-- linter.defProp false in`, exactly as the oracle does — a `theorem
-- rfl` does NOT compile here: `@[match_pattern] theorem rfl` fails
-- with "`rfl` is not an exposed definition", since the oracle's whole
-- file is wrapped in `@[expose] section`, Prelude.lean:11, which this
-- fixture does not replicate), `Eq.ndrec` :80-81, `cast` :411-412
-- (attributes trimmed — `macro_inline`/`implicit_reducible` are
-- compiler/reducibility hints irrelevant to a decode-only fixture),
-- `HEq` :95-97, `id` :131 (attributes trimmed, same reasoning as
-- `cast`), `eq_of_heq` :546-550 (exact copy), `heq_of_eq` :553-554
-- (body adapted: `h.rec (HEq.refl a)` instead of the oracle's `Eq.subst
-- h (HEq.refl a)`, since `Eq.subst` is not part of this minimal
-- scaffold and is itself defined in terms of `.rec`), `Prod` :563-571
-- (field docs/the `mk ::` constructor-naming line dropped — cosmetic),
-- `PProd` :581-585.
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

inductive N where
  | zero : N
  | succ : N → N

-- One matcher, one discriminant, two alternatives.
def isZero (n : N) : N :=
  match n with
  | .zero => .succ .zero
  | .succ _ => .zero

-- Two discriminants (a distinct matcher shape: numDiscrs = 2).
def both (a b : N) : N :=
  match a, b with
  | .zero, .zero => .zero
  | _, _ => .succ .zero

def plainId (n : N) : N := n
