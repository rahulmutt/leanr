-- Fixture for the tabled typeclass-synthesis DRIVER's termination test
-- (M4a plan 4, task B5): a CYCLIC instance graph.
--
-- `instAofB` derives `A a` from `B a`, and `instBofA` derives `B a`
-- from `A a` — so a goal `A N` reaches `B N` reaches `A N` again, with
-- no base case anywhere. A naive (memoized-backtracking) resolver
-- diverges on it; a TABLED resolver terminates, because the second
-- occurrence of `A N` resolves against the table entry the first
-- occurrence already created (it registers a waiter instead of
-- spawning a second generator). `synth.rs::cyclic_instances_terminate`
-- asserts the driver returns `Ok(None)` WITHOUT a step-budget error —
-- a budget error would mask a real loop rather than prove tabling
-- works.
--
-- `prelude`-mode, import-free (the Prelude0/Matcher/Instances pattern),
-- for hermeticity: CI never installs Lean, so the committed `.olean`
-- is the only input `with_cyclic_instances_ctx` replays from.
--
-- Scaffold below is copied verbatim from `tests/fixtures/Instances.lean`
-- (its own doc comment carries the full provenance/line-number
-- citations against the v4.33.0-rc1 oracle's `Init/Prelude.lean`; not
-- re-derived here).
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
-- Two classes, each derivable ONLY from the other: a 2-cycle with no
-- base instance. `A N` is therefore genuinely unsolvable — the point of
-- the fixture is that deciding so TERMINATES.
class A (a : Type u) where mkA : a → a
class B (a : Type u) where mkB : a → a

instance instAofB {a : Type u} [B a] : A a where mkA := fun x => x
instance instBofA {a : Type u} [A a] : B a where mkB := fun x => x
