-- Fixture for the typeclass-synthesis extension decodes (M4a plan 4,
-- task A1): `instanceExtension`, `defaultInstanceExtension`, and
-- `projectionFnInfoExt`. Exercises: a class with a superclass
-- (projection + diamond potential via `Semigroup`/`Monoid` both
-- reaching `Mul` through different paths), plain concrete instances,
-- a parametrized instance (subgoal chaining through `Add (Prod a b)`),
-- and a `@[default_instance]`.
--
-- `prelude`-mode, import-free (the Prelude0/Matcher pattern), for
-- hermeticity: CI never installs Lean, so the committed `.olean` is
-- the only input later A-tasks and PR-B replay from.
--
-- Scaffold below is copied verbatim from `tests/fixtures/Matcher.lean`
-- (lines 21-66 there: `lcErased`/`lcAny`/`lcVoid`, `PUnit`/`Unit`,
-- `Eq`/`Eq.ndrec`/`rfl`, `HEq`, `id`, `cast`, `eq_of_heq`/`heq_of_eq`,
-- `PProd`, `Prod`) plus its `inductive N`. See that file's own doc
-- comment for the full provenance/line-number citations against the
-- v4.33.0-rc1 oracle's `Init/Prelude.lean`; not re-derived here.
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

-- classes with a superclass relationship (exercises projections + diamonds)
class Add (a : Type u) where add : a → a → a
class Mul (a : Type u) where mul : a → a → a
class Semigroup (a : Type u) extends Mul a where       -- projection: Semigroup.toMul
class Monoid (a : Type u) extends Semigroup a where one : a

-- concrete instances (simple resolution)
instance instAddN : Add N where add := fun _ b => b
instance instMulN : Mul N where mul := fun _ b => b
instance instSemigroupN : Semigroup N where            -- diamond source via toMul
instance instMonoidN : Monoid N where one := N.zero

-- parametrized instance (subgoal chaining: Add (Prod a b) needs Add a, Add b)
instance instAddProd {a b : Type u} [Add a] [Add b] : Add (Prod a b) where
  add := fun p q => Prod.mk (Add.add p.fst q.fst) (Add.add p.snd q.snd)

-- a default instance
class OfN (n : N) (a : Type u) where ofN : a
@[default_instance] instance instOfNN (n : N) : OfN n N where ofN := n

-- === M4b-3 P2b-i: outParam classes (design spec § P2b-i) ===
--
-- The FIRST classes in any leanr fixture carrying an `outParam`. Until
-- this block, `getOutParamPositions?` was empty everywhere and the
-- oracle's `preprocessOutParam`/`assignOutParams` were unreachable, so
-- leanr's not having them was invisible (design spec § Amendment 3,
-- item 2).
--
-- `outParam` must be declared here, at the ROOT namespace, because these
-- fixtures are `prelude`-mode and import no `Init`. The oracle's `class`
-- command decides output-parameter positions with
-- `Lean.Expr.isOutParam` (`Expr.lean:1708-1710`), which is
-- `isAppOfArity ``outParam 1` against the ROOT name `outParam` — so this
-- declaration is the real thing, not a look-alike. Copied verbatim from
-- `Init/Prelude.lean:702` of the pin.
@[reducible] def outParam (α : Sort u) : Sort u := α

-- `Op` — the binop shape. Two ordinary parameters and one `outParam`,
-- i.e. `ClassEntry.outParams == #[2]` and `outLevelParams == #[]` (all
-- three parameters share the universe `u`). This is the shape
-- `crates/leanr_elab/src/synthetic/ladder.rs:105-115` cites as a live
-- divergence — the oracle answers `Op N N ?γ` with `?γ := N` assigned,
-- leanr (before this plan) answers `Undef`.
class Op (a : Type u) (b : Type u) (c : outParam (Type u)) where
  op : a → b → c

instance instOpN : Op N N N where
  op := fun _ b => b

-- `Lvl` — a universe that appears ONLY in an output parameter, i.e.
-- `outParams == #[1]` AND `outLevelParams == #[1]` (the universe `v`
-- occurs only in `b`'s type). It is what gives `ClassEntry`'s third
-- field a non-empty producer, and it is the class
-- `preprocessOutParam`'s `preprocessLevels` branch
-- (`SynthInstance.lean:786-795`) runs on.
class Lvl (a : Type u) (b : outParam (Type v)) where
  lvl : a → b

instance instLvlN : Lvl N N where
  lvl := fun a => a

-- `Get` — the `GetElem` shape from the oracle's own worked example
-- (`App.lean:143-146`): two ordinary parameters, one `outParam`, and a
-- method taking both ordinary parameters. M4b-3 P2b-ii needs exactly
-- this shape in `Elab0.lean`; proving it out at the synthesis tier first
-- is why it is here.
class Get (cont : Type u) (idx : Type v) (elem : outParam (Type w)) where
  get : cont → idx → elem

instance instGetN : Get N N N where
  get := fun c _ => c
