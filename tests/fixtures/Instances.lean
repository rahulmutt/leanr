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
-- `crates/leanr_elab/src/synthetic/ladder.rs`' "Residue 1" cites as a
-- live divergence — the oracle answers `Op N N ?γ` with `?γ := N` assigned,
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
-- (`SynthInstance.lean:785-794` — corrected from `:786-795`, which
-- starts one line late and ends one line into `preprocessArgs`' own
-- declaration) runs on.
class Lvl (a : Type u) (b : outParam (Type v)) where
  lvl : a → b

instance instLvlN : Lvl N N where
  lvl := fun a => a

-- `Get` — the `GetElem` shape from the oracle's own worked example
-- (the class is declared at `App.lean:150-151`, inside the
-- `resultIsOutParamSupport` doc comment spanning `:141-167` — NOT at
-- `:143-146`, which is that comment's opening prose): two ordinary
-- parameters, one `outParam`, and a method taking both ordinary
-- parameters. M4b-3 P2b-ii needs exactly this shape in `Elab0.lean`;
-- proving it out at the synthesis tier first is why it is here.
class Get (cont : Type u) (idx : Type v) (elem : outParam (Type w)) where
  get : cont → idx → elem

instance instGetN : Get N N N where
  get := fun c _ => c

-- `Dep` — the only class here with a DEPENDENT telescope: `c`'s TYPE
-- mentions `b`, and `b` is itself an output parameter. Every other
-- out-param class above (`Op`/`Lvl`/`Get`) has every parameter typed by
-- a bare `Type _`, so `preprocessOutParam`'s `preprocessArgs` loop
-- (`SynthInstance.lean:795-811`) could instantiate the class telescope
-- with the CALLER's original argument instead of the freshly minted
-- replacement and no test or corpus record would notice. Here it would:
-- the mvar minted for `c` is typed `outParam (?b → a)` only if the loop
-- instantiated with the fresh `?b`; instantiating with the caller's
-- `args[1]` types it `outParam (N → N)` instead. Pinned by
-- `synth.rs::preprocess_out_param_instantiates_with_the_replacement`.
--
-- `c` must ITSELF be an `outParam`: the oracle's `class` command rejects
-- `(c : b → a)` outright with "invalid class, parameter #3 depends on
-- `outParam`, but it is not an `outParam`", so `outParams == #[1, 2]` is
-- the only shape this dependency can take. No instance is declared and
-- no query in `Synth0.lean`/`dump_synth.lean` mentions `Dep` — the unit
-- test replays `Instances.olean` directly, so the synthesis corpus and
-- its record count stay untouched.
class Dep (a : Type) (b : outParam Type) (c : outParam (b → a)) where
  dep : a

-- === M4b-3 P4: the monad-lift shape guard's positive environment ===
--
-- `coerce`'s guard (design spec § Amendment 5 item 6) fires only when
-- BOTH types reduce to type applications AND the environment contains
-- `Monad` or `MonadLiftT` — the only shape on which the oracle's
-- `coerceMonadLift?` (`Meta/Coe.lean:201-257`) can return `some`. This
-- axiom is EXISTENCE-ONLY (nothing reads its type) so that
-- `coe.rs`'s unit test can drive the guard over this fixture, while the
-- two corpus fixtures (`Synth0`, `Elab0`) stay `Monad`-free and never
-- reach it. No corpus record is dumped from this file.
axiom Monad : (Type → Type) → Type
