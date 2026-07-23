-- M4a plan-4 tier-1 SYNTHESIS corpus (spec § The gate). Sibling of
-- `Meta0.lean`: `prelude`-mode and import-free (the Prelude0/Matcher
-- pattern) so BOTH sides of the differential gate see exactly this
-- module and nothing else — `dump_synth.lean` imports only `Synth0`,
-- and `crates/leanr_meta/tests/oracle_synth.rs` replays only
-- `Synth0.olean`. Grow deliberately, like the parse pass-list.
--
-- Why a SEPARATE module from `Meta0.lean` rather than extending it:
-- `Meta0.olean` and `meta-queries.jsonl` are frozen inputs of the
-- already-green `oracle_fast` gate (task B7's brief: do not modify
-- them), and adding classes/instances to `Meta0` would change every
-- committed `infer` record produced by `dump_defeq.lean`'s
-- constant-loop.
--
-- Contents = `tests/fixtures/Instances.lean` (PR-A's extension-decode
-- fixture) verbatim through `instOfNN`, plus the extra declarations
-- tasks B7's curated query list needs (a priority pair, an
-- instance-free class, a chain-failure case). Keeping the shared
-- prefix byte-identical means the two fixtures pin the same decoded
-- instance/default-instance/projection-fn shapes.
--
-- Scaffold below (`lcErased` .. `Prod`) is copied verbatim from
-- `tests/fixtures/Matcher.lean`; see that file's own doc comment for
-- the full provenance/line-number citations against the v4.33.0-rc1
-- oracle's `Init/Prelude.lean`. Not re-derived here.
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

-- classes with a superclass relationship. NOTE: the chain is LINEAR
-- (`Monoid → Semigroup → Mul`), not a multi-PARENT diamond. The
-- "diamond" this fixture exercises is the REDUNDANT-PATH sense: a goal
-- `Mul N` is reachable BOTH directly (`instMulN`) and through the
-- superclass projection instance `Semigroup.toMul` applied to
-- `instSemigroupN` (and again through `Monoid.toSemigroup`), so the
-- search has several distinct derivations of one goal and must pick
-- ONE deterministically. That choice is exactly what the committed
-- `val` term pins.
class Add (a : Type u) where add : a → a → a
class Mul (a : Type u) where mul : a → a → a
class Semigroup (a : Type u) extends Mul a where       -- projection: Semigroup.toMul
class Monoid (a : Type u) extends Semigroup a where one : a

-- concrete instances (simple resolution)
instance instAddN : Add N where add := fun _ b => b
instance instMulN : Mul N where mul := fun _ b => b
instance instSemigroupN : Semigroup N where            -- redundant path to `Mul N` via toMul
instance instMonoidN : Monoid N where one := N.zero

-- parametrized instance (subgoal chaining: Add (Prod a b) needs Add a, Add b)
instance instAddProd {a b : Type u} [Add a] [Add b] : Add (Prod a b) where
  add := fun p q => Prod.mk (Add.add p.fst q.fst) (Add.add p.snd q.snd)

-- a default instance
class OfN (n : N) (a : Type u) where ofN : a
@[default_instance] instance instOfNN (n : N) : OfN n N where ofN := n

-- === Synth0-specific additions (M4a plan 4 task B7) ===

-- PRIORITY ORDERING. Two instances of the SAME class at the SAME type,
-- distinguished only by `(priority := ...)`. `instPriLow` is declared
-- SECOND, so at equal priority the oracle's own ordering (later
-- declaration first within a priority bucket) would select it; the
-- explicit higher priority on `instPriHigh` must override that, so the
-- committed answer for `Pri N` is `instPriHigh` and NOT `instPriLow`.
-- Declaration order and priority order therefore disagree, which is
-- what makes this query discriminating rather than vacuous.
class Pri (a : Type u) where pri : a
instance (priority := 5000) instPriHigh : Pri N where pri := N.zero
instance (priority := 100) instPriLow : Pri N where pri := N.succ N.zero

-- NEGATIVE. A class with no instance at all: `NoInst N` must fail
-- outright (`ok:false`), not error.
class NoInst (a : Type u) where nope : a

-- NEGATIVE THROUGH A SUBGOAL. `Chain (Prod a b)` is derivable only
-- from `Chain a` and `Chain b`, and the ONLY base instance is at `N`.
-- So `Chain (Prod N N)` succeeds (two-level chaining) while
-- `Chain (Prod N (Prod N N))` needs `Chain (Prod N N)` — also fine —
-- and `Chain (Prod NoBase N)` fails only AFTER the parametrized
-- instance has been applied and its first subgoal has failed. That is
-- the "search fails deeper than the root" shape, distinct from
-- `NoInst N`'s "no candidate at all".
inductive NoBase where
  | mk : NoBase

class Chain (a : Type u) where ch : a
instance instChainN : Chain N where ch := N.zero
instance instChainProd {a b : Type u} [Chain a] [Chain b] : Chain (Prod a b) where
  ch := Prod.mk Chain.ch Chain.ch
