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

-- CYCLIC instance graph (design spec § tier-1 corpus shapes lists this
-- alongside diamond/negative/stuck; B7's curated list had omitted it —
-- see the B7 review report). `CycA`/`CycB` are derivable ONLY from each
-- other (`CycA a` from `CycB a`, `CycB a` from `CycA a`), with NO base
-- instance anywhere in the 2-cycle, so `CycA N` is genuinely
-- unsolvable — same shape as B5's `InstancesCyclic.lean`
-- (`synth.rs::cyclic_instances_terminate`), but exercised here
-- DIFFERENTIALLY against the oracle rather than only as a leanr-side
-- termination unit test. The point of the query is that deciding
-- "no instance" TERMINATES rather than loops; `cyclic/synth/0`'s
-- `near_budget` flag would catch it if it came anywhere near the
-- oracle's own heartbeat budget.
class CycA (a : Type u) where mkA : a → a
class CycB (a : Type u) where mkB : a → a
instance instCycAofB {a : Type u} [CycB a] : CycA a where mkA := fun x => x
instance instCycBofA {a : Type u} [CycA a] : CycB a where mkB := fun x => x

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

-- `Dual` — SEMIREDUCIBLE by construction (a plain `def`, no
-- `@[reducible]`). It exists for one query, `outParamNoMVars/synth/0`
-- (`Op N N (Dual N)`), and it is what makes that query discriminating
-- rather than merely covering. Type class resolution runs at
-- `TransparencyMode.instances`, which cannot unfold `Dual`, so a search
-- against the goal as written fails; the oracle instead replaces the
-- output parameter with a fresh mvar (`preprocessOutParam`, called even
-- on the `.noMVars` path — the call at `SynthInstance.lean:1000`, under
-- the `OrderDual` note at `:981-999`), finds `instOpN`, and then
-- reconciles with `assignOutParams`' `isDefEq` under `withDefault`
-- (`SynthInstance.lean:842` — corrected from `:851`, which falls inside
-- `checkMayHaveSideEffects`' doc comment; `:842` is the
-- `let defEq ← withDefault <| withAssignableSyntheticOpaque <|
-- isDefEq type resultType` line itself), where `Dual` DOES unfold.
-- Skip either half and the answer flips from `some instOpN` to `none`.
def Dual (a : Type) : Type := a

-- === M4b-3 P4: the coercion class chain (design spec § P4, § Amendment 5 item 9) ===
--
-- `semiOutParam` at the ROOT namespace, verbatim from
-- `Init/Prelude.lean:725`, for the same reason `outParam` above is:
-- `Coe`'s first parameter is `semiOutParam (Sort u)`, and only the root
-- name is the real gadget. For synthesis it is inert apart from being
-- reducible (it is consulted only by `computeSynthOrder`, whose result
-- is already serialized into `InstanceEntry.synthOrder` and read by
-- `leanr_meta::instances`).
@[reducible] def semiOutParam (α : Sort u) : Sort u := α

-- The chain, VERBATIM from `Init/Coe.lean:131-287` of the pin with the
-- doc comments dropped and nothing else changed: twelve classes,
-- seventeen instances (anonymous, so Lean auto-names them exactly as
-- it does in Init), twelve `attribute [coe_decl]` lines. A stand-in
-- chain was rejected (§ Amendment 5 item 9): the diamond of reflexive
-- (`CoeTC α α`) and transitive (`[Coe β γ] [CoeTC α β] : CoeTC α γ`)
-- instances is exactly what the Mathlib synthesis nightly hits, and the
-- resolver's path through it is observable ONLY at this tier — the
-- elaborator tier unfolds the instance away (`expandCoe`).
class Coe (α : semiOutParam (Sort u)) (β : Sort v) where
  coe : α → β
attribute [coe_decl] Coe.coe

class CoeTC (α : Sort u) (β : Sort v) where
  coe : α → β
attribute [coe_decl] CoeTC.coe
instance [Coe β γ] [CoeTC α β] : CoeTC α γ where coe a := Coe.coe (CoeTC.coe a : β)
instance [Coe α β] : CoeTC α β where coe a := Coe.coe a
instance : CoeTC α α where coe a := a

class CoeOut (α : Sort u) (β : semiOutParam (Sort v)) where
  coe : α → β
attribute [coe_decl] CoeOut.coe

class CoeOTC (α : Sort u) (β : Sort v) where
  coe : α → β
attribute [coe_decl] CoeOTC.coe
instance [CoeOut α β] [CoeOTC β γ] : CoeOTC α γ where coe a := CoeOTC.coe (CoeOut.coe a : β)
instance [CoeTC α β] : CoeOTC α β where coe a := CoeTC.coe a
instance : CoeOTC α α where coe a := a

class CoeHead (α : Sort u) (β : semiOutParam (Sort v)) where
  coe : α → β
attribute [coe_decl] CoeHead.coe

class CoeHTC (α : Sort u) (β : Sort v) where
  coe : α → β
attribute [coe_decl] CoeHTC.coe
instance [CoeHead α β] [CoeOTC β γ] : CoeHTC α γ where coe a := CoeOTC.coe (CoeHead.coe a : β)
instance [CoeOTC α β] : CoeHTC α β where coe a := CoeOTC.coe a
instance : CoeHTC α α where coe a := a

class CoeTail (α : semiOutParam (Sort u)) (β : Sort v) where
  coe : α → β
attribute [coe_decl] CoeTail.coe

class CoeHTCT (α : Sort u) (β : Sort v) where
  coe : α → β
attribute [coe_decl] CoeHTCT.coe
instance [CoeTail β γ] [CoeHTC α β] : CoeHTCT α γ where coe a := CoeTail.coe (CoeHTC.coe a : β)
instance [CoeHTC α β] : CoeHTCT α β where coe a := CoeHTC.coe a
instance : CoeHTCT α α where coe a := a

class CoeDep (α : Sort u) (_ : α) (β : Sort v) where
  coe : β
attribute [coe_decl] CoeDep.coe

class CoeT (α : Sort u) (_ : α) (β : Sort v) where
  coe : β
attribute [coe_decl] CoeT.coe
instance [CoeHTCT α β] : CoeT α a β where coe := CoeHTCT.coe a
instance [CoeDep α a β] : CoeT α a β where coe := CoeDep.coe a
instance : CoeT α a α where coe := a

class CoeFun (α : Sort u) (γ : outParam (α → Sort v)) where
  coe : (f : α) → γ f
attribute [coe_decl] CoeFun.coe
instance [CoeFun α fun _ => β] : CoeOut α β where coe a := CoeFun.coe a

class CoeSort (α : Sort u) (β : outParam (Sort v)) where
  coe : α → β
attribute [coe_decl] CoeSort.coe
instance [CoeSort α β] : CoeOut α β where coe a := CoeSort.coe a

-- A two-step chain `N → M → Big` through two plain `Coe` instances.
-- `CoeT N n Big` is solvable ONLY through `CoeTC`'s transitive
-- instance (`[Coe β γ] [CoeTC α β] : CoeTC α γ`, with `β := M` found
-- by the search), so its recorded instance term is the discriminator
-- for the resolver's candidate order through the diamond (§ Amendment 5
-- item 10). `M` and `Big` are new opaque carriers; the requirement is
-- the chain, not the names.
inductive M where
  | ofN : N → M

inductive Big where
  | ofM : M → Big

instance instCoeNM : Coe N M := ⟨M.ofN⟩
instance instCoeMBig : Coe M Big := ⟨Big.ofM⟩

-- `CoeFun` / `CoeSort` carriers, for the two outParam-bearing classes:
-- the goal's last argument is an mvar the search ASSIGNS (P2b-i's
-- `assignOutParams`), observable in the record's `assigns`.
structure FnN where
  f : N → N

instance instCoeFunFnN : CoeFun FnN (fun _ => N → N) := ⟨FnN.f⟩

structure SortN where
  ty : Type

instance instCoeSortSortN : CoeSort SortN Type := ⟨SortN.ty⟩
