-- M4a plan-2 tier-1 corpus (spec § Acceptance harness). prelude-mode
-- and import-free (the Prelude0 pattern) so BOTH sides of the
-- differential gate see exactly this module and nothing else: the
-- oracle imports only Meta0; leanr replays only Meta0.olean. One
-- section per reduction rule; grow deliberately, like the parse
-- pass-list.
--
-- The bare fixture (starting directly at `inductive N`) does not
-- elaborate under `prelude`: `match` needs `Lean.PProd`/`Unit`/`Eq`/
-- `HEq` machinery (`Lean.Elab.Match`'s pattern compiler unconditionally
-- packs discriminant types via `PProd`, even for a single wildcard
-- alt), and `inductive N`'s `.brecOn` needs `Prod` (`hasUnit &&
-- hasProd` gate, `Elab/MutualInductive.lean:1555`) for the structural
-- recursion `count` below to get smart-unfolding markers at all. So
-- this file opens with the SAME scaffold prefix as `tests/fixtures/
-- Matcher.lean` (verbatim, `lcErased` through `Prod`) — see that
-- file's own doc comment for the exact oracle citations
-- (`Init/Prelude.lean`, v4.33.0-rc1) each scaffold declaration is
-- copied or minimally adapted from. Task 1 established this scaffold;
-- this task reuses it rather than re-deriving it.
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

-- === Meta0-specific corpus below (M4a plan 2 task 8) ===

-- beta / plain delta at each status
inductive N where
  | zero : N
  | succ : N → N

@[reducible] def redId (n : N) : N := n
def semiDouble (n : N) : N := N.succ (N.succ n)
@[irreducible] def irredId (n : N) : N := n

-- zeta
def letChain : N := let a := N.zero; let b := N.succ a; N.succ b

-- proj (a structure-like single-ctor inductive). `structure` itself is
-- confirmed to work under this scaffold (PProd/Prod above are
-- structures); the anonymous-constructor `⟨...⟩` notation is core
-- term syntax (not Init-dependent) and also compiled cleanly here, so
-- no fallback to an explicit single-ctor `inductive` was needed.
structure P where
  fst : N
  snd : N

def mkP : P := ⟨N.zero, N.succ N.zero⟩
def useFst (p : P) : N := p.fst

-- iota (recursor application; noncomputable — recursors aren't compiled)
noncomputable def add (a b : N) : N :=
  N.rec a (fun _ ih => N.succ ih) b

-- matcher + smart unfolding (structural recursion) — same shape as
-- Matcher.lean's own `count`, confirmed to emit `count._sunfold` under
-- this scaffold.
def count (n : N) : N :=
  match n with
  | .zero => .zero
  | .succ m => .succ (count m)
