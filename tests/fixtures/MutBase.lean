-- Hermetic, import-free base module for the mutation-differential harness
-- (M1b Task 15). `prelude` suppresses the implicit `import Init`, so the whole
-- constant set is built from scratch and the kernel replays it from an empty
-- environment (no toolchain needed at test time). `mutate.lean` mutates the
-- safe defs/theorems declared here and records the real kernel's verdicts;
-- `Mutations0.olean` (the mutants) plus `MutBase.olean` (this base) are the
-- hermetic, CI-green inputs to `check_fixtures.rs::mutation_verdicts_hermetic`.
--
-- The declarations are chosen for verdict diversity under the 5 structural
-- mutations: several are two-argument applications whose last two arguments
-- have DIFFERENT types (so swapping them type-errors → reject), a few have a
-- `Sort` in their type (so bumping the universe → reject), the types alternate
-- (so value crossover between neighbours → reject), and the theorems / nullary
-- values stay well typed under the identity wrapper (→ accept).
prelude

inductive N where
  | zero : N
  | succ : N → N

inductive B where
  | tt : B
  | ff : B

-- A `Prop` with a trivial proof, for exercising the theorem-admission arm.
inductive P : Prop where
  | intro : P

-- Two-argument functions with MISMATCHED argument types: swapping the last two
-- arguments of an application of these type-errors.
def useNB (n : N) (_b : B) : N := n
def useBN (_b : B) (n : N) : N := n

-- Application-valued defs (value = `useNB _ _` / `useBN _ _`): mutation (a)
-- swaps the last two args → the `N`/`B` mismatch rejects.
def app0 : N := useNB N.zero B.tt
def app1 : N := useBN B.ff N.zero
def app2 : N := useNB (N.succ N.zero) B.ff
def app3 : N := useBN B.tt (N.succ N.zero)
def app4 : N := useNB N.zero B.ff
def app5 : N := useBN B.ff (N.succ (N.succ N.zero))

-- `Sort`-typed defs: mutation (c) bumps the universe of the type → the value no
-- longer inhabits the bumped type, so it rejects.
def ty0 : Type := N
def ty1 : Type := B

-- Recursive defs (values are `.rec` applications) for extra body shapes.
noncomputable def add (a b : N) : N :=
  N.rec (motive := fun _ => N) a (fun _ ih => N.succ ih) b

noncomputable def neg (b : B) : B :=
  B.rec (motive := fun _ => B) B.ff B.tt b

-- Lambda-valued def: mutation (e) can drop the binder's use.
def constN : B → N := fun _ => N.zero

-- Theorems: values are constructor applications; identity-wrapped they stay
-- well typed (accept), but a value crossover onto them rejects.
theorem triv0 : P := P.intro
theorem triv1 : P := P.intro
theorem triv2 : P := P.intro
