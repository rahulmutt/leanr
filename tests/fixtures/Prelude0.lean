-- A `prelude`-mode fixture that imports NOTHING: it declares a tiny,
-- self-contained world so the kernel can replay it from an empty
-- environment (crates/leanr_olean/tests/check_fixtures.rs). Because
-- `prelude` suppresses the implicit `import Init`, every constant here
-- is built from scratch — there is no `Nat`, `Eq`, etc. to lean on.
prelude

-- An inductive with a recursive constructor (`succ`), which forces the
-- kernel to regenerate a real recursor (`N.rec`) during replay.
inductive N where
  | zero : N
  | succ : N → N

-- A definition that USES the recursor, so replay must admit `N` (and
-- regenerate `N.rec`) before this def and its postponed recursor check.
-- `noncomputable` because applying a recursor directly is not something
-- the code generator compiles (irrelevant to kernel checking, which is
-- all replay cares about).
noncomputable def N.add (a b : N) : N :=
  N.rec (motive := fun _ => N) a (fun _ ih => N.succ ih) b

-- A `Prop`-valued inductive and a theorem over it, exercising the
-- theorem admission arm.
inductive Truth : Prop where
  | intro : Truth

theorem triv : Truth := Truth.intro
