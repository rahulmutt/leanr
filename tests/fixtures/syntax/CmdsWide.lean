prelude

mutual
  def isEven : Nat → Bool
    | z => z
  def isOdd : Nat → Bool
    | z => z
end

coinductive Stream' (α : Sort 1) where
  | mk : α → Stream' α → Stream' α

class inductive Wrap (α : Sort 1) where
  | mk : α → Wrap α

with_weak_namespace Foo
  def bar := x

namespace Q
open Q hiding a
open Q renaming a → b
open scoped Q
end Q

#check_assertions!

#print sig foo
#print axioms foo
#print equations foo
#print tactic tags

structure HasCtor where
  mk2 ::
  z : Nat

/-! Module doc. -/

/-- Doc for addDocString. -/
add_decl_doc foo

deprecated_syntax Lean.Parser.Term.let_fun "use have" (since := "2026-01-01")
deprecated_module "use NewMod" (since := "2026-01-01")
docs_to_verso Foo, Bar

grind_pattern [foo] bar => baz, qux
init_grind_norm a b | c d
