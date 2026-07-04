axiom richAxiom : Nat → Prop

opaque richOpaque : Nat := 7

inductive RichTree where
  | leaf : RichTree
  | node : RichTree → RichTree → RichTree

structure RichPoint where
  x : Nat
  y : Nat

def richBig : Nat := 340282366920938463463374607431768211455

def richString : String := "héllo⟨w⟩orld"

theorem richTheorem : richOpaque = richOpaque := rfl

partial def richPartial (n : Nat) : Nat :=
  if n == 0 then 0 else richPartial (n - 1)

mutual
  def richEven : Nat → Bool
    | 0 => true
    | n + 1 => richOdd n
  def richOdd : Nat → Bool
    | 0 => false
    | n + 1 => richEven n
end
