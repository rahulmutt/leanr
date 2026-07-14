prelude

/-- A doc comment. -/
def documented (a : A) : A := a
@[someAttr] def attributed := x
private def hidden' := x
protected def prot := x
noncomputable def nc : A := x
unsafe def dangerous : A := x
partial def looping (a : A) : A := looping a
theorem thm (h : P) : P := h
abbrev shortcut : A := x
example : A := x
axiom ax : P
opaque opq : A
def withEqns : N → N
  | z => z
def withWhere : A := helper
  where helper : A := x
mutual
  def evenish : N → N
    | z => z
  def oddish : N → N
    | z => z
end
