prelude

namespace Outer
namespace Inner
def deep := x
end Inner
end Outer

section MySection
universe u v
variable (α : Sort u) {β : Sort v}
def usesVars (a : α) := a
end MySection

open Outer
open Outer.Inner in
def opened := deep
open Outer (Inner)
set_option maxHeartbeats 400000
set_option pp.all true in
def optioned := x
attribute [someAttr] opened
export Outer (Inner)
#check opened

def usesTermOpen := open Outer.Inner in deep
def usesTermSetOption := set_option pp.all true in deep
example : Sort 1 := by open Outer.Inner in match deep with | hp => _
example : Sort 1 := by set_option pp.all true in match deep with | hp => _

initialize initField : Nat ← pure z

builtin_initialize
  pure z

attribute [-someAttr, someAttr] opened

instance (priority := 200) : Inhabited Nat where
  default := z
