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
