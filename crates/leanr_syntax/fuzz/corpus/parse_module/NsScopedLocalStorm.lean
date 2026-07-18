prelude

namespace Widgsc
scoped syntax "wobsc" : term
macro_rules | `(wobsc) => `(48)
#check wobsc
end Widgsc
open Widgsc
#check wobsc

section A
local syntax "wobloc" : term
macro_rules | `(wobloc) => `(45)
#check wobloc
end A
section B
#check wobloc
end B

namespace Outer.Inner
syntax "wobns" : term
macro_rules | `(wobns) => `(1)
#check wobns
end Outer.Inner
#check wobns
