namespace Widgsc
scoped syntax "wobsc" : term
macro_rules | `(wobsc) => `(48)
#check wobsc
end Widgsc
open Widgsc
#check wobsc
namespace Widgsc.Inner
#check wobsc
end Widgsc.Inner
