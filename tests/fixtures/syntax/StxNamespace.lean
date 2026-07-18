namespace Widgetish
syntax "wobns" : term
macro_rules | `(wobns) => `(42)
#check wobns
syntax (name := probeNamed) "wobnamed" : term
macro_rules | `(wobnamed) => `(43)
#check wobnamed
namespace Inner
notation "wobnest" => 44
#check wobnest
end Inner
end Widgetish
#check wobns
