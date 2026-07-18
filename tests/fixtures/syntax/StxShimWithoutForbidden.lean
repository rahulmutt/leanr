syntax "woforb " withoutForbidden(term) : term
macro_rules | `(woforb $x) => `($x)
#check woforb 1
