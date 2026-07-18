syntax "wobind" sepByIndentSemicolon(term) : term
macro_rules | `(wobind $[$xs]*) => `(42)
#check wobind 1; 2
