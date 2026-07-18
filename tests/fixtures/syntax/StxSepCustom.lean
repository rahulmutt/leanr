syntax "wobalt" sepBy(term, "|") : term
macro_rules | `(wobalt $xs|*) => `(42)
#check wobalt 1 | 2 | 3
def s := `(wobalt $[1]|* )
