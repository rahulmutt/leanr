syntax "wopos " withoutPosition(term,*) : term
macro_rules | `(wopos $xs,*) => `(0)
#check wopos 1, 2
