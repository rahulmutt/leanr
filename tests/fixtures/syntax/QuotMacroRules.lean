syntax "probe" term : term
macro_rules | `(probe $x) => `(f $x)
macro "twice" x:term : term => `(f $x $x)
#check probe 4
#check twice 3
