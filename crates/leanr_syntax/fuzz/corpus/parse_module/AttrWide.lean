prelude

@[macro foo] def a1 := x
@[export foo] def a2 := x
@[recursor 0] def a3 := x
@[instance] def a4 := x
@[instance 100] def a5 := x
@[default_instance] def a6 := x
@[default_instance 50] def a7 := x
@[specialize] def a8 := x
@[specialize foo 1] def a9 := x
@[extern "foo"] def a10 := x
@[extern foo inline "bar"] def a11 := x
@[tactic_alt foo] def a12 := x
@[tactic_tag foo bar] def a13 := x
@[tactic_name foo] def a14 := x
@[tactic_name "foo"] def a15 := x
@[local simp] def a16 := x
@[scoped simp] def a17 := x
class inductive Cls where
  | mk : Cls
