import Lean
open Lean Parser in
@[term_parser] def rawWidget : Parser :=
  leading_parser "rawwob"
