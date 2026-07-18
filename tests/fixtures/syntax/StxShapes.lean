declare_syntax_cat widgetish
declare_syntax_cat gadget (behavior := symbol)
syntax "wob" : widgetish
syntax num : widgetish
syntax:65 "probe" term : term
syntax (name := probed) "probe!" term,* : term
syntax "grab[" widgetish "]" : term
syntax "many_of" term+ : term
syntax "opt_of" (term)? : term
syntax "many1_of" many1(term) : term
syntax "alt_of" orelse(term, num) : term
syntax "sep_of" sepBy(term, ", ") : term
syntax "sep1_of" sepBy1(term, ", ") : term
syntax "nonres" &"weird" : term
syntax myNum := num
