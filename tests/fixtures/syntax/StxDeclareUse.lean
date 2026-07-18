declare_syntax_cat widgetish
syntax "wob" : widgetish
syntax num : widgetish
syntax "grab[" widgetish "]" : term
macro_rules
  | `(grab[wob]) => `(0)
  | `(grab[$n:num]) => `($n)
#check grab[wob]
#check grab[42]
