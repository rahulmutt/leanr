-- M3b1 Task 8: two notations sharing a leading token (`⊛`) — the
-- end-to-end coverage for Task 6's overloaded-dispatch tie-break
-- (`longest_match`, ORACLE-PORT `runLongestMatchParser`): among
-- leading candidates dispatched off the SAME first token, the one that
-- consumes the MOST input wins. `⊛`/`⋈` are NOVEL (absent from Init —
-- see NotationMixfix.lean).
prefix:75 "⊛" => Not
notation:75 "⊛" a:75 " ⋈ " b:75 => Sum a b

-- Only the short (prefix) candidate can match here: nothing after `x`
-- looks like ` ⋈ `.
example := ⊛ x
-- The shared leading token `⊛` dispatches BOTH candidates; the wider
-- notation consumes strictly more input (through `⋈ y`) so it wins.
example := ⊛ x ⋈ y
