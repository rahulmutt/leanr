-- M3b1 Task 8: a multi-token `notation` with interior placeholders (3
-- placeholders, 2 symbol tokens) — the task brief's own illustrative
-- shape. `⊗`/`⊘` are NOVEL (absent from Init — see NotationMixfix.lean
-- for the grep confirmation; reused here since fixtures parse
-- independently, no cross-file grammar leakage).
notation:70 a " ⊗ " b " ⊘ " c => Sum (Sum a b) c

example := x ⊗ y ⊘ z
