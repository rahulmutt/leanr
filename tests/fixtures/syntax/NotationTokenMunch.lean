-- M3b1 Task 8: a same-file notation registers a token that changes
-- MAXIMAL-MUNCH tokenization of later source — the overlay's
-- `munch_with` union (Task 1). `⊗` is declared first; `⊗⊗` (of which
-- `⊗` is a strict PREFIX) is declared second. Once `⊗⊗` is registered,
-- the lexer must munch it as ONE token wherever it appears, never as
-- two adjacent `⊗` tokens. `⊗`/`⊗⊗` are NOVEL (absent from Init — see
-- NotationMixfix.lean).
infixl:65 " ⊗ " => Sum
infixl:70 " ⊗⊗ " => Prod

-- Before `⊗⊗` is even relevant: plain `⊗` still tokenizes on its own.
example := a ⊗ b
-- Munch competition: at the `⊗` position, `⊗⊗` (registered, 2 chars)
-- must beat `⊗` (registered, 1 char) — maximal munch, not declaration
-- order.
example := a ⊗⊗ b
