-- M3b1 Task 8: one of each mixfix family member (infixl/infixr/infix/
-- prefix/postfix), each with a NESTED use pinning associativity. No
-- `prelude` header (see dump_syntax_elab.lean's module doc): the
-- elaborating oracle dumper needs the implicit `import Init` this
-- omission gives it. Symbols are all NOVEL — absent from the pinned
-- toolchain's own `Init/` (verified: `grep -rn ' ⊗ \| ⇛ \| ⊙ \|⊹|⊺'
-- over Init/` — no hits) — so no `_1`-suffixed collision with an
-- existing Init declaration (e.g. `⊕`, already `infixr:30 " ⊕ " =>
-- Sum` in `Init.Core`).
infixl:65 " ⊗ " => Sum
infixr:65 " ⇛ " => Prod
infix:65 " ⊙ " => And
prefix:100 "⊹" => Not
postfix:100 "⊺" => Not

example := a ⊗ b ⊗ c
example := a ⇛ b ⇛ c
example := a ⊙ b
example := ⊹ ⊹ a
example := a ⊺ ⊺
