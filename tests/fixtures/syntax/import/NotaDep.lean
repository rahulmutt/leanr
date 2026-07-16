-- Declares the imported-notation surface the importer fixtures use.
-- Each mixfix fixity, a multi-token notation, an ASCII munch token,
-- a scoped notation (must be SKIPPED by leanr), and a custom category
-- reachable from term.
infixl:65 " ⊕⊕ " => HAdd.hAdd
infixr:67 " ⊗⊗ " => HMul.hMul
prefix:100 "⋄⋄" => Nat.succ
postfix:200 "‼" => Nat.succ
notation:50 "⟪" x "⟫" => Nat.succ x
infixl:60 " +++ " => HAdd.hAdd
namespace NotaDep
scoped infixl:65 " ⊖⊖ " => HSub.hSub
end NotaDep
declare_syntax_cat widget
syntax "wob" : widget
syntax num : widget
syntax "wrap[" widget "]" : term
