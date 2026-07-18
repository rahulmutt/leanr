-- M3b3 Task 6b: a `local syntax` anchors its activation to the exact
-- scope entry that declared it, NOT to scope depth. Ported from the
-- Task 6 oracle probe (see `parse.rs`'s
-- `local_activation_anchors_to_its_declaring_scope` pin test). Three
-- pinned facts, dumped by the ELABORATING dumper (`dump_syntax_elab.
-- lean`) since the private-kind wrap only appears after `elabSyntax`:
--   * inside the declaring `section A`, and in a `section C` nested
--     BELOW the declaration, `wobinact` dispatches the private
--     production (`_private.0.termWobinact`) — still active;
--   * after `end A` closes the declaring scope, an UNRELATED
--     `section B` reaching the SAME depth does NOT re-activate it:
--     `#check wobinact` there is a plain IDENT.
-- The old `>=`-depth predicate wrongly re-activated in `section B`;
-- the oracle (this dump) is the byte authority proving it must not.
section A
local syntax "wobinact" : term
macro_rules | `(wobinact) => `(99)
section C
#check wobinact
end C
#check wobinact
end A
section B
#check wobinact
end B
