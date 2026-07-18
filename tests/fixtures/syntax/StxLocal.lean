-- M3b3 Task 3: `local` on the general `syntax`/`macro` surface derives
-- the PRIVATE kind name, the same `mkPrivateName` gate
-- `notation.rs`'s `mangle_private_kind` already pins for `local
-- notation`/`local infixl`/… (`NotationLocal.lean`) — `Lean/Elab/
-- Syntax.lean:432`'s `elabSyntax` applies it uniformly regardless of
-- whether the declaration came through the `notation` sugar or the
-- general `syntax`/`macro` surface. A `local syntax` INSIDE a
-- `namespace` block is included too, to pin the prefix ORDERING
-- between the `_private.0.` wrap and the namespace qualification
-- (`_private.0.Ns.x` vs `Ns._private.0.x` — both chains must agree,
-- whatever the oracle says).
local syntax "wobloc" : term
macro_rules | `(wobloc) => `(45)
#check wobloc
namespace Widgloc
local syntax "woblocns" : term
macro_rules | `(woblocns) => `(46)
#check woblocns
end Widgloc
local macro "woblocm" : term => `(47)
#check woblocm
