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
-- whatever the oracle says). Task 3 REVIEW fix: `local syntax`/`local
-- macro` alone left the ordering fix (`notation.rs:806-810`, qualify
-- THEN privatize) with zero regression coverage — every `local
-- notation`/`local mixfix` fixture (`NotationLocal.lean`,
-- `NotationMixfix.lean`) sits at empty namespace, where the OLD
-- (privatize-then-qualify) and NEW orderings coincide byte-for-byte,
-- so a silent revert of the reordering would still pass every
-- existing test. `local notation "woblocnot" => 47` inside `Widgloc`
-- below closes that gap for the `notation` sugar surface specifically
-- (as opposed to `local syntax`, already covered by `woblocns` above).
local syntax "wobloc" : term
macro_rules | `(wobloc) => `(45)
#check wobloc
namespace Widgloc
local syntax "woblocns" : term
macro_rules | `(woblocns) => `(46)
#check woblocns
local notation "woblocnot" => 47
#check woblocnot
end Widgloc
local macro "woblocm" : term => `(47)
#check woblocm
