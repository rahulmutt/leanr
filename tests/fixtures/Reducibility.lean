-- Fixture for the `reducibilityCore` / `reducibilityExtra` environment
-- extension decode (M4a plan 1, task 2). Each attribute below is one
-- of the five that funnel into `setReducibilityStatusCore`
-- (ReducibilityAttrs.lean:90); `plainDef` carries no attribute and must
-- therefore be ABSENT from the extension array, exercising the
-- `.semireducible` default rather than an explicit entry.
--
-- `@[semireducible] def semiredDef` was dropped: the oracle (v4.33.0-rc1)
-- rejects it with "failed to set `[semireducible]` for `semiredDef`
-- because it already is `[semireducible]`" — `semireducible` is the
-- default status, so an explicit `@[semireducible]` is a no-op the
-- oracle refuses rather than silently allows. `plainDef` already covers
-- the semireducible-by-default case.
@[reducible] def redDef : Nat := 1
@[irreducible] def irredDef : Nat := 2
@[instance_reducible] def instRedDef : Nat := 4
@[implicit_reducible] def implRedDef : Nat := 5
def plainDef : Nat := 6
