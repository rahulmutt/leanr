-- M3b1 Task 8: `local notation` declared and used later in the same
-- file (spec §7: `local notation` in scope, `scoped` excluded). `★` is
-- NOVEL (absent from Init — see NotationMixfix.lean). `Term.attrKind`
-- (`command_notation.rs`'s `notation_prefix`) already carries the
-- optional `local`/`scoped` prefix (`attr.rs`'s `scoped_or_local`), so
-- this needs no new grammar — Task 8's job is exercising it against a
-- real oracle dump.
local notation "★" => Sum

example := ★
