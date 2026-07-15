prelude

-- M3a Task 9: `Term.structInstFields`'s `sepByIndent` fix (was a KNOWN
-- DIVERGENCE — approximated with a plain, non-indentation-aware
-- `SepBy` — task-8 report's Fix wave 1 section). Real `sepByIndent`
-- (comma-separated, implicit-newline alternative) is now available
-- (`do_notation.rs`/`tactic.rs`'s `sepBy1IndentSemicolon`/
-- `sepByIndentSemicolon` share the same generalized `Prim::SepByIndent`
-- primitive, `grammar.rs`) — this fixture is the MULTI-LINE structure-
-- instance case that would have caught the old approximation being
-- wrong (a newline-separated, no-comma field list). Each field starts
-- FRESH on its own line, all at the SAME column (the `sepByIndent`
-- marker is set at the position of the FIRST field — every
-- subsequent field must be at or past that column, or an EXPLICIT `,`
-- is required).

-- multi-line, no commas at all (implicit newline separators only).
def foo := fun (x y : A) =>
  { a := x
    b := y : S }

-- multi-line, MIXED: one explicit comma, one implicit newline.
def bar := fun (x y z : A) =>
  { a := x, b := y
    c := z : S }

-- single-line, comma-separated (unaffected by the fix — kept as a
-- regression check that the ordinary case still works).
def baz := fun (x y : A) => { a := x, b := y : S }
