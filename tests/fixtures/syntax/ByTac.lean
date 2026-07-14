prelude

-- M3a Task 9: `by` blocks — Term.byTactic + the builtin `tactic`
-- category. The builtin tactic set is deliberately tiny (surface
-- table: `unknown`/`nestedTactic`/`«match»`/`introMatch`, plus the
-- `tacticSeq` machinery — anything more, e.g. `exact`/`intro <ident>`/
-- `simp`, is `Init`-declared and lands in M3b). This fixture's `by`-
-- block coverage is therefore syntactic, not tactic-breadth: `by` +
-- `tacticSeq` + a builtin tactic, matching the spec's own scope line.
--
-- Honest caveat (also called out in the task brief): an UNRECOGNIZED
-- tactic name (e.g. `nested (hp)`) parses as `Tactic.unknown`, whose
-- `errorAtSavedPos` genuinely reports a Parser-level "unknown tactic"
-- message in real Lean (confirmed: `lean ByTac.lean` would fail to
-- compile cleanly) — NOT eligible for this "zero parse errors" fixture.
-- Every tactic-mode `match`/`intro` alt below instead bottoms out in
-- `Term.hole` (`_`) — `Tactic.lean`'s own `matchRhs := Term.hole <|>
-- Term.syntheticHole <|> tacticSeq` names `_`/`?_` as legitimate,
-- non-tactic alt bodies, confirmed against a fresh oracle dump (zero
-- parser messages — task-9 report).

-- by + tacticSeq1Indented + «match», single alt.
def t1 := fun (h : A) => by
  match h with
  | hp => _

-- by + introMatch.
def t2 := fun (h : A) => by
  intro
  | hp => _

-- by + nested `match` (a tactic-mode match nested inside another
-- tactic-mode match's alt).
def t3 := fun (h : A) => by
  match h with
  | hp => match hp with
    | hp2 => _

-- by + tacticSeqBracketed (`{ .. }`, `nestedTactic`), used as a SECOND
-- tactic in the same `tacticSeq` (a multi-line sequence — one
-- `«match»` tactic, then a bracketed nested-tactic block).
def t4 := fun (h : A) => by
  match h with
  | hp => _
  { match h with
    | hp2 => _ }

-- by + multiple tactics on ONE line separated by `;` (sepByIndentSemicolon
-- requires the explicit `;` when two tactics share a line).
def t5 := fun (h h2 : A) => by match h with | hp => _; match h2 with | hp2 => _

-- multiple patterns per `«match»` alt (`| a | b => _`), tactic mode.
def t6 := fun (h : A) => by
  match h with
  | hp | hq => _

-- `byTactic'` (the `show .. by ..` / `suffices .. by ..` rhs form).
def t7 := fun (h : A) => show A by
  match h with
  | hp => _

-- Nested `by`: the OUTER `by`'s tactic-mode `match` discriminant is
-- itself a parenthesized proof term built from ANOTHER `by` block.
def t8 := fun (h : A) => by
  match (by match h with | hp => _) with
  | hp2 => _
