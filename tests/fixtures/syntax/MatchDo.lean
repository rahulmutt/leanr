prelude

-- M3a Task 9: `match`/`do` — the doElem category (Do.lean) plus the
-- term-category `do`-block wrappers. Builtin-only grammar throughout
-- (no Init notation/operators); every binder/type lives at TERM level
-- (`fun (x : A) => ..`), since `command.rs`'s `optDeclSig` (decl-level
-- binders/types) is still Task 10's job — every fixture uses the bare
-- `def name := <term>` shape the rest of tests/fixtures/syntax/ already
-- establishes.

-- match: single discriminant, single pattern.
def m1 := fun (n : A) => match n with
  | z => z

-- match: constructor pattern with a wildcard argument.
def m2 := fun (p : A) => match p with
  | pair a _ => a

-- match: multiple discriminants (comma-separated), multi-line `with`.
def m3 := fun (n m : A) =>
  match n, m with
  | a, b => f a b

-- match: multiple patterns per alt (`| a | b => e`), nested match in
-- the rhs of another alt.
def m4 := fun (n : A) => match n with
  | z | one => z
  | s a => match a with
    | z => a
    | s b => b

-- do: let / letArrow / if-then-else / return, multi-line.
def doBlock := fun (act : A) => do
  let x ← act
  let y := f x
  if cond then
    pure y
  else
    act

-- do: for loop, multi-line body, trailing bare `return`.
def doFor := fun (xs : A) => do
  for x in xs do
    consume x
  return

-- do: nested `do` (a do-block whose let-arrow's RHS is itself a
-- multi-line do-block).
def doNested := do
  let a ← do
    let b ← inner
    pure b
  pure a

-- do: else-if chain (multi-branch), each branch itself multi-line.
def doIfChain := fun (a b c : A) => do
  if a then
    x
  else if b then
    y
  else if c then
    z
  else
    w

-- do: reassignment of a `mut` binding, dbg_trace, assert!.
def doMut := do
  let mut x := a
  x := b
  dbg_trace x
  assert! cond
  pure x

-- do: while / repeat-until / unless / break / continue.
def doLoops := fun (xs : A) => do
  for y in xs do
    if p y then
      break
    continue
  while cond do
    step
  repeat
    tick
  until done
  unless cond do
    other

-- term-level `do` wrappers used directly as a `def`'s value (bare
-- `unless`/`for`/`try`/`return` as TERMS, not inside a `do` block —
-- `termUnless`/`termFor`/`termTry`/`termReturn`).
def termUnlessEx := fun (cond act : A) => unless cond do
  act
def termForEx := fun (xs : A) => for y in xs do
  g y
def termTryEx := fun (act : A) => try
  act
catch e =>
  h e
def termReturnEx := fun (z : A) => return z

-- nested action `(← e)` and the `do←` forwarding form, each as the
-- last argument of a function application.
def nestedActionEx := fun (f act : A) => f (← act)
def doForwardEx := fun (f act : A) => f (do← act)
