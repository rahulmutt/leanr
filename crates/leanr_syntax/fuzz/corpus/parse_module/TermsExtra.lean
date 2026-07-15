prelude

-- M3a Task 8 wave 2: the term-category "port"-status rows wave 1 left
-- unported (cdot, the app/proj extras, the let-family siblings, the
-- elaborator-pragma terms, the parser-authoring meta-DSL). Builtin-only
-- grammar throughout (no Init notation/operators, no decl-level
-- binders/types — `command.rs`'s `optDeclSig` is still Task 10's job,
-- same constraint Terms.lean's own header documents).

-- cdot (both spellings) inside `paren`.
def cdotUnicode := (·)
def cdotAscii := (.)

-- dotIdent: leading "." + ident, distinct from `proj`'s trailing "."
-- (Terms.lean's `projections` already exercises the latter).
def dotIdentTerm := .mk

-- namedPattern: `x@pat` inside a match pattern position.
def namedPatternTerm := match x with
  | y@Foo.mk => y
  | _ => x

-- pipeProj / pipeCompletion.
def pipeProjTerm := x |>.foo
def pipeCompletionTerm := x |>.

-- Chained forms (review finding 1): `pipeProj`/`subst` are singly-
-- annotated `trailing_parser`s (only `prec` given) whose OMITTED
-- `lhsPrec` defaults to 0 (ORACLE-PORT `BuiltinNotation.lean:194-197`),
-- not to their own `prec` — so a further `proj`/`subst` (both requiring
-- `lhs_prec >= 0`, always true) must still apply on top of a `pipeProj`
-- result. Previously mis-registered with `lhsPrec` equal to `pipeProj`'s
-- own `prec` (MIN_PREC), which wrongly gated these out.
def pipeProjThenProjTerm := x |>.foo.1
def pipeProjThenSubstTerm := x |>.foo ▸ y

-- subst.
def substTerm := h ▸ x

-- panic! / unreachable! / dbg_trace.
def panicTerm := panic! "boom"
def unreachableTerm := unreachable!
def dbgTraceTerm := dbg_trace x; y

-- borrowed (@&), inside an application argument.
def borrowedTerm := f (@& x)

-- no_index.
def noindexTerm := no_index x

-- binrel%/binrel_no_prop%/binop%/binop_lazy%/leftact%/rightact%/unop%.
def binrelTerm := binrel% Eq a b
def binrelNoPropTerm := binrel_no_prop% Eq a b
def binopTerm := binop% f a b
def binopLazyTerm := binop_lazy% f a b
def leftactTerm := leftact% f a b
def rightactTerm := rightact% f a b
def unopTerm := unop% f a

-- for_in%/for_in'%.
def forInTerm := for_in% x y z
def forInTerm' := for_in'% x y z

-- let-family siblings.
def letFunTerm := let_fun x := 1; x
def letDelayedTerm := let_delayed x := 1; x
def letTmpTerm := let_tmp x := 1; x
def haveITerm := haveI x := 1; x
def letITerm := letI x := 1; x
def letrecTerm := let rec x := 1; x

-- elaborator-pragma terms.
def stateRefTTerm := StateRefT Foo Bar
def stateRefTDollarTerm := StateRefT Foo $ Baz
def showTermElabTerm := show_term_elab x
def matchExprTerm := match_expr e with
  | Foo a b => a
  | _ => e
def letExprTerm := let_expr Foo a b := e | a; a
def throwNamedErrorTerm := throwNamedError foo.bar x
def throwNamedErrorAtTerm := throwNamedErrorAt x foo.bar y
def logNamedErrorTerm := logNamedError foo.bar x
def logNamedErrorAtTerm := logNamedErrorAt x foo.bar y
def logNamedWarningTerm := logNamedWarning foo.bar x
def logNamedWarningAtTerm := logNamedWarningAt x foo.bar y
def declNameTerm := decl_name%
def privateDeclTerm := private_decl% x
def withDeclNameTerm := with_decl_name% foo x
def withDeclNameHoleTerm := with_decl_name% ?foo x
def typeOfTerm := type_of% x
def ensureTypeOfTerm := ensure_type_of% x "msg" y
def ensureExpectedTypeTerm := ensure_expected_type% "msg" x
def noImplicitLambdaTerm := no_implicit_lambda% x
def inferInstanceAsTerm := inferInstanceAs Foo
def inferInstanceAsDollarTerm := inferInstanceAs $ Foo
def valueOfTerm := value_of% x
def clearTerm := clear% x; y
def letMVarTerm := let_mvar% ?m := x; y
def waitIfTypeMVarTerm := wait_if_type_mvar% ?m; y
def waitIfTypeContainsMVarTerm := wait_if_type_contains_mvar% ?m; y
def waitIfContainsMVarTerm := wait_if_contains_mvar% ?m; y
def defaultOrOfNonemptyTerm := default_or_ofNonempty%
def defaultOrOfNonemptyUnsafeTerm := default_or_ofNonempty% unsafe
def noErrorIfUnusedTerm := no_error_if_unused% x
def idbgTerm := idbg x; y
def assertTerm := assert! x; y
def debugAssertTerm := debug_assert! x; y
def elabToSyntaxTerm := elabToSyntax% 3

-- parser-authoring meta-DSL (kept to a single string-literal body to
-- avoid the `>>` Init-notation entanglement the task-8-wave2 report
-- documents — see `term_pragma.rs`'s module doc).
def leadingParserTerm := leading_parser "foo"
def trailingParserTerm := trailing_parser "foo"
