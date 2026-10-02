//! `ElabError`: every way leaf term elaboration can fail to produce an
//! `ExprId`. Named-seam discipline: an unsupported construct is a
//! variant carrying the kind name, never a panic.

use leanr_kernel::bank::ExprId;
use leanr_meta::MetaError;

#[derive(Debug)]
pub enum ElabError {
    /// A syntax kind with no leaf elaborator in M4b-1. Carries the kind
    /// name. Named seam: binders/app/num/char/match/etc. land in later
    /// M4b slices; until then their kinds arrive here, never silently.
    UnsupportedSyntax(String),
    UnknownIdent(String),
    /// oracle: `throwUnknownConstantAt` — the `binop%` family's head did not
    /// resolve (`Extra.lean:213`, `:220`, `:562`).
    UnknownConstant(String),
    AmbiguousIdent(String),
    /// `ensureHasType`'s mismatch: `mkCoe`'s `.none` answer and its
    /// caught `MetaError::CoeExpansionMismatch` both land here
    /// (`TermElabM.lean:1307`, `:1313-1317`, `:1322`) — the coercion
    /// search or a post-expansion check genuinely failed, as opposed to
    /// `StuckCoercion` (not-yet-solvable). Before M4b-3 P4 this was
    /// raised directly by every defeq-mismatch site; since P4 it is
    /// raised only from inside `coe::mk_coe`/`ensure_has_type`, reached
    /// through `elab_term_ensuring_type`, the `($e :)` ascription arm,
    /// and `elab_and_add_new_arg`'s `ensureArgType`.
    TypeMismatch {
        expected: ExprId,
        got: ExprId,
    },
    Meta(MetaError),
    /// oracle: `addNamedArg`'s "Argument `x` was already set"
    /// (`Arg.lean:55-59`).
    DuplicateNamedArg(String),
    /// oracle: `mkConst`'s "too many explicit universe levels for
    /// '{constName}'" (`Lean/Elab/Term/TermElabM.lean:2128-2136`).
    /// Carries the head identifier's raw source text. Reachable only
    /// once `.{u, v}` explicit-universe syntax has a producer (M4b-3 P1
    /// task 8); the check itself lives in `app::head::elab_app_fn_id`
    /// from task 4 on, so the arm can never be silently skipped.
    TooManyUniverseLevels(String),
    /// A syntax node whose shape contradicts the grammar (missing child,
    /// wrong node/token variant, a non-trailing `..`). Distinct from
    /// `UnsupportedSyntax`, which means "this construct's slice has not
    /// landed"; this means "this tree cannot be what it claims to be".
    IllFormedSyntax(String),
    /// oracle: `synthesizeInstMVarCore`'s `.none` arm — "failed to
    /// synthesize" (`TermElabM.lean:1275-1288`). Carries the goal type;
    /// the oracle's `extraErrorMsg?` prose is deferred (design spec
    /// § Amendment, item 2). Unmodelled: the `.none` arm's own
    /// `ignoreTCFailures` reader-context escape (`if (← read
    /// ).ignoreTCFailures then return false`, `TermElabM.lean:1276-1277`)
    /// — a caller can ask to treat "no instance found" as "not ready
    /// yet" rather than a hard failure; leanr has no reader context
    /// carrying that flag, so this variant always fires as a hard
    /// error, which is the one unmodelled branch of
    /// `synthesizeInstMVarCore` with no note anywhere else in this
    /// crate.
    InstanceSynthesisFailed {
        goal: ExprId,
    },
    /// oracle: `reportStuckSyntheticMVar`'s `.typeClass` arm —
    /// "typeclass instance problem is stuck"
    /// (`SyntheticMVars.lean:295-303`). Carries the goal type; the note
    /// and hint prose are deferred.
    StuckSyntheticMVar {
        goal: ExprId,
    },
    /// oracle: the stuck reporter's `.coe` arm (`SyntheticMVars.lean:304-310`)
    /// — `throwTypeMismatchError header expectedType (← inferType e) e f?
    /// "failed to create type class instance for {mvar type}"`. A
    /// distinct variant from `TypeMismatch` (which `mkCoe`'s IMMEDIATE
    /// failure keeps, `TermElabM.lean:1317,1322`) so a test can tell
    /// "stuck" from "impossible". The mvar's type IS `expected`.
    StuckCoercion {
        expected: ExprId,
        got: ExprId,
    },
    /// oracle: `synthesizeInstMVarCore`'s assignment-mismatch throws
    /// (`TermElabM.lean:1265-1272`) — the synthesized instance is not
    /// defeq to the one typing already inferred. Two distinct call
    /// sites collapse into this one variant: the "already assigned, not
    /// defeq" throw (`inferred` is `infer_type(old_val)`, the
    /// pre-existing assignment's type) and the "not yet assigned,
    /// assignment failed" throw (`inferred` is the mvar's own declared
    /// type — there is no `old_val` to infer from).
    InstanceMismatch {
        synthesized: ExprId,
        inferred: ExprId,
    },
    /// oracle: `"Function expected at .. but this term has type .."`
    /// (`App.lean:409-411`). Carries the head and its type; the oracle's
    /// `.note` hint about indentation mishaps (`App.lean:404-408`) is
    /// prose (deferred).
    FunctionExpected {
        f: ExprId,
        f_type: ExprId,
    },
    /// oracle: `ensureType`'s "type expected, got …"
    /// (`TermElabM.lean:1946-1949`). Raised from `binder/mod.rs`'s
    /// `elab_type` since M4b-3 P4; before that a non-type domain was
    /// (wrongly) a value-level `TypeMismatch` against `Sort ?u`.
    TypeExpected {
        e: ExprId,
        ty: ExprId,
    },
    /// oracle: `elabBinderViews`' "invalid binder annotation, type is not a
    /// class instance" (`Elab/Binders.lean:218`). Carries the binder's
    /// elaborated type. Raised for `forall`, `depArrow` and `let`/`have`'s
    /// own instance binders — never for `fun`, whose `elabFunBinderViews`
    /// runs no check. `set_option checkBinderAnnotations false` is not
    /// modelled (leanr has no options; the check always runs, the
    /// oracle's default).
    InvalidBinderAnnotation {
        ty: ExprId,
    },
    /// oracle: `checkLocalInstanceParameters`' "invalid parametric local
    /// instance, parameter with type … does not have forward dependencies"
    /// (`Elab/Binders.lean:205`). Carries the offending parameter's type.
    InvalidParametricLocalInstance {
        param_ty: ExprId,
    },
    /// oracle: `elabNumLit`'s two `getDecLevel` failure branches
    /// (`BuiltinTerm.lean:219-223`) — "numerals are data in Lean, but
    /// the expected type is a proposition" and "…is universe
    /// polymorphic and may be a proposition". Two distinct oracle
    /// errors, kept distinct by `is_prop` rather than collapsed: they
    /// say different things about what the user must change.
    NumeralIsNotData {
        expected: ExprId,
        is_prop: bool,
    },
    /// A literal TOKEN that leanr's lexer accepted but the oracle's own
    /// decoder rejects (`12a`, `0z1`, `0_1`). Distinct from
    /// `IllFormedSyntax`, which is about tree SHAPE. The decoders are
    /// arbitrary-precision, so a literal is never too WIDE to accept —
    /// only malformed.
    IllFormedLiteral(String),
    /// oracle: `resolveLValAux`'s `fieldIdx` throws (`App.lean:1520-1551`,
    /// `:1589-1591`, `:1601-1603`, `:1613-1616`) and `mkProjAndCheck`'s
    /// `lean.projNonPropFromProp` (`:65-73`). Prose deferred (design spec
    /// § Errors); `reason` identifies the throw site.
    InvalidProjection {
        e: ExprId,
        e_type: ExprId,
        reason: InvalidProjectionReason,
    },
    /// oracle: `resolveLValAux`'s `fieldName` throws (`App.lean:1578`,
    /// `:1588`, `:1593-1600`, `:1609-1612`; the message itself is the
    /// `throwInvalidFieldAt` helper, `:1619-1654`).
    InvalidField {
        e: ExprId,
        e_type: ExprId,
        field: String,
        reason: InvalidFieldReason,
    },
    /// oracle: `addLValArg.throwUnusableParameter` (`App.lean:1811-1829`,
    /// thrown at `:1772`): a parameter of the base type exists but can be
    /// passed neither positionally nor by name. `allow_named` is false
    /// once a `CoeFun` coercion has disabled named insertion (`:1785`).
    /// `f` is the function the user named (`fPreCoercion?.getD f`): the
    /// oracle's `funMsg` (`:1796-1809`) mentions both it and the coerced
    /// function, but its prose is deferred (design spec § Errors) and
    /// the head the user wrote is the one worth carrying.
    UnusableLValParameter {
        f: ExprId,
        param: String,
        allow_named: bool,
    },
    /// oracle: `addLValArg`'s final throw (`App.lean:1792-1794`): "Function
    /// … does not have a usable parameter of type `base` …". `f` as for
    /// `UnusableLValParameter`: the function the user named, before any
    /// `CoeFun` coercion.
    NoLValParameter {
        f: ExprId,
        base: String,
    },
    /// oracle: `throwMaxRecDepthAt` (`Exception.lean:225-226`), reached
    /// from `withIncRecDepth` (`:245-249`). Built as an `.error` (tagged
    /// `runtime.maxRecDepth`), but a runtime exception
    /// (`Exception.isRuntime`, `CoreM.lean:783-784`) that `Core.tryCatch`
    /// (`:792-799`) rethrows before any elaborator `catch` arm runs, so
    /// no catch site handles it ([`ElabError::is_oracle_error`] is
    /// `false`). leanr
    /// counts only the recursions that can run away on their own
    /// (`addLValArg.go`, `App.lean:1749`, and the anonymous-constructor
    /// flatten tail, `elab.rs`'s `dispatch_target` / `anon_tail_depth`)
    /// against the oracle's
    /// `defaultMaxRecDepth` (512, `Init/Prelude.lean:4836`); the oracle
    /// counts from the ambient depth, so the exact cut-off differs,
    /// never whether one exists.
    MaxRecDepth,
    /// oracle: `elabAppFn`'s `` `(_) `` arm (`App.lean:2119`): "A
    /// placeholder `_` cannot be used where a function is expected".
    PlaceholderAsFunction,
    /// oracle: `throwInvalidExplicitUniversesForLocal`
    /// (`TermElabM.lean:2160-2161`), from `resolveName`'s `processLocal`
    /// (`:2172-2179`): explicit universes on an identifier that resolves
    /// to a local with no fields left over, e.g. `x.{0}`. With fields
    /// (`x.val.{0}`) the levels belong to the last field instead.
    InvalidExplicitUniversesForLocal(ExprId),
    /// A named pattern `x@p` outside a pattern. Two oracle throw sites,
    /// both measured: `elabNamedPatternErr` (`BuiltinTerm.lean:443-444`)
    /// answers for a whole term (`as_function: false`), and `elabAppFn`'s
    /// arm (`App.lean:2098-2100`) for an application head
    /// (`as_function: true`).
    NamedPatternOutsidePattern {
        as_function: bool,
    },
    /// oracle: `resolveDottedIdentFn`'s throws (`App.lean:1985-2058`);
    /// `id` is the identifier after the dot, as written. Prose deferred
    /// (design spec § Errors).
    InvalidDottedIdent {
        id: String,
        reason: InvalidDottedIdentReason,
    },
    /// oracle: `elabAnonymousCtor`'s throws
    /// (`Lean/Elab/BuiltinNotation.lean:43-102`). Prose deferred (design
    /// spec 2026-09-30-m4b4b § Errors).
    InvalidAnonymousCtor(AnonCtorError),
    /// oracle: the eliminator elaborator's throws — `getElabElimExprInfo`
    /// (`App.lean:1006-1050`) from M4b-4c P1; `ElabElim` (`:1140-1319`)
    /// from P2. Prose deferred; `oracle_first_line` is what the oracle
    /// gate compares.
    Eliminator {
        reason: EliminatorErrorReason,
    },
    /// An oracle `panic!`/`unreachable!` site (`mkBaseProjections`,
    /// `App.lean:1703`, `:1708`): unreachable on a well-formed
    /// environment, an error rather than a panic here because `.olean`
    /// input is untrusted.
    Internal(String),
    /// oracle: `Exception.internal postponeExceptionId`
    /// (`Elab/Exception.lean:15`, thrown by `throwPostpone`, `:22-23`) —
    /// "not ready yet: retry once more is known". An internal exception,
    /// never a user-facing error. Raised only while `may_postpone` holds,
    /// by the `try_postpone` family (`postpone.rs`) and `elab.rs`'s
    /// `useImplicitLambda` `.postpone` arm.
    ///
    /// Caught in exactly two places: `elab.rs`'s `elab_using_elab_fns`
    /// (`elabUsingElabFnsAux`, `TermElabM.lean:1615-1661`) and
    /// `synthetic/ladder.rs`'s `resume_postponed`
    /// (`SyntheticMVars.lean:62-65`). A catch site that retries or
    /// swallows ERRORS must let it through: see
    /// [`ElabError::is_oracle_error`], used by `app/lval.rs`'s
    /// `resolve_lval_loop` (`App.lean:1688-1694`) and `resume_postponed`.
    /// `commit_when` restores and rethrows every `Err`;
    /// `with_synthesize_impl` rethrows every `Err` after merging the
    /// caller's pending mvars back (its `finally`, no state restore) —
    /// the oracle's treatment of it too.
    Postpone,
}

impl ElabError {
    /// Whether this error stands for an oracle `Exception.error` — the
    /// kind a `catch | ex@(.error ..)` arm handles (retries, swallows,
    /// or postpones on). `false` for the oracle's `.internal` exceptions
    /// (`Postpone` is `postponeExceptionId`) and for leanr's own
    /// failures that have no oracle `.error` counterpart: a named seam
    /// (`UnsupportedSyntax`, "this path was never run") and
    /// `Meta`/`Internal` (budget and internal failures). Handling one of
    /// those as an oracle error would report an outcome for a path leanr
    /// never ran, so every such catch rethrows them.
    ///
    /// Also `false` for the oracle's runtime exceptions (`MaxRecDepth`):
    /// `Exception.isRuntime` (`CoreM.lean:783-784`) exceptions are an
    /// `.error` by construction, but `Core.tryCatch` (`:792-799`)
    /// rethrows them before any `catch` arm runs, so no catch site may
    /// handle them.
    pub fn is_oracle_error(&self) -> bool {
        !matches!(
            self,
            ElabError::UnsupportedSyntax(_)
                | ElabError::Meta(_)
                | ElabError::Internal(_)
                | ElabError::Postpone
                | ElabError::MaxRecDepth
        )
    }
}

/// Which `resolveLValAux` / `mkProjAndCheck` throw an
/// `ElabError::InvalidProjection` stands for.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InvalidProjectionReason {
    /// `App.lean:1520-1521` — "Index must be greater than 0". Unreachable
    /// from source: the `fieldIdx` token rejects `0`, so `(o).0` is a
    /// parse error in both implementations.
    IndexZero,
    /// `App.lean:1546-1551` — "Index `idx` is invalid for this structure".
    IndexOutOfRange { idx: usize, num_fields: usize },
    /// `App.lean:1542-1545` — a one-constructor type with no fields.
    NoFields,
    /// `App.lean:1523-1527` — `matchConstStructure`'s `failK`: not a
    /// one-constructor inductive type.
    NotOneCtor,
    /// `App.lean:1589-1591` — "Projections cannot be used on functions".
    OnFunction,
    /// `App.lean:1601-1603` — "Type of … is not known".
    TypeUnknown,
    /// `App.lean:1613-1616` — "Projection operates on types of the form
    /// `C ...`".
    NotConstApp,
    /// `App.lean:1536-1539` — explicit universes on a projection of an
    /// `inductive` (not `structure`) type.
    ExplicitUnivsOnInductive,
    /// `App.lean:68-72` — `lean.projNonPropFromProp`.
    NonPropFromProp,
}

/// Which `resolveLValAux` throw an `ElabError::InvalidField` stands for.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InvalidFieldReason {
    /// `App.lean:1578`, `:1588` (`throwInvalidFieldAt`) — "The environment
    /// does not contain `full_name`".
    NotFound { full_name: String },
    /// `App.lean:1593-1600` — "Type of … is not known; cannot resolve field".
    TypeUnknown,
    /// `App.lean:1609-1612` — "Field projection operates on types of the
    /// form `C ...`".
    NotConstApp,
}

/// Which `resolveDottedIdentFn` throw an `ElabError::InvalidDottedIdent`
/// stands for.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum InvalidDottedIdentReason {
    /// `App.lean:1986-1987` — "The name `id` must be atomic".
    NotAtomic,
    /// `throwNoExpectedType` (`App.lean:1997-2007`), thrown with no
    /// expected type (`:1989-1990`) or with an mvar-headed one (`:2044-2045`).
    NoExpectedType,
    /// `App.lean:2041-2042` — "Not supported on type universe".
    Sort,
    /// `App.lean:2046-2048` — "is not of the form `C ...` or `... → C ...`".
    NotConstApp,
    /// `App.lean:2038-2040` — `throwUnknownIdentifierAt` "Unknown constant
    /// `full_name`", the last one tried after every `unfoldDefinition?` step.
    UnknownConstant { full_name: String },
}

/// Which eliminator-elaborator throw an `ElabError::Eliminator` stands
/// for. Line citations are `Lean/Elab/App.lean`, v4.33.0-rc1.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EliminatorErrorReason {
    /// `App.lean:1012-1013`: the telescope's body is not an application
    /// of a telescope fvar to at least one argument.
    UnexpectedResultingType,
    /// `App.lean:1016-1017`.
    UnexpectedMotiveArity,
    /// `App.lean:1018-1019`.
    MotiveResultNotSort,
    /// `App.lean:1020-1021`: the motive is an fvar bound outside the
    /// eliminator's own telescope. Unreachable from `get_elab_elim_info`
    /// (a constant's type is closed); reachable from
    /// `get_elab_elim_expr_info` on an expression whose type mentions an
    /// ambient local.
    UnexpectedEliminatorType,
    /// `App.lean:1376`, `:1378`: no expected type, or an mvar-headed one.
    NoExpectedType,
    /// `App.lean:1199-1200`: `finalize` reached with no motive yet (an
    /// explicit binder before the motive ran out of positionals).
    InsufficientArgs,
    /// `App.lean:1207`: as `InsufficientArgs`, expected type on later lines.
    InsufficientArgsExpectedType,
    /// `App.lean:1197-1198`: named arguments no binder consumed.
    UnusedNamedArgs(Vec<String>),
    /// `App.lean:1224`: after generalizing over-applied arguments the
    /// expected type is type incorrect (type on later lines).
    OverAppTypeIncorrect,
    /// `App.lean:1234`: the synthesized motive is not type correct.
    MotiveNotTypeCorrect,
    /// `App.lean:1236`: the synthesized motive is invalid.
    InvalidMotive,
    /// `App.lean:1229`: a target type that is not an application of the
    /// motive.
    MotiveNotHead,
}

impl EliminatorErrorReason {
    /// The first line of the oracle's `throwError` text.
    pub fn oracle_first_line(&self) -> String {
        let p = "failed to elaborate eliminator, ";
        match self {
            Self::UnexpectedResultingType => "unexpected eliminator resulting type".to_string(),
            Self::UnexpectedMotiveArity => {
                "unexpected number of arguments at motive type".to_string()
            }
            Self::MotiveResultNotSort => "motive result type must be a sort".to_string(),
            Self::UnexpectedEliminatorType => "unexpected eliminator type".to_string(),
            Self::NoExpectedType => format!("{p}expected type is not available"),
            Self::InsufficientArgs => format!("{p}insufficient number of arguments"),
            Self::InsufficientArgsExpectedType => {
                format!("{p}insufficient number of arguments, expected type:")
            }
            Self::UnusedNamedArgs(names) => {
                format!("{p}unused named arguments: [{}]", names.join(", "))
            }
            Self::OverAppTypeIncorrect => format!(
                "{p}after generalizing over-applied arguments, expected type is type incorrect:"
            ),
            Self::MotiveNotTypeCorrect => format!("{p}motive is not type correct:"),
            Self::InvalidMotive => format!("{p}invalid motive"),
            Self::MotiveNotHead => {
                "Internal error, eliminator target type isn't an application of the motive"
                    .to_string()
            }
        }
    }
}

impl ElabError {
    /// The oracle's first error line, for the variants the corpus gate
    /// compares (`Eliminator`); `None` for every other variant.
    pub fn oracle_first_line(&self) -> Option<String> {
        match self {
            Self::Eliminator { reason } => Some(reason.oracle_first_line()),
            Self::UnknownConstant(n) => Some(format!("Unknown constant `{n}`")),
            _ => None,
        }
    }
}

/// Which `elabAnonymousCtor` throw an `ElabError::InvalidAnonymousCtor`
/// stands for. `ctor` is the constructor's rendered name.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AnonCtorError {
    /// `BuiltinNotation.lean:47-48`, thrown at `:54` (an mvar head after
    /// `whnf`) and `:101` (no expected type).
    ExpectedTypeUnknown,
    /// `:56-57` — `matchConstInduct`'s failure continuation.
    NotInductive { ty: ExprId },
    /// `:98`.
    NoCtors { ty: ExprId },
    /// `:99-100`.
    MultipleCtors { ty: ExprId },
    /// `:77-82`. The oracle logs this under `errToSorry` and pads with
    /// labeled `sorry`s; leanr has no `errToSorry` and throws.
    InsufficientFields {
        ctor: String,
        explicit: usize,
        provided: usize,
    },
    /// `:89-91`.
    NoExplicitFields { ctor: String, provided: usize },
}

impl From<MetaError> for ElabError {
    fn from(e: MetaError) -> Self {
        ElabError::Meta(e)
    }
}

/// oracle: `defaultMaxRecDepth` (512, `Init/Prelude.lean:4836`), the
/// limit `withIncRecDepth` checks. leanr counts only the recursions that
/// can run away on their own (see [`ElabError::MaxRecDepth`]).
pub(crate) const MAX_REC_DEPTH: usize = 512;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn unknown_constant_first_line_is_the_oracles() {
        // oracle: `throwUnknownConstantAt` (probed 2026-10-02 against
        // ElabOp: `binop% NoSuch a b` -> "Unknown constant `NoSuch`").
        assert_eq!(
            ElabError::UnknownConstant("NoSuch".into())
                .oracle_first_line()
                .as_deref(),
            Some("Unknown constant `NoSuch`")
        );
    }

    #[test]
    fn eliminator_first_lines_are_the_oracles() {
        use EliminatorErrorReason as R;
        assert_eq!(
            R::UnusedNamedArgs(vec!["foo".into(), "bar".into()]).oracle_first_line(),
            "failed to elaborate eliminator, unused named arguments: [foo, bar]"
        );
        assert_eq!(
            ElabError::Eliminator {
                reason: R::InvalidMotive
            }
            .oracle_first_line()
            .as_deref(),
            Some("failed to elaborate eliminator, invalid motive")
        );
        assert_eq!(ElabError::Postpone.oracle_first_line(), None);
    }
}
