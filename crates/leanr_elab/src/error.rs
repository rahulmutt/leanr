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
    /// '{constName}'" (`Lean/Elab/Term/TermElabM.lean:2117-2126`).
    /// Carries the head identifier's raw source text. Reachable only
    /// once `.{u, v}` explicit-universe syntax has a producer (M4b-3 P1
    /// task 8); the check itself lives in `app::head::elab_ident_head`
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
    /// (`TermElabM.lean:1946-1949`). Raised from `binder.rs`'s
    /// `elab_type` since M4b-3 P4; before that a non-type domain was
    /// (wrongly) a value-level `TypeMismatch` against `Sort ?u`.
    TypeExpected {
        e: ExprId,
        ty: ExprId,
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
}

impl From<MetaError> for ElabError {
    fn from(e: MetaError) -> Self {
        ElabError::Meta(e)
    }
}
