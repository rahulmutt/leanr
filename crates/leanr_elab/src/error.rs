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
    /// ensureHasType mismatch. In slice 1 this errors; coercion
    /// insertion (mkCoe) is M4b-3.
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
}

impl From<MetaError> for ElabError {
    fn from(e: MetaError) -> Self {
        ElabError::Meta(e)
    }
}
