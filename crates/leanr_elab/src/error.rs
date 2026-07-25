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
}

impl From<MetaError> for ElabError {
    fn from(e: MetaError) -> Self {
        ElabError::Meta(e)
    }
}
