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
}

impl From<MetaError> for ElabError {
    fn from(e: MetaError) -> Self {
        ElabError::Meta(e)
    }
}
