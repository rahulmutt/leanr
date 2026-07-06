use std::sync::Arc;

use crate::Name;

/// Every failure the kernel can report. Untrusted input maps to `Err`,
/// never a panic (docs/THREAT_MODEL.md). Variants carry the declaration
/// being admitted where known; the CLI adds module context.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum KernelError {
    /// The term bank's 2³¹-per-region id space (or a side pool) is
    /// exhausted. Ids are minted once per *distinct* interned row, so
    /// reaching this bound requires input of comparable size —
    /// rejection is incompleteness on absurd input, never unsoundness
    /// (same posture as `DeepRecursion`).
    BankExhausted,
    /// Recursion guard cap (guard.rs). Rejection here is incompleteness,
    /// never unsoundness: we refuse, we never accept unchecked.
    DeepRecursion,
    UnknownConstant(Arc<Name>),
    /// oracle: environment.cpp:102 (already_declared_exception)
    AlreadyDeclared(Arc<Name>),
    /// oracle: environment.cpp:111 (duplicate universe level parameter)
    DuplicateUnivParam(Arc<Name>),
    /// oracle: environment.cpp:87 (declaration_has_metavars_exception)
    HasMetavars(Arc<Name>),
    /// oracle: environment.cpp:92 (declaration_has_free_vars_exception)
    HasFVars(Arc<Name>),
    /// oracle: type_checker.cpp:98 (incorrect number of universe levels)
    UnivParamArityMismatch {
        name: Arc<Name>,
    },
    /// oracle: type_checker.cpp:104-113 (unsafe const in safe decl)
    UnsafeConstInSafeDecl(Arc<Name>),
    /// ensure_sort failed (type_checker.cpp:53) — "type expected"
    TypeExpected,
    /// ensure_pi failed (type_checker.cpp:65) — "function expected"
    FunctionExpected,
    /// oracle: type_checker.cpp:163-197 (app_type_mismatch)
    AppTypeMismatch,
    /// oracle: type_checker.cpp:198-220 (invalid let, type mismatch)
    LetTypeMismatch,
    /// oracle: type_checker.cpp:221-268 (invalid projection)
    InvalidProj,
    /// A loose bound variable escaped (infer_type on BVar is a kernel
    /// invariant violation for *closed* input, but attacker input can
    /// contain loose bvars — reject, don't assert).
    LooseBVar,
    /// Level/expr metavariable reached the checker (spec: the checker
    /// rejects mvars, the decoder does not).
    MetavarEncountered,
    /// oracle: environment.cpp:176/185 (definition_type_mismatch_exception)
    DefTypeMismatch(Arc<Name>),
    /// oracle: environment.cpp:201 (theorem_type_is_not_prop)
    TheoremTypeNotProp(Arc<Name>),
    /// inductive.cpp violations; `what` is a short static reason like
    /// "positivity", "invalid occurrence", "universe too small".
    InvalidInductive {
        name: Arc<Name>,
        what: &'static str,
    },
    /// quot.cpp:19-45 — environment lacks the expected `Eq`.
    InvalidQuot {
        what: &'static str,
    },
    /// Replay: postponed ctor/recursor not structurally equal to the
    /// regenerated one (Replay.lean:149-164).
    ConstructorMismatch(Arc<Name>),
    RecursorMismatch(Arc<Name>),
    /// Replay: name in a ConstantInfo cross-reference missing from the
    /// module set (Replay.lean uses `unreachable!`; untrusted input
    /// makes it a real error for us).
    MissingConstant(Arc<Name>),
}

impl std::fmt::Display for KernelError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            KernelError::BankExhausted => write!(f, "term bank id space exhausted"),
            KernelError::DeepRecursion => write!(f, "maximum recursion depth exceeded"),
            KernelError::UnknownConstant(n) => write!(f, "unknown constant '{n}'"),
            KernelError::AlreadyDeclared(n) => write!(f, "'{n}' has already been declared"),
            KernelError::DuplicateUnivParam(n) => write!(f, "duplicate universe parameter '{n}'"),
            KernelError::HasMetavars(n) => write!(f, "declaration '{n}' contains metavariables"),
            KernelError::HasFVars(n) => write!(f, "declaration '{n}' contains free variables"),
            KernelError::UnivParamArityMismatch { name } => {
                write!(f, "incorrect number of universe levels at '{name}'")
            }
            KernelError::UnsafeConstInSafeDecl(n) => {
                write!(
                    f,
                    "invalid declaration, unsafe constant '{n}' used in safe declaration"
                )
            }
            KernelError::TypeExpected => write!(f, "type expected"),
            KernelError::FunctionExpected => write!(f, "function expected"),
            KernelError::AppTypeMismatch => write!(f, "application type mismatch"),
            KernelError::LetTypeMismatch => write!(f, "invalid let declaration, type mismatch"),
            KernelError::InvalidProj => write!(f, "invalid projection"),
            KernelError::LooseBVar => write!(f, "loose bound variable"),
            KernelError::MetavarEncountered => write!(f, "declaration contains metavariables"),
            KernelError::DefTypeMismatch(n) => write!(f, "definition type mismatch at '{n}'"),
            KernelError::TheoremTypeNotProp(n) => {
                write!(f, "theorem type of '{n}' is not a proposition")
            }
            KernelError::InvalidInductive { name, what } => {
                write!(f, "invalid inductive '{name}': {what}")
            }
            KernelError::InvalidQuot { what } => write!(f, "invalid quotient init: {what}"),
            KernelError::ConstructorMismatch(n) => write!(f, "invalid constructor '{n}'"),
            KernelError::RecursorMismatch(n) => write!(f, "invalid recursor '{n}'"),
            KernelError::MissingConstant(n) => write!(f, "constant '{n}' missing from module set"),
        }
    }
}

impl std::error::Error for KernelError {}
