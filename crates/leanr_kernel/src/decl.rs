//! Constant declarations as the kernel sees them (oracle:
//! src/Lean/Declaration.lean; per-type line cites below). Field names
//! and order mirror the oracle so the decoder and future checker read
//! like the original.

use std::sync::Arc;

use crate::{Expr, Name, Nat};

/// oracle: Declaration.lean:95-99
#[derive(Debug, Clone)]
pub struct ConstantVal {
    pub name: Arc<Name>,
    pub level_params: Vec<Arc<Name>>,
    pub ty: Arc<Expr>,
}

/// oracle: Declaration.lean:46-50
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ReducibilityHints {
    Opaque,
    Abbrev,
    Regular(u32),
}

/// oracle: Declaration.lean:116-118
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum DefinitionSafety {
    Unsafe,
    Safe,
    Partial,
}

/// oracle: Declaration.lean:410-415
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum QuotKind {
    Type,
    Ctor,
    Lift,
    Ind,
}

/// oracle: Declaration.lean:101-103
#[derive(Debug, Clone)]
pub struct AxiomVal {
    pub val: ConstantVal,
    pub is_unsafe: bool,
}

/// oracle: Declaration.lean:120-133
#[derive(Debug, Clone)]
pub struct DefinitionVal {
    pub val: ConstantVal,
    pub value: Arc<Expr>,
    pub hints: ReducibilityHints,
    pub safety: DefinitionSafety,
    pub all: Vec<Arc<Name>>,
}

/// oracle: Declaration.lean:142-146
#[derive(Debug, Clone)]
pub struct TheoremVal {
    pub val: ConstantVal,
    pub value: Arc<Expr>,
    pub all: Vec<Arc<Name>>,
}

/// oracle: Declaration.lean:156-160
#[derive(Debug, Clone)]
pub struct OpaqueVal {
    pub val: ConstantVal,
    pub value: Arc<Expr>,
    pub is_unsafe: bool,
    pub all: Vec<Arc<Name>>,
}

/// oracle: Declaration.lean:417-421
#[derive(Debug, Clone)]
pub struct QuotVal {
    pub val: ConstantVal,
    pub kind: QuotKind,
}

/// oracle: Declaration.lean:261-301
#[derive(Debug, Clone)]
pub struct InductiveVal {
    pub val: ConstantVal,
    pub num_params: Nat,
    pub num_indices: Nat,
    pub all: Vec<Arc<Name>>,
    pub ctors: Vec<Arc<Name>>,
    pub num_nested: Nat,
    pub is_rec: bool,
    pub is_unsafe: bool,
    pub is_reflexive: bool,
}

/// oracle: Declaration.lean:328-334
#[derive(Debug, Clone)]
pub struct ConstructorVal {
    pub val: ConstantVal,
    pub induct: Arc<Name>,
    pub cidx: Nat,
    pub num_params: Nat,
    pub num_fields: Nat,
    pub is_unsafe: bool,
}

/// oracle: Declaration.lean:348-356
#[derive(Debug, Clone)]
pub struct RecursorRule {
    pub ctor: Arc<Name>,
    pub nfields: Nat,
    pub rhs: Arc<Expr>,
}

/// oracle: Declaration.lean:357-379
#[derive(Debug, Clone)]
pub struct RecursorVal {
    pub val: ConstantVal,
    pub all: Vec<Arc<Name>>,
    pub num_params: Nat,
    pub num_indices: Nat,
    pub num_motives: Nat,
    pub num_minors: Nat,
    pub rules: Vec<RecursorRule>,
    pub k: bool,
    pub is_unsafe: bool,
}

/// oracle: Declaration.lean:429-437; variant order is the on-disk ctor
/// tag order, do not reorder.
#[derive(Debug, Clone)]
pub enum ConstantInfo {
    Axiom(AxiomVal),
    Defn(DefinitionVal),
    Thm(TheoremVal),
    Opaque(OpaqueVal),
    Quot(QuotVal),
    Induct(InductiveVal),
    Ctor(ConstructorVal),
    Rec(RecursorVal),
}

/// Kernel admission INPUT (oracle declaration.h:201; Lean `Declaration`).
/// No `MutualDefinition` variant: replay skips unsafe/partial constants
/// (Replay.lean:176-181), which are the only legal mutual defs
/// (environment.cpp:224-232), so the variant is unreachable for us.
#[derive(Debug, Clone)]
pub enum Declaration {
    Axiom(AxiomVal),
    Defn(DefinitionVal),
    Thm(TheoremVal),
    Opaque(OpaqueVal),
    Quot,
    /// oracle: inductive_decl (declaration.h:266+): the mutual block's
    /// level params, num params, and per-type name/type/ctors.
    Inductive {
        lparams: Vec<Arc<Name>>,
        nparams: Nat,
        types: Vec<InductiveType>,
        is_unsafe: bool, // always false from replay
    },
}

#[derive(Debug, Clone)]
pub struct InductiveType {
    pub name: Arc<Name>,
    pub ty: Arc<Expr>,
    pub ctors: Vec<(Arc<Name>, Arc<Expr>)>, // (ctor name, ctor type)
}

impl ConstantInfo {
    pub fn constant_val(&self) -> &ConstantVal {
        match self {
            ConstantInfo::Axiom(v) => &v.val,
            ConstantInfo::Defn(v) => &v.val,
            ConstantInfo::Thm(v) => &v.val,
            ConstantInfo::Opaque(v) => &v.val,
            ConstantInfo::Quot(v) => &v.val,
            ConstantInfo::Induct(v) => &v.val,
            ConstantInfo::Ctor(v) => &v.val,
            ConstantInfo::Rec(v) => &v.val,
        }
    }

    pub fn name(&self) -> &Arc<Name> {
        &self.constant_val().name
    }

    /// One-word kind label. Must stay byte-identical to `kindStr` in
    /// tests/fixtures/dump_decls.lean — the golden decls fixtures
    /// compare these strings against the oracle's output.
    pub fn kind(&self) -> &'static str {
        match self {
            ConstantInfo::Axiom(_) => "axiom",
            ConstantInfo::Defn(_) => "def",
            ConstantInfo::Thm(_) => "thm",
            ConstantInfo::Opaque(_) => "opaque",
            ConstantInfo::Quot(_) => "quot",
            ConstantInfo::Induct(_) => "induct",
            ConstantInfo::Ctor(_) => "ctor",
            ConstantInfo::Rec(_) => "rec",
        }
    }
}
