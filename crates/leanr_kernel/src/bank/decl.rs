//! Id-twin constant declarations — the bank-native counterpart of
//! `crate::decl` (oracle: src/Lean/Declaration.lean; per-type line
//! cites below). Field names and order mirror `decl.rs`/the oracle so
//! the two representations read side-by-side; `Arc<Name>`/`Arc<Expr>`
//! become `NameId`/`ExprId` via the phase-1 bank (spec:
//! docs/superpowers/specs/2026-07-06-compact-expr-term-bank-design.md).
//! Porting is representation-only: no algorithmic change from
//! `decl.rs`.
//!
//! Declaration-position names (`ConstantVal.name`, level-param names,
//! `induct`, `ctor`, inductive/constructor names, `lparams`) are never
//! `Name::Anonymous` in legitimate data (Lean's own grammar never
//! permits an anonymous identifier there), so they bridge to a plain
//! `NameId` rather than `Option<NameId>` (matching this module's
//! interface). This bridge does not *assert* that invariant, though:
//! `Store::intern_name` maps `Name::Anonymous` to `None` (bank/names.rs
//! — there is no real row for it), and on that input `intern_name_req`
//! below reports `KernelError::BankExhausted` (an honest `Err`, never a
//! panic — the same "reject, don't assert" posture as everywhere else
//! in this crate) instead of fabricating a `NameId`. An anonymous name
//! embedded *inside* an expression tree (e.g. `Sort (Param
//! Name.anonymous)`) is a different, already-supported path: it flows
//! through `Store::intern_expr`/`intern_level`, which use
//! `Option<NameId>` throughout and round-trip `Name::Anonymous`
//! unchanged (see `constant_info_round_trip_with_anonymous_name_in_type`
//! below).

use std::sync::Arc;

use super::{ExprId, NameId, Store};
use crate::{
    AxiomVal as ArcAxiomVal, ConstantInfo as ArcConstantInfo, ConstantVal as ArcConstantVal,
    ConstructorVal as ArcConstructorVal, Declaration as ArcDeclaration,
    DefinitionVal as ArcDefinitionVal, InductiveType as ArcInductiveType,
    InductiveVal as ArcInductiveVal, KernelError, Name, Nat, OpaqueVal as ArcOpaqueVal,
    QuotVal as ArcQuotVal, RecGuard, RecursorRule as ArcRecursorRule,
    RecursorVal as ArcRecursorVal, TheoremVal as ArcTheoremVal,
};

pub use crate::{DefinitionSafety, QuotKind, ReducibilityHints};

/// oracle: Declaration.lean:95-99
#[derive(Debug, Clone)]
pub struct ConstantVal {
    pub name: NameId,
    pub level_params: Vec<NameId>,
    pub ty: ExprId,
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
    pub value: ExprId,
    pub hints: ReducibilityHints,
    pub safety: DefinitionSafety,
    pub all: Vec<NameId>,
}

/// oracle: Declaration.lean:142-146
#[derive(Debug, Clone)]
pub struct TheoremVal {
    pub val: ConstantVal,
    pub value: ExprId,
    pub all: Vec<NameId>,
}

/// oracle: Declaration.lean:156-160
#[derive(Debug, Clone)]
pub struct OpaqueVal {
    pub val: ConstantVal,
    pub value: ExprId,
    pub is_unsafe: bool,
    pub all: Vec<NameId>,
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
    pub all: Vec<NameId>,
    pub ctors: Vec<NameId>,
    pub num_nested: Nat,
    pub is_rec: bool,
    pub is_unsafe: bool,
    pub is_reflexive: bool,
}

/// oracle: Declaration.lean:328-334
#[derive(Debug, Clone)]
pub struct ConstructorVal {
    pub val: ConstantVal,
    pub induct: NameId,
    pub cidx: Nat,
    pub num_params: Nat,
    pub num_fields: Nat,
    pub is_unsafe: bool,
}

/// oracle: Declaration.lean:348-356
#[derive(Debug, Clone)]
pub struct RecursorRule {
    pub ctor: NameId,
    pub nfields: Nat,
    pub rhs: ExprId,
}

/// oracle: Declaration.lean:357-379
#[derive(Debug, Clone)]
pub struct RecursorVal {
    pub val: ConstantVal,
    pub all: Vec<NameId>,
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
        lparams: Vec<NameId>,
        nparams: Nat,
        types: Vec<InductiveType>,
        is_unsafe: bool, // always false from replay
    },
}

#[derive(Debug, Clone)]
pub struct InductiveType {
    pub name: NameId,
    pub ty: ExprId,
    pub ctors: Vec<(NameId, ExprId)>, // (ctor name, ctor type)
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

    pub fn name(&self) -> NameId {
        self.constant_val().name
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

// ---- bridges: Arc -> id ---------------------------------------------

/// Intern a declaration-position name (never anonymous by the Lean
/// grammar this crate trusts, but not asserted here — see the
/// module-level doc comment). `Store::intern_name` maps
/// `Name::Anonymous` to `None`; that has no `NameId`, so it surfaces as
/// `KernelError::BankExhausted` rather than a fabricated id or a panic.
fn intern_name_req(
    st: &mut Store,
    base: Option<&Store>,
    n: &Arc<Name>,
) -> Result<NameId, KernelError> {
    st.intern_name(base, n)?.ok_or(KernelError::BankExhausted)
}

fn intern_name_vec(
    st: &mut Store,
    base: Option<&Store>,
    ns: &[Arc<Name>],
) -> Result<Vec<NameId>, KernelError> {
    ns.iter().map(|n| intern_name_req(st, base, n)).collect()
}

fn intern_constant_val(
    st: &mut Store,
    base: Option<&Store>,
    v: &ArcConstantVal,
) -> Result<ConstantVal, KernelError> {
    Ok(ConstantVal {
        name: intern_name_req(st, base, &v.name)?,
        level_params: intern_name_vec(st, base, &v.level_params)?,
        ty: st.intern_expr(base, &v.ty)?,
    })
}

fn intern_axiom_val(
    st: &mut Store,
    base: Option<&Store>,
    v: &ArcAxiomVal,
) -> Result<AxiomVal, KernelError> {
    Ok(AxiomVal {
        val: intern_constant_val(st, base, &v.val)?,
        is_unsafe: v.is_unsafe,
    })
}

fn intern_definition_val(
    st: &mut Store,
    base: Option<&Store>,
    v: &ArcDefinitionVal,
) -> Result<DefinitionVal, KernelError> {
    Ok(DefinitionVal {
        val: intern_constant_val(st, base, &v.val)?,
        value: st.intern_expr(base, &v.value)?,
        hints: v.hints,
        safety: v.safety,
        all: intern_name_vec(st, base, &v.all)?,
    })
}

fn intern_theorem_val(
    st: &mut Store,
    base: Option<&Store>,
    v: &ArcTheoremVal,
) -> Result<TheoremVal, KernelError> {
    Ok(TheoremVal {
        val: intern_constant_val(st, base, &v.val)?,
        value: st.intern_expr(base, &v.value)?,
        all: intern_name_vec(st, base, &v.all)?,
    })
}

fn intern_opaque_val(
    st: &mut Store,
    base: Option<&Store>,
    v: &ArcOpaqueVal,
) -> Result<OpaqueVal, KernelError> {
    Ok(OpaqueVal {
        val: intern_constant_val(st, base, &v.val)?,
        value: st.intern_expr(base, &v.value)?,
        is_unsafe: v.is_unsafe,
        all: intern_name_vec(st, base, &v.all)?,
    })
}

fn intern_quot_val(
    st: &mut Store,
    base: Option<&Store>,
    v: &ArcQuotVal,
) -> Result<QuotVal, KernelError> {
    Ok(QuotVal {
        val: intern_constant_val(st, base, &v.val)?,
        kind: v.kind,
    })
}

fn intern_inductive_val(
    st: &mut Store,
    base: Option<&Store>,
    v: &ArcInductiveVal,
) -> Result<InductiveVal, KernelError> {
    Ok(InductiveVal {
        val: intern_constant_val(st, base, &v.val)?,
        num_params: v.num_params.clone(),
        num_indices: v.num_indices.clone(),
        all: intern_name_vec(st, base, &v.all)?,
        ctors: intern_name_vec(st, base, &v.ctors)?,
        num_nested: v.num_nested.clone(),
        is_rec: v.is_rec,
        is_unsafe: v.is_unsafe,
        is_reflexive: v.is_reflexive,
    })
}

fn intern_constructor_val(
    st: &mut Store,
    base: Option<&Store>,
    v: &ArcConstructorVal,
) -> Result<ConstructorVal, KernelError> {
    Ok(ConstructorVal {
        val: intern_constant_val(st, base, &v.val)?,
        induct: intern_name_req(st, base, &v.induct)?,
        cidx: v.cidx.clone(),
        num_params: v.num_params.clone(),
        num_fields: v.num_fields.clone(),
        is_unsafe: v.is_unsafe,
    })
}

fn intern_recursor_rule(
    st: &mut Store,
    base: Option<&Store>,
    r: &ArcRecursorRule,
) -> Result<RecursorRule, KernelError> {
    Ok(RecursorRule {
        ctor: intern_name_req(st, base, &r.ctor)?,
        nfields: r.nfields.clone(),
        rhs: st.intern_expr(base, &r.rhs)?,
    })
}

fn intern_recursor_val(
    st: &mut Store,
    base: Option<&Store>,
    v: &ArcRecursorVal,
) -> Result<RecursorVal, KernelError> {
    Ok(RecursorVal {
        val: intern_constant_val(st, base, &v.val)?,
        all: intern_name_vec(st, base, &v.all)?,
        num_params: v.num_params.clone(),
        num_indices: v.num_indices.clone(),
        num_motives: v.num_motives.clone(),
        num_minors: v.num_minors.clone(),
        rules: v
            .rules
            .iter()
            .map(|r| intern_recursor_rule(st, base, r))
            .collect::<Result<Vec<_>, _>>()?,
        k: v.k,
        is_unsafe: v.is_unsafe,
    })
}

/// Bridge: intern an `Arc`-side `ConstantInfo` into the bank
/// (field-by-field; exprs delegate to `Store::intern_expr`, which is
/// already iterative).
pub fn intern_constant_info(
    st: &mut Store,
    base: Option<&Store>,
    ci: &ArcConstantInfo,
) -> Result<ConstantInfo, KernelError> {
    Ok(match ci {
        ArcConstantInfo::Axiom(v) => ConstantInfo::Axiom(intern_axiom_val(st, base, v)?),
        ArcConstantInfo::Defn(v) => ConstantInfo::Defn(intern_definition_val(st, base, v)?),
        ArcConstantInfo::Thm(v) => ConstantInfo::Thm(intern_theorem_val(st, base, v)?),
        ArcConstantInfo::Opaque(v) => ConstantInfo::Opaque(intern_opaque_val(st, base, v)?),
        ArcConstantInfo::Quot(v) => ConstantInfo::Quot(intern_quot_val(st, base, v)?),
        ArcConstantInfo::Induct(v) => ConstantInfo::Induct(intern_inductive_val(st, base, v)?),
        ArcConstantInfo::Ctor(v) => ConstantInfo::Ctor(intern_constructor_val(st, base, v)?),
        ArcConstantInfo::Rec(v) => ConstantInfo::Rec(intern_recursor_val(st, base, v)?),
    })
}

fn intern_inductive_type(
    st: &mut Store,
    base: Option<&Store>,
    t: &ArcInductiveType,
) -> Result<InductiveType, KernelError> {
    Ok(InductiveType {
        name: intern_name_req(st, base, &t.name)?,
        ty: st.intern_expr(base, &t.ty)?,
        ctors: t
            .ctors
            .iter()
            .map(|(n, ty)| Ok((intern_name_req(st, base, n)?, st.intern_expr(base, ty)?)))
            .collect::<Result<Vec<_>, KernelError>>()?,
    })
}

/// Bridge: intern an `Arc`-side `Declaration` (admission input) into
/// the bank.
pub fn intern_declaration(
    st: &mut Store,
    base: Option<&Store>,
    d: &ArcDeclaration,
) -> Result<Declaration, KernelError> {
    Ok(match d {
        ArcDeclaration::Axiom(v) => Declaration::Axiom(intern_axiom_val(st, base, v)?),
        ArcDeclaration::Defn(v) => Declaration::Defn(intern_definition_val(st, base, v)?),
        ArcDeclaration::Thm(v) => Declaration::Thm(intern_theorem_val(st, base, v)?),
        ArcDeclaration::Opaque(v) => Declaration::Opaque(intern_opaque_val(st, base, v)?),
        ArcDeclaration::Quot => Declaration::Quot,
        ArcDeclaration::Inductive {
            lparams,
            nparams,
            types,
            is_unsafe,
        } => Declaration::Inductive {
            lparams: intern_name_vec(st, base, lparams)?,
            nparams: nparams.clone(),
            types: types
                .iter()
                .map(|t| intern_inductive_type(st, base, t))
                .collect::<Result<Vec<_>, _>>()?,
            is_unsafe: *is_unsafe,
        },
    })
}

// ---- bridges: id -> Arc -----------------------------------------------

/// Rebuild a declaration-position name. Every id stored by this module
/// was produced by `intern_name_req`, which never stores the sentinel
/// for `Name::Anonymous` (it errors instead — see the module doc), so
/// this is always a real `Some(id)` lookup.
fn to_name_req(st: &Store, base: Option<&Store>, id: NameId) -> Arc<Name> {
    st.to_name(base, Some(id))
}

fn to_name_vec(st: &Store, base: Option<&Store>, ids: &[NameId]) -> Vec<Arc<Name>> {
    ids.iter().map(|&id| to_name_req(st, base, id)).collect()
}

fn to_constant_val(
    st: &Store,
    base: Option<&Store>,
    v: &ConstantVal,
    g: &mut RecGuard,
) -> Result<ArcConstantVal, KernelError> {
    Ok(ArcConstantVal {
        name: to_name_req(st, base, v.name),
        level_params: to_name_vec(st, base, &v.level_params),
        ty: st.to_expr(base, v.ty, g)?,
    })
}

fn to_axiom_val(
    st: &Store,
    base: Option<&Store>,
    v: &AxiomVal,
    g: &mut RecGuard,
) -> Result<ArcAxiomVal, KernelError> {
    Ok(ArcAxiomVal {
        val: to_constant_val(st, base, &v.val, g)?,
        is_unsafe: v.is_unsafe,
    })
}

fn to_definition_val(
    st: &Store,
    base: Option<&Store>,
    v: &DefinitionVal,
    g: &mut RecGuard,
) -> Result<ArcDefinitionVal, KernelError> {
    Ok(ArcDefinitionVal {
        val: to_constant_val(st, base, &v.val, g)?,
        value: st.to_expr(base, v.value, g)?,
        hints: v.hints,
        safety: v.safety,
        all: to_name_vec(st, base, &v.all),
    })
}

fn to_theorem_val(
    st: &Store,
    base: Option<&Store>,
    v: &TheoremVal,
    g: &mut RecGuard,
) -> Result<ArcTheoremVal, KernelError> {
    Ok(ArcTheoremVal {
        val: to_constant_val(st, base, &v.val, g)?,
        value: st.to_expr(base, v.value, g)?,
        all: to_name_vec(st, base, &v.all),
    })
}

fn to_opaque_val(
    st: &Store,
    base: Option<&Store>,
    v: &OpaqueVal,
    g: &mut RecGuard,
) -> Result<ArcOpaqueVal, KernelError> {
    Ok(ArcOpaqueVal {
        val: to_constant_val(st, base, &v.val, g)?,
        value: st.to_expr(base, v.value, g)?,
        is_unsafe: v.is_unsafe,
        all: to_name_vec(st, base, &v.all),
    })
}

fn to_quot_val(
    st: &Store,
    base: Option<&Store>,
    v: &QuotVal,
    g: &mut RecGuard,
) -> Result<ArcQuotVal, KernelError> {
    Ok(ArcQuotVal {
        val: to_constant_val(st, base, &v.val, g)?,
        kind: v.kind,
    })
}

fn to_inductive_val(
    st: &Store,
    base: Option<&Store>,
    v: &InductiveVal,
    g: &mut RecGuard,
) -> Result<ArcInductiveVal, KernelError> {
    Ok(ArcInductiveVal {
        val: to_constant_val(st, base, &v.val, g)?,
        num_params: v.num_params.clone(),
        num_indices: v.num_indices.clone(),
        all: to_name_vec(st, base, &v.all),
        ctors: to_name_vec(st, base, &v.ctors),
        num_nested: v.num_nested.clone(),
        is_rec: v.is_rec,
        is_unsafe: v.is_unsafe,
        is_reflexive: v.is_reflexive,
    })
}

fn to_constructor_val(
    st: &Store,
    base: Option<&Store>,
    v: &ConstructorVal,
    g: &mut RecGuard,
) -> Result<ArcConstructorVal, KernelError> {
    Ok(ArcConstructorVal {
        val: to_constant_val(st, base, &v.val, g)?,
        induct: to_name_req(st, base, v.induct),
        cidx: v.cidx.clone(),
        num_params: v.num_params.clone(),
        num_fields: v.num_fields.clone(),
        is_unsafe: v.is_unsafe,
    })
}

fn to_recursor_rule(
    st: &Store,
    base: Option<&Store>,
    r: &RecursorRule,
    g: &mut RecGuard,
) -> Result<ArcRecursorRule, KernelError> {
    Ok(ArcRecursorRule {
        ctor: to_name_req(st, base, r.ctor),
        nfields: r.nfields.clone(),
        rhs: st.to_expr(base, r.rhs, g)?,
    })
}

fn to_recursor_val(
    st: &Store,
    base: Option<&Store>,
    v: &RecursorVal,
    g: &mut RecGuard,
) -> Result<ArcRecursorVal, KernelError> {
    Ok(ArcRecursorVal {
        val: to_constant_val(st, base, &v.val, g)?,
        all: to_name_vec(st, base, &v.all),
        num_params: v.num_params.clone(),
        num_indices: v.num_indices.clone(),
        num_motives: v.num_motives.clone(),
        num_minors: v.num_minors.clone(),
        rules: v
            .rules
            .iter()
            .map(|r| to_recursor_rule(st, base, r, g))
            .collect::<Result<Vec<_>, _>>()?,
        k: v.k,
        is_unsafe: v.is_unsafe,
    })
}

/// Bridge: rebuild an `Arc`-side `ConstantInfo` from its id-twin
/// (field-by-field; exprs delegate to `Store::to_expr`, which is
/// already iterative and needs the caller's `RecGuard`).
pub fn to_constant_info(
    st: &Store,
    base: Option<&Store>,
    ci: &ConstantInfo,
    g: &mut RecGuard,
) -> Result<ArcConstantInfo, KernelError> {
    Ok(match ci {
        ConstantInfo::Axiom(v) => ArcConstantInfo::Axiom(to_axiom_val(st, base, v, g)?),
        ConstantInfo::Defn(v) => ArcConstantInfo::Defn(to_definition_val(st, base, v, g)?),
        ConstantInfo::Thm(v) => ArcConstantInfo::Thm(to_theorem_val(st, base, v, g)?),
        ConstantInfo::Opaque(v) => ArcConstantInfo::Opaque(to_opaque_val(st, base, v, g)?),
        ConstantInfo::Quot(v) => ArcConstantInfo::Quot(to_quot_val(st, base, v, g)?),
        ConstantInfo::Induct(v) => ArcConstantInfo::Induct(to_inductive_val(st, base, v, g)?),
        ConstantInfo::Ctor(v) => ArcConstantInfo::Ctor(to_constructor_val(st, base, v, g)?),
        ConstantInfo::Rec(v) => ArcConstantInfo::Rec(to_recursor_val(st, base, v, g)?),
    })
}

// ---- id/scalar structural equality -----------------------------------

/// `ConstantVal` id/scalar equality: `name` and `level_params` are
/// plain `NameId`/`Vec<NameId>` equality (the interning invariant makes
/// this structural), `ty` is plain `ExprId` equality for the same
/// reason.
fn constant_val_eq(a: &ConstantVal, b: &ConstantVal) -> bool {
    a.name == b.name && a.level_params == b.level_params && a.ty == b.ty
}

/// Structural equality over EVERY field of `ConstantInfo`, id/scalar
/// comparisons only (oracle: Lean's derived `BEq ConstantInfo` compares
/// all fields of all 8 kinds — this is the id-twin of `crate::decl`'s
/// `constant_info_eq`, a line-for-line field enumeration of that
/// function). Unlike the Arc version, this one takes neither a
/// `RecGuard` nor returns a `Result`: by the interning invariant, id
/// equality on `NameId`/`ExprId`/`Vec<NameId>` fields already IS the
/// guarded structural walk the Arc version performs explicitly — two
/// ids compare equal iff the trees they name are structurally equal,
/// and comparing them is O(1)/O(len), never proportional to tree depth,
/// so there is nothing left for a guard to bound. Field coverage below
/// must stay complete — Task 12's replay uses this to compare a
/// postponed constructor/recursor against the freshly regenerated one,
/// so a skipped field would be a soundness hole in that check.
///
/// Field coverage (every variant, every field of its payload struct):
/// - `ConstantVal` (`.val` on every kind): `name`, `level_params`, `ty`.
/// - `AxiomVal`: `val`, `is_unsafe`.
/// - `DefinitionVal`: `val`, `value`, `hints`, `safety`, `all`.
/// - `TheoremVal`: `val`, `value`, `all`.
/// - `OpaqueVal`: `val`, `value`, `is_unsafe`, `all`.
/// - `QuotVal`: `val`, `kind`.
/// - `InductiveVal`: `val`, `num_params`, `num_indices`, `all`,
///   `ctors`, `num_nested`, `is_rec`, `is_unsafe`, `is_reflexive`.
/// - `ConstructorVal`: `val`, `induct`, `cidx`, `num_params`,
///   `num_fields`, `is_unsafe`.
/// - `RecursorVal`: `val`, `all`, `num_params`, `num_indices`,
///   `num_motives`, `num_minors`, `rules` (per `RecursorRule`: `ctor`,
///   `nfields`, `rhs`), `k`, `is_unsafe`.
///
/// A kind mismatch (e.g. `Axiom` vs. `Defn`) is `false`, never an
/// error.
pub fn constant_info_eq(a: &ConstantInfo, b: &ConstantInfo) -> bool {
    match (a, b) {
        (ConstantInfo::Axiom(x), ConstantInfo::Axiom(y)) => {
            constant_val_eq(&x.val, &y.val) && x.is_unsafe == y.is_unsafe
        }
        (ConstantInfo::Defn(x), ConstantInfo::Defn(y)) => {
            constant_val_eq(&x.val, &y.val)
                && x.value == y.value
                && x.hints == y.hints
                && x.safety == y.safety
                && x.all == y.all
        }
        (ConstantInfo::Thm(x), ConstantInfo::Thm(y)) => {
            constant_val_eq(&x.val, &y.val) && x.value == y.value && x.all == y.all
        }
        (ConstantInfo::Opaque(x), ConstantInfo::Opaque(y)) => {
            constant_val_eq(&x.val, &y.val)
                && x.value == y.value
                && x.is_unsafe == y.is_unsafe
                && x.all == y.all
        }
        (ConstantInfo::Quot(x), ConstantInfo::Quot(y)) => {
            constant_val_eq(&x.val, &y.val) && x.kind == y.kind
        }
        (ConstantInfo::Induct(x), ConstantInfo::Induct(y)) => {
            constant_val_eq(&x.val, &y.val)
                && x.num_params == y.num_params
                && x.num_indices == y.num_indices
                && x.all == y.all
                && x.ctors == y.ctors
                && x.num_nested == y.num_nested
                && x.is_rec == y.is_rec
                && x.is_unsafe == y.is_unsafe
                && x.is_reflexive == y.is_reflexive
        }
        (ConstantInfo::Ctor(x), ConstantInfo::Ctor(y)) => {
            constant_val_eq(&x.val, &y.val)
                && x.induct == y.induct
                && x.cidx == y.cidx
                && x.num_params == y.num_params
                && x.num_fields == y.num_fields
                && x.is_unsafe == y.is_unsafe
        }
        (ConstantInfo::Rec(x), ConstantInfo::Rec(y)) => {
            constant_val_eq(&x.val, &y.val)
                && x.all == y.all
                && x.num_params == y.num_params
                && x.num_indices == y.num_indices
                && x.num_motives == y.num_motives
                && x.num_minors == y.num_minors
                && x.k == y.k
                && x.is_unsafe == y.is_unsafe
                && x.rules.len() == y.rules.len()
                && x.rules.iter().zip(y.rules.iter()).all(|(rx, ry)| {
                    rx.ctor == ry.ctor && rx.nfields == ry.nfields && rx.rhs == ry.rhs
                })
        }
        // Kind mismatch.
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bank::Store;
    use crate::testenv::{g, nm};
    use crate::ConstantInfo as ArcConstantInfo;
    use crate::{
        AxiomVal as ArcAxiomVal, ConstantVal as ArcConstantVal,
        ConstructorVal as ArcConstructorVal, DefinitionVal as ArcDefinitionVal,
        InductiveVal as ArcInductiveVal, OpaqueVal as ArcOpaqueVal, QuotVal as ArcQuotVal,
        RecursorRule as ArcRecursorRule, RecursorVal as ArcRecursorVal,
        TheoremVal as ArcTheoremVal,
    };
    use crate::{DefinitionSafety, Level, Name, Nat, QuotKind, ReducibilityHints};
    use std::sync::Arc;

    fn ty() -> Arc<crate::Expr> {
        crate::Expr::sort(Arc::new(Level::Zero), &mut g()).unwrap()
    }

    fn ty2() -> Arc<crate::Expr> {
        crate::Expr::sort(Level::mk_succ(Arc::new(Level::Zero)), &mut g()).unwrap()
    }

    fn cval(name: &str, level_params: Vec<Arc<Name>>) -> ArcConstantVal {
        ArcConstantVal {
            name: nm(name),
            level_params,
            ty: ty(),
        }
    }

    fn intern(ci: &ArcConstantInfo) -> ConstantInfo {
        let mut st = Store::persistent();
        intern_constant_info(&mut st, None, ci).unwrap()
    }

    /// Intern both `ConstantInfo`s into the SAME `Store` (`NameId`/
    /// `ExprId` equality is only meaningful within one store's id
    /// space) and assert `constant_info_eq` says they differ.
    fn assert_ne_ci(a: &ArcConstantInfo, b: &ArcConstantInfo) {
        let mut st = Store::persistent();
        let ida = intern_constant_info(&mut st, None, a).unwrap();
        let idb = intern_constant_info(&mut st, None, b).unwrap();
        assert!(!constant_info_eq(&ida, &idb));
    }

    /// Same-store counterpart of `assert_ne_ci`, asserting equality.
    fn assert_eq_ci(a: &ArcConstantInfo, b: &ArcConstantInfo) {
        let mut st = Store::persistent();
        let ida = intern_constant_info(&mut st, None, a).unwrap();
        let idb = intern_constant_info(&mut st, None, b).unwrap();
        assert!(constant_info_eq(&ida, &idb));
    }

    // Build a small Arc-side ConstantInfo, bridge in, bridge out,
    // compare with the Arc structural equality.
    #[test]
    fn constant_info_round_trip() {
        let ci = crate::testenv::axiom_u();
        let mut st = Store::persistent();
        let id_ci = intern_constant_info(&mut st, None, &ci).unwrap();
        let back = to_constant_info(&st, None, &id_ci, &mut g()).unwrap();
        assert!(crate::constant_info_eq(&ci, &back, &mut g()).unwrap());
    }

    #[test]
    fn interning_twice_gives_equal_twins() {
        let ci = crate::testenv::axiom_u();
        let mut st = Store::persistent();
        let a = intern_constant_info(&mut st, None, &ci).unwrap();
        let b = intern_constant_info(&mut st, None, &ci).unwrap();
        assert!(constant_info_eq(&a, &b));
        assert_eq!(a.name(), b.name());
    }

    /// Round-trip a `ConstantInfo` whose `ty` carries `Name::Anonymous`
    /// buried inside a `Level::Param` — pins that `Name::Anonymous`
    /// survives `intern_constant_info`/`to_constant_info` unchanged
    /// wherever it legitimately can appear (inside an expr/level tree,
    /// via the already-`Option<NameId>`-based `intern_expr`/
    /// `intern_level`), as distinct from the declaration-position name
    /// fields, which reject a literal `Name::Anonymous` outright (see
    /// `declaration_name_anonymous_is_rejected` below).
    #[test]
    fn constant_info_round_trip_with_anonymous_name_in_type() {
        let anon_sort =
            crate::Expr::sort(Arc::new(Level::Param(Arc::new(Name::Anonymous))), &mut g()).unwrap();
        let ci = ArcConstantInfo::Axiom(ArcAxiomVal {
            val: ArcConstantVal {
                name: nm("A"),
                level_params: vec![],
                ty: anon_sort,
            },
            is_unsafe: false,
        });
        let mut st = Store::persistent();
        let id_ci = intern_constant_info(&mut st, None, &ci).unwrap();
        let back = to_constant_info(&st, None, &id_ci, &mut g()).unwrap();
        assert!(crate::constant_info_eq(&ci, &back, &mut g()).unwrap());
    }

    /// A literal anonymous declaration name has no `NameId` to store
    /// (see the module doc) — pin that this is a graceful `Err`, never
    /// a panic.
    #[test]
    fn declaration_name_anonymous_is_rejected() {
        let ci = ArcConstantInfo::Axiom(ArcAxiomVal {
            val: ArcConstantVal {
                name: Arc::new(Name::Anonymous),
                level_params: vec![],
                ty: ty(),
            },
            is_unsafe: false,
        });
        let mut st = Store::persistent();
        assert!(matches!(
            intern_constant_info(&mut st, None, &ci),
            Err(KernelError::BankExhausted)
        ));
    }

    #[test]
    fn eq_distinguishes_every_field() {
        // ConstantVal.name
        let a1 = ArcConstantInfo::Axiom(ArcAxiomVal {
            val: cval("a", vec![]),
            is_unsafe: false,
        });
        let a2 = ArcConstantInfo::Axiom(ArcAxiomVal {
            val: cval("b", vec![]),
            is_unsafe: false,
        });
        assert_ne_ci(&a1, &a2);

        // ConstantVal.level_params (one differing element)
        let lp1 = ArcConstantInfo::Axiom(ArcAxiomVal {
            val: cval("a", vec![nm("u")]),
            is_unsafe: false,
        });
        let lp2 = ArcConstantInfo::Axiom(ArcAxiomVal {
            val: cval("a", vec![nm("v")]),
            is_unsafe: false,
        });
        assert_ne_ci(&lp1, &lp2);

        // ConstantVal.ty
        let t1 = ArcConstantInfo::Axiom(ArcAxiomVal {
            val: ArcConstantVal {
                name: nm("a"),
                level_params: vec![],
                ty: ty(),
            },
            is_unsafe: false,
        });
        let t2 = ArcConstantInfo::Axiom(ArcAxiomVal {
            val: ArcConstantVal {
                name: nm("a"),
                level_params: vec![],
                ty: ty2(),
            },
            is_unsafe: false,
        });
        assert_ne_ci(&t1, &t2);

        // AxiomVal.is_unsafe
        let iu1 = ArcConstantInfo::Axiom(ArcAxiomVal {
            val: cval("a", vec![]),
            is_unsafe: false,
        });
        let iu2 = ArcConstantInfo::Axiom(ArcAxiomVal {
            val: cval("a", vec![]),
            is_unsafe: true,
        });
        assert_ne_ci(&iu1, &iu2);

        // DefinitionVal.value
        let dv1 = ArcConstantInfo::Defn(ArcDefinitionVal {
            val: cval("d", vec![]),
            value: ty(),
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all: vec![nm("d")],
        });
        let dv2 = ArcConstantInfo::Defn(ArcDefinitionVal {
            val: cval("d", vec![]),
            value: ty2(),
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all: vec![nm("d")],
        });
        assert_ne_ci(&dv1, &dv2);

        // DefinitionVal.hints
        let dh = ArcConstantInfo::Defn(ArcDefinitionVal {
            val: cval("d", vec![]),
            value: ty(),
            hints: ReducibilityHints::Opaque,
            safety: DefinitionSafety::Safe,
            all: vec![nm("d")],
        });
        assert_ne_ci(&dv1, &dh);

        // DefinitionVal.safety
        let ds = ArcConstantInfo::Defn(ArcDefinitionVal {
            val: cval("d", vec![]),
            value: ty(),
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Unsafe,
            all: vec![nm("d")],
        });
        assert_ne_ci(&dv1, &ds);

        // DefinitionVal.all
        let da = ArcConstantInfo::Defn(ArcDefinitionVal {
            val: cval("d", vec![]),
            value: ty(),
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all: vec![nm("other")],
        });
        assert_ne_ci(&dv1, &da);

        // ConstructorVal.induct
        let ci1 = ArcConstantInfo::Ctor(ArcConstructorVal {
            val: cval("I.mk", vec![]),
            induct: nm("I"),
            cidx: Nat::from(0u64),
            num_params: Nat::from(0u64),
            num_fields: Nat::from(0u64),
            is_unsafe: false,
        });
        let ci2 = ArcConstantInfo::Ctor(ArcConstructorVal {
            val: cval("I.mk", vec![]),
            induct: nm("J"),
            cidx: Nat::from(0u64),
            num_params: Nat::from(0u64),
            num_fields: Nat::from(0u64),
            is_unsafe: false,
        });
        assert_ne_ci(&ci1, &ci2);

        // ConstructorVal.cidx
        let ccidx = ArcConstantInfo::Ctor(ArcConstructorVal {
            val: cval("I.mk", vec![]),
            induct: nm("I"),
            cidx: Nat::from(1u64),
            num_params: Nat::from(0u64),
            num_fields: Nat::from(0u64),
            is_unsafe: false,
        });
        assert_ne_ci(&ci1, &ccidx);

        // ConstructorVal.num_params
        let cnp = ArcConstantInfo::Ctor(ArcConstructorVal {
            val: cval("I.mk", vec![]),
            induct: nm("I"),
            cidx: Nat::from(0u64),
            num_params: Nat::from(1u64),
            num_fields: Nat::from(0u64),
            is_unsafe: false,
        });
        assert_ne_ci(&ci1, &cnp);

        // ConstructorVal.num_fields
        let cnf = ArcConstantInfo::Ctor(ArcConstructorVal {
            val: cval("I.mk", vec![]),
            induct: nm("I"),
            cidx: Nat::from(0u64),
            num_params: Nat::from(0u64),
            num_fields: Nat::from(1u64),
            is_unsafe: false,
        });
        assert_ne_ci(&ci1, &cnf);

        // ConstructorVal.is_unsafe
        let cus = ArcConstantInfo::Ctor(ArcConstructorVal {
            val: cval("I.mk", vec![]),
            induct: nm("I"),
            cidx: Nat::from(0u64),
            num_params: Nat::from(0u64),
            num_fields: Nat::from(0u64),
            is_unsafe: true,
        });
        assert_ne_ci(&ci1, &cus);

        // QuotVal.kind
        let q1 = ArcConstantInfo::Quot(ArcQuotVal {
            val: cval("q", vec![]),
            kind: QuotKind::Type,
        });
        let q2 = ArcConstantInfo::Quot(ArcQuotVal {
            val: cval("q", vec![]),
            kind: QuotKind::Ctor,
        });
        assert_ne_ci(&q1, &q2);

        // InductiveVal base + one-field perturbations.
        let mk_ind = |num_params: u64,
                      num_indices: u64,
                      all: Vec<Arc<Name>>,
                      ctors: Vec<Arc<Name>>,
                      num_nested: u64,
                      is_rec: bool,
                      is_unsafe: bool,
                      is_reflexive: bool| {
            ArcConstantInfo::Induct(ArcInductiveVal {
                val: cval("I", vec![]),
                num_params: Nat::from(num_params),
                num_indices: Nat::from(num_indices),
                all,
                ctors,
                num_nested: Nat::from(num_nested),
                is_rec,
                is_unsafe,
                is_reflexive,
            })
        };
        let ind_base = mk_ind(
            0,
            0,
            vec![nm("I")],
            vec![nm("I.mk")],
            0,
            false,
            false,
            false,
        );
        let ind_np = mk_ind(
            1,
            0,
            vec![nm("I")],
            vec![nm("I.mk")],
            0,
            false,
            false,
            false,
        );
        let ind_ni = mk_ind(
            0,
            1,
            vec![nm("I")],
            vec![nm("I.mk")],
            0,
            false,
            false,
            false,
        );
        let ind_all = mk_ind(
            0,
            0,
            vec![nm("J")],
            vec![nm("I.mk")],
            0,
            false,
            false,
            false,
        );
        let ind_ctors = mk_ind(
            0,
            0,
            vec![nm("I")],
            vec![nm("I.other")],
            0,
            false,
            false,
            false,
        );
        let ind_nn = mk_ind(
            0,
            0,
            vec![nm("I")],
            vec![nm("I.mk")],
            1,
            false,
            false,
            false,
        );
        let ind_rec = mk_ind(0, 0, vec![nm("I")], vec![nm("I.mk")], 0, true, false, false);
        let ind_unsafe = mk_ind(0, 0, vec![nm("I")], vec![nm("I.mk")], 0, false, true, false);
        let ind_reflexive = mk_ind(0, 0, vec![nm("I")], vec![nm("I.mk")], 0, false, false, true);
        assert_eq_ci(&ind_base, &ind_base);
        assert_ne_ci(&ind_base, &ind_np);
        assert_ne_ci(&ind_base, &ind_ni);
        assert_ne_ci(&ind_base, &ind_all);
        assert_ne_ci(&ind_base, &ind_ctors);
        assert_ne_ci(&ind_base, &ind_nn);
        assert_ne_ci(&ind_base, &ind_rec);
        assert_ne_ci(&ind_base, &ind_unsafe);
        assert_ne_ci(&ind_base, &ind_reflexive);

        // RecursorVal base + one-field perturbations.
        let rule = |nfields: u64, rhs: Arc<crate::Expr>| ArcRecursorRule {
            ctor: nm("I.mk"),
            nfields: Nat::from(nfields),
            rhs,
        };
        let mk_rec = |num_motives: u64, num_minors: u64, rules: Vec<ArcRecursorRule>, k: bool| {
            ArcConstantInfo::Rec(ArcRecursorVal {
                val: cval("I.rec", vec![]),
                all: vec![nm("I.rec")],
                num_params: Nat::from(0u64),
                num_indices: Nat::from(0u64),
                num_motives: Nat::from(num_motives),
                num_minors: Nat::from(num_minors),
                rules,
                k,
                is_unsafe: false,
            })
        };
        let rec_base = mk_rec(1, 1, vec![rule(0, ty())], false);
        let rec_rhs = mk_rec(1, 1, vec![rule(0, ty2())], false);
        let rec_nfields = mk_rec(1, 1, vec![rule(1, ty())], false);
        let rec_k = mk_rec(1, 1, vec![rule(0, ty())], true);
        let rec_nm = mk_rec(2, 1, vec![rule(0, ty())], false);
        let rec_nmin = mk_rec(1, 2, vec![rule(0, ty())], false);
        assert_eq_ci(&rec_base, &rec_base);
        assert_ne_ci(&rec_base, &rec_rhs);
        assert_ne_ci(&rec_base, &rec_nfields);
        assert_ne_ci(&rec_base, &rec_k);
        assert_ne_ci(&rec_base, &rec_nm);
        assert_ne_ci(&rec_base, &rec_nmin);

        // RecursorVal.num_indices (reuses the InductiveVal-adjacent
        // shape; a dedicated recursor pair keeps this independent of
        // num_params/num_motives above).
        let rec_ni_base = ArcConstantInfo::Rec(ArcRecursorVal {
            val: cval("I.rec", vec![]),
            all: vec![nm("I.rec")],
            num_params: Nat::from(0u64),
            num_indices: Nat::from(0u64),
            num_motives: Nat::from(1u64),
            num_minors: Nat::from(1u64),
            rules: vec![rule(0, ty())],
            k: false,
            is_unsafe: false,
        });
        let rec_ni_diff = ArcConstantInfo::Rec(ArcRecursorVal {
            val: cval("I.rec", vec![]),
            all: vec![nm("I.rec")],
            num_params: Nat::from(0u64),
            num_indices: Nat::from(1u64),
            num_motives: Nat::from(1u64),
            num_minors: Nat::from(1u64),
            rules: vec![rule(0, ty())],
            k: false,
            is_unsafe: false,
        });
        assert_ne_ci(&rec_ni_base, &rec_ni_diff);

        // Kind mismatch => false.
        assert_ne_ci(&a1, &dv1);
    }

    #[test]
    fn kind_strings_match_arc_kernel() {
        let cases: Vec<ArcConstantInfo> = vec![
            ArcConstantInfo::Axiom(ArcAxiomVal {
                val: cval("a", vec![]),
                is_unsafe: false,
            }),
            ArcConstantInfo::Defn(ArcDefinitionVal {
                val: cval("d", vec![]),
                value: ty(),
                hints: ReducibilityHints::Regular(0),
                safety: DefinitionSafety::Safe,
                all: vec![nm("d")],
            }),
            ArcConstantInfo::Thm(ArcTheoremVal {
                val: cval("t", vec![]),
                value: ty(),
                all: vec![nm("t")],
            }),
            ArcConstantInfo::Opaque(ArcOpaqueVal {
                val: cval("o", vec![]),
                value: ty(),
                is_unsafe: false,
                all: vec![nm("o")],
            }),
            ArcConstantInfo::Quot(ArcQuotVal {
                val: cval("q", vec![]),
                kind: QuotKind::Type,
            }),
            ArcConstantInfo::Induct(ArcInductiveVal {
                val: cval("I", vec![]),
                num_params: Nat::from(0u64),
                num_indices: Nat::from(0u64),
                all: vec![nm("I")],
                ctors: vec![nm("I.mk")],
                num_nested: Nat::from(0u64),
                is_rec: false,
                is_unsafe: false,
                is_reflexive: false,
            }),
            ArcConstantInfo::Ctor(ArcConstructorVal {
                val: cval("I.mk", vec![]),
                induct: nm("I"),
                cidx: Nat::from(0u64),
                num_params: Nat::from(0u64),
                num_fields: Nat::from(0u64),
                is_unsafe: false,
            }),
            ArcConstantInfo::Rec(ArcRecursorVal {
                val: cval("I.rec", vec![]),
                all: vec![nm("I.rec")],
                num_params: Nat::from(0u64),
                num_indices: Nat::from(0u64),
                num_motives: Nat::from(1u64),
                num_minors: Nat::from(1u64),
                rules: vec![ArcRecursorRule {
                    ctor: nm("I.mk"),
                    nfields: Nat::from(0u64),
                    rhs: ty(),
                }],
                k: false,
                is_unsafe: false,
            }),
        ];
        for arc_ci in &cases {
            let id_ci = intern(arc_ci);
            assert_eq!(id_ci.kind(), arc_ci.kind(), "kind mismatch for {arc_ci:?}");
        }
    }
}
