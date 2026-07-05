//! Constant declarations as the kernel sees them (oracle:
//! src/Lean/Declaration.lean; per-type line cites below). Field names
//! and order mirror the oracle so the decoder and future checker read
//! like the original.

use std::sync::Arc;

use crate::{Expr, KernelError, Name, Nat, RecGuard};

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

/// `ConstantVal` structural equality: `name` and `level_params` via
/// `Name`'s (non-recursive, adversarial-depth-safe) `PartialEq`, `ty`
/// via `Expr::structural_eq` under the caller's `RecGuard`.
fn constant_val_eq(
    a: &ConstantVal,
    b: &ConstantVal,
    g: &mut RecGuard,
) -> Result<bool, KernelError> {
    Ok(a.name == b.name
        && name_slice_eq(&a.level_params, &b.level_params)
        && Expr::structural_eq(&a.ty, &b.ty, g)?)
}

/// Element-wise `Name` equality over a `Name` list (`all`/`ctors`/
/// `level_params`): same length, same names in order.
fn name_slice_eq(a: &[Arc<Name>], b: &[Arc<Name>]) -> bool {
    a.len() == b.len() && a.iter().zip(b.iter()).all(|(x, y)| x == y)
}

/// Structural equality over EVERY field of `ConstantInfo` (oracle:
/// Lean's derived `BEq ConstantInfo` compares all fields of all 8
/// kinds; this is a line-for-line field enumeration of that, not a
/// `PartialEq` impl — see the module-level rationale in the Task 11
/// brief: `PartialEq` can neither thread a `RecGuard` through the
/// depth-bounded descent into `Expr`/`Name` trees, nor report
/// `KernelError::DeepRecursion` on a guard-cap hit, so a trait impl
/// would silently hide that path (panic or wrong answer) instead of
/// surfacing it as `Err`. Task 12's replay uses this to compare a
/// postponed constructor/recursor against the freshly regenerated one,
/// so field coverage below must be complete — a skipped field would be
/// a soundness hole in that check.
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
/// A kind mismatch (e.g. `Axiom` vs. `Defn`) is `Ok(false)`, never an
/// error.
pub fn constant_info_eq(
    a: &ConstantInfo,
    b: &ConstantInfo,
    g: &mut RecGuard,
) -> Result<bool, KernelError> {
    match (a, b) {
        (ConstantInfo::Axiom(x), ConstantInfo::Axiom(y)) => {
            Ok(constant_val_eq(&x.val, &y.val, g)? && x.is_unsafe == y.is_unsafe)
        }
        (ConstantInfo::Defn(x), ConstantInfo::Defn(y)) => Ok(constant_val_eq(&x.val, &y.val, g)?
            && Expr::structural_eq(&x.value, &y.value, g)?
            && x.hints == y.hints
            && x.safety == y.safety
            && name_slice_eq(&x.all, &y.all)),
        (ConstantInfo::Thm(x), ConstantInfo::Thm(y)) => Ok(constant_val_eq(&x.val, &y.val, g)?
            && Expr::structural_eq(&x.value, &y.value, g)?
            && name_slice_eq(&x.all, &y.all)),
        (ConstantInfo::Opaque(x), ConstantInfo::Opaque(y)) => {
            Ok(constant_val_eq(&x.val, &y.val, g)?
                && Expr::structural_eq(&x.value, &y.value, g)?
                && x.is_unsafe == y.is_unsafe
                && name_slice_eq(&x.all, &y.all))
        }
        (ConstantInfo::Quot(x), ConstantInfo::Quot(y)) => {
            Ok(constant_val_eq(&x.val, &y.val, g)? && x.kind == y.kind)
        }
        (ConstantInfo::Induct(x), ConstantInfo::Induct(y)) => {
            Ok(constant_val_eq(&x.val, &y.val, g)?
                && x.num_params == y.num_params
                && x.num_indices == y.num_indices
                && name_slice_eq(&x.all, &y.all)
                && name_slice_eq(&x.ctors, &y.ctors)
                && x.num_nested == y.num_nested
                && x.is_rec == y.is_rec
                && x.is_unsafe == y.is_unsafe
                && x.is_reflexive == y.is_reflexive)
        }
        (ConstantInfo::Ctor(x), ConstantInfo::Ctor(y)) => Ok(constant_val_eq(&x.val, &y.val, g)?
            && x.induct == y.induct
            && x.cidx == y.cidx
            && x.num_params == y.num_params
            && x.num_fields == y.num_fields
            && x.is_unsafe == y.is_unsafe),
        (ConstantInfo::Rec(x), ConstantInfo::Rec(y)) => {
            if !constant_val_eq(&x.val, &y.val, g)?
                || !name_slice_eq(&x.all, &y.all)
                || x.num_params != y.num_params
                || x.num_indices != y.num_indices
                || x.num_motives != y.num_motives
                || x.num_minors != y.num_minors
                || x.k != y.k
                || x.is_unsafe != y.is_unsafe
                || x.rules.len() != y.rules.len()
            {
                return Ok(false);
            }
            for (rx, ry) in x.rules.iter().zip(y.rules.iter()) {
                if rx.ctor != ry.ctor || rx.nfields != ry.nfields {
                    return Ok(false);
                }
                if !Expr::structural_eq(&rx.rhs, &ry.rhs, g)? {
                    return Ok(false);
                }
            }
            Ok(true)
        }
        // Kind mismatch.
        _ => Ok(false),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Level;

    fn nm(s: &str) -> Arc<Name> {
        Arc::new(Name::Str {
            parent: Arc::new(Name::Anonymous),
            part: s.to_string(),
        })
    }

    fn g() -> RecGuard {
        RecGuard::new()
    }

    fn ty() -> Arc<Expr> {
        Expr::sort(Arc::new(Level::Zero), &mut g()).unwrap()
    }

    fn cval(name: &str) -> ConstantVal {
        ConstantVal {
            name: nm(name),
            level_params: vec![],
            ty: ty(),
        }
    }

    #[test]
    fn constant_info_eq_discriminates() {
        let mut g = g();

        // Axiom: differing `is_unsafe`.
        let ax1 = ConstantInfo::Axiom(AxiomVal {
            val: cval("a"),
            is_unsafe: false,
        });
        let ax2 = ConstantInfo::Axiom(AxiomVal {
            val: cval("a"),
            is_unsafe: false,
        });
        let ax3 = ConstantInfo::Axiom(AxiomVal {
            val: cval("a"),
            is_unsafe: true,
        });
        assert!(constant_info_eq(&ax1, &ax2, &mut g).unwrap());
        assert!(!constant_info_eq(&ax1, &ax3, &mut g).unwrap());

        // Defn: differing `hints`, differing `safety`.
        let d1 = ConstantInfo::Defn(DefinitionVal {
            val: cval("d"),
            value: ty(),
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all: vec![nm("d")],
        });
        let d2 = ConstantInfo::Defn(DefinitionVal {
            val: cval("d"),
            value: ty(),
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all: vec![nm("d")],
        });
        let d_hints = ConstantInfo::Defn(DefinitionVal {
            val: cval("d"),
            value: ty(),
            hints: ReducibilityHints::Opaque,
            safety: DefinitionSafety::Safe,
            all: vec![nm("d")],
        });
        let d_safety = ConstantInfo::Defn(DefinitionVal {
            val: cval("d"),
            value: ty(),
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Unsafe,
            all: vec![nm("d")],
        });
        assert!(constant_info_eq(&d1, &d2, &mut g).unwrap());
        assert!(!constant_info_eq(&d1, &d_hints, &mut g).unwrap());
        assert!(!constant_info_eq(&d1, &d_safety, &mut g).unwrap());

        // Thm: differing `all`.
        let t1 = ConstantInfo::Thm(TheoremVal {
            val: cval("t"),
            value: ty(),
            all: vec![nm("t")],
        });
        let t2 = ConstantInfo::Thm(TheoremVal {
            val: cval("t"),
            value: ty(),
            all: vec![nm("t")],
        });
        let t3 = ConstantInfo::Thm(TheoremVal {
            val: cval("t"),
            value: ty(),
            all: vec![nm("other")],
        });
        assert!(constant_info_eq(&t1, &t2, &mut g).unwrap());
        assert!(!constant_info_eq(&t1, &t3, &mut g).unwrap());

        // Opaque: differing `is_unsafe`.
        let o1 = ConstantInfo::Opaque(OpaqueVal {
            val: cval("o"),
            value: ty(),
            is_unsafe: false,
            all: vec![nm("o")],
        });
        let o2 = ConstantInfo::Opaque(OpaqueVal {
            val: cval("o"),
            value: ty(),
            is_unsafe: false,
            all: vec![nm("o")],
        });
        let o3 = ConstantInfo::Opaque(OpaqueVal {
            val: cval("o"),
            value: ty(),
            is_unsafe: true,
            all: vec![nm("o")],
        });
        assert!(constant_info_eq(&o1, &o2, &mut g).unwrap());
        assert!(!constant_info_eq(&o1, &o3, &mut g).unwrap());

        // Quot: differing `kind`.
        let q1 = ConstantInfo::Quot(QuotVal {
            val: cval("q"),
            kind: QuotKind::Type,
        });
        let q2 = ConstantInfo::Quot(QuotVal {
            val: cval("q"),
            kind: QuotKind::Type,
        });
        let q3 = ConstantInfo::Quot(QuotVal {
            val: cval("q"),
            kind: QuotKind::Ctor,
        });
        assert!(constant_info_eq(&q1, &q2, &mut g).unwrap());
        assert!(!constant_info_eq(&q1, &q3, &mut g).unwrap());

        // Induct: differing `is_rec`.
        let mk_ind = |is_rec: bool| {
            ConstantInfo::Induct(InductiveVal {
                val: cval("I"),
                num_params: Nat::from(0u64),
                num_indices: Nat::from(0u64),
                all: vec![nm("I")],
                ctors: vec![nm("I.mk")],
                num_nested: Nat::from(0u64),
                is_rec,
                is_unsafe: false,
                is_reflexive: false,
            })
        };
        let i1 = mk_ind(false);
        let i2 = mk_ind(false);
        let i3 = mk_ind(true);
        assert!(constant_info_eq(&i1, &i2, &mut g).unwrap());
        assert!(!constant_info_eq(&i1, &i3, &mut g).unwrap());

        // Ctor: differing `cidx`.
        let mk_ctor = |cidx: u64| {
            ConstantInfo::Ctor(ConstructorVal {
                val: cval("I.mk"),
                induct: nm("I"),
                cidx: Nat::from(cidx),
                num_params: Nat::from(0u64),
                num_fields: Nat::from(0u64),
                is_unsafe: false,
            })
        };
        let c1 = mk_ctor(0);
        let c2 = mk_ctor(0);
        let c3 = mk_ctor(1);
        assert!(constant_info_eq(&c1, &c2, &mut g).unwrap());
        assert!(!constant_info_eq(&c1, &c3, &mut g).unwrap());

        // Rec: differing rule `nfields`, differing `k`.
        let rule_a = RecursorRule {
            ctor: nm("I.mk"),
            nfields: Nat::from(0u64),
            rhs: ty(),
        };
        let rule_b = RecursorRule {
            ctor: nm("I.mk"),
            nfields: Nat::from(1u64),
            rhs: ty(),
        };
        let mk_rec = |rules: Vec<RecursorRule>, k: bool| {
            ConstantInfo::Rec(RecursorVal {
                val: cval("I.rec"),
                all: vec![nm("I.rec")],
                num_params: Nat::from(0u64),
                num_indices: Nat::from(0u64),
                num_motives: Nat::from(1u64),
                num_minors: Nat::from(1u64),
                rules,
                k,
                is_unsafe: false,
            })
        };
        let r1 = mk_rec(vec![rule_a.clone()], false);
        let r2 = mk_rec(vec![rule_a.clone()], false);
        let r3 = mk_rec(vec![rule_b], false);
        let r4 = mk_rec(vec![rule_a], true);
        assert!(constant_info_eq(&r1, &r2, &mut g).unwrap());
        assert!(!constant_info_eq(&r1, &r3, &mut g).unwrap());
        assert!(!constant_info_eq(&r1, &r4, &mut g).unwrap());

        // Kind mismatch => false, not an error.
        assert!(!constant_info_eq(&ax1, &d1, &mut g).unwrap());
    }
}
