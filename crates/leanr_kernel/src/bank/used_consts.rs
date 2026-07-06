//! Id-native port of `crate::used_consts` (oracle:
//! src/Lean/Util/FoldConsts.lean:65-71, `ConstantInfo.getUsedConstantsAsSet`)
//! — the dependency source `bank::replay` uses to admit declarations in
//! the right order. Representation-only port: `Arc<Name>` -> `NameId`,
//! `Arc<Expr>`/`ExprNode` -> `ExprId`/`terms::Node`, otherwise identical
//! field coverage and traversal shape to `crate::used_consts`'s own
//! module doc (reproduced here for the exact dependency-set rationale).
//!
//! The oracle collects (a) every `Const` name in the declaration's
//! `type`, (b) if it has a value (defn always; thm/opaque with
//! `allowOpaque := true`) every `Const` name in that value, and (c) when
//! it has *no* value, a per-kind name set: `inductInfo` -> its `ctors`,
//! `ctorInfo` -> its own name, `recInfo` -> its `all`. We reproduce that
//! exactly, and additionally walk each recursor rule's `rhs` (the
//! brief's "type+value+rec rules"): a strict *superset* of the oracle's
//! dependency set, always safe for the same reason `crate::used_consts`
//! documents (extra names only pull already-destined work earlier, a
//! missing dependency would be a real bug).
//!
//! Recursion discipline (lib.rs): the `ExprId` walk is an explicit-stack
//! loop, never guarded recursion — same posture as `crate::used_consts`
//! and every other bank-module tree walk (`scratch::promote`,
//! `subst.rs`).

use std::collections::HashSet;

use super::decl::ConstantInfo;
use super::terms::Node;
use super::{ExprId, NameId, Store};

/// Collect, deduplicated and in first-seen order, every constant
/// `NameId` a `ConstantInfo` depends on for replay ordering. See the
/// module doc for the exact field coverage (mirrors
/// `ConstantInfo.getUsedConstantsAsSet` plus recursor-rule right-hand
/// sides). `st`/`base` follow the crate's usual "writable store first,
/// `base: Option<&Store>` second" convention, though this walk never
/// writes — it only reads rows, routing through `base` exactly like
/// every other read-only bank helper.
pub fn used_constants(st: &Store, base: Option<&Store>, info: &ConstantInfo) -> Vec<NameId> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();

    // (a) constants in the declared type — always.
    collect_expr_consts(st, base, info.constant_val().ty, &mut out, &mut seen);

    // (b)/(c) value consts when present, else the per-kind name set.
    match info {
        ConstantInfo::Defn(v) => collect_expr_consts(st, base, v.value, &mut out, &mut seen),
        ConstantInfo::Thm(v) => collect_expr_consts(st, base, v.value, &mut out, &mut seen),
        ConstantInfo::Opaque(v) => collect_expr_consts(st, base, v.value, &mut out, &mut seen),
        // No value: the oracle's `getUsedConstantsAsSet` else-branch.
        ConstantInfo::Induct(v) => {
            for &ctor in &v.ctors {
                push_name(ctor, &mut out, &mut seen);
            }
        }
        ConstantInfo::Ctor(v) => push_name(v.val.name, &mut out, &mut seen),
        ConstantInfo::Rec(v) => {
            for &n in &v.all {
                push_name(n, &mut out, &mut seen);
            }
            // Superset over the oracle: also the rule right-hand sides
            // (see module doc). Harmless and satisfies the brief.
            for rule in &v.rules {
                collect_expr_consts(st, base, rule.rhs, &mut out, &mut seen);
            }
        }
        // Axiom / Quot carry no value and no extra names.
        ConstantInfo::Axiom(_) | ConstantInfo::Quot(_) => {}
    }

    out
}

fn push_name(name: NameId, out: &mut Vec<NameId>, seen: &mut HashSet<NameId>) {
    if seen.insert(name) {
        out.push(name);
    }
}

/// Iterative (explicit-stack) walk collecting every `Const` name in an
/// expression tree, deduped against `seen`. A `Const` node whose name is
/// `None` (`Name::Anonymous`) is skipped: no declaration is ever named
/// `Name::Anonymous` (`decl.rs`'s module doc), so it can never denote a
/// real dependency — the id-native analog of the Arc walk never having
/// this case at all (`ExprNode::Const.name` is a plain `Arc<Name>`
/// there).
fn collect_expr_consts(
    st: &Store,
    base: Option<&Store>,
    root: ExprId,
    out: &mut Vec<NameId>,
    seen: &mut HashSet<NameId>,
) {
    let mut stack: Vec<ExprId> = vec![root];
    while let Some(e) = stack.pop() {
        match st.expr_node(base, e) {
            Node::Const { name, .. } => {
                if let Some(n) = name {
                    push_name(n, out, seen);
                }
            }
            Node::App { f, arg } => {
                stack.push(f);
                stack.push(arg);
            }
            Node::Lam {
                binder_type, body, ..
            }
            | Node::Forall {
                binder_type, body, ..
            } => {
                stack.push(binder_type);
                stack.push(body);
            }
            Node::LetE {
                ty, value, body, ..
            } => {
                stack.push(ty);
                stack.push(value);
                stack.push(body);
            }
            Node::MData { expr, .. } => stack.push(expr),
            Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => stack.push(structure),
            // Leaves with no `Const` child.
            Node::BVar { .. }
            | Node::BVarBig { .. }
            | Node::FVar { .. }
            | Node::MVar { .. }
            | Node::Sort { .. }
            | Node::LitNat { .. }
            | Node::LitStr { .. } => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bank::decl::intern_constant_info;
    use crate::testenv::{g, nm};
    use crate::{
        AxiomVal, BinderInfo, ConstantInfo as ArcConstantInfo, ConstructorVal, DefinitionSafety,
        DefinitionVal, Expr, InductiveVal, Name, Nat, RecursorRule, RecursorVal, ReducibilityHints,
    };
    use std::sync::Arc;

    fn cst(name: &str) -> Arc<Expr> {
        Expr::const_(nm(name), vec![], &mut g()).unwrap()
    }

    fn cval(name: &str, ty: Arc<Expr>) -> crate::ConstantVal {
        crate::ConstantVal {
            name: nm(name),
            level_params: vec![],
            ty,
        }
    }

    /// Bridge an Arc-side `ConstantInfo` into a fresh persistent `Store`
    /// and run the id-native `used_constants`, returning the bridged-out
    /// `Arc<Name>`s for easy comparison against the Arc test's own
    /// expectations (dual-harness convention, `bank::decl::tests`'
    /// `intern`/`assert_eq_ci` precedent).
    fn used(ci: &ArcConstantInfo) -> (Store, Vec<NameId>) {
        let mut st = Store::persistent();
        let id_ci = intern_constant_info(&mut st, None, ci).unwrap();
        let used = used_constants(&st, None, &id_ci);
        (st, used)
    }

    fn contains(st: &Store, used: &[NameId], name: &str) -> bool {
        used.iter().any(|&n| st.to_name(None, Some(n)) == nm(name))
    }

    #[test]
    fn walks_type_and_value_deduped() {
        // def d : A := app B B   (type uses A; value uses B twice)
        let value = Expr::app(cst("B"), cst("B"));
        let info = ArcConstantInfo::Defn(DefinitionVal {
            val: cval("d", cst("A")),
            value,
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all: vec![nm("d")],
        });
        let (st, used) = used(&info);
        assert!(contains(&st, &used, "A"));
        assert!(contains(&st, &used, "B"));
        // `B` appears twice in the value but is deduped.
        assert_eq!(
            used.iter()
                .filter(|&&n| st.to_name(None, Some(n)) == nm("B"))
                .count(),
            1
        );
    }

    #[test]
    fn walks_binders_and_proj() {
        // ty = forall (x : A), Proj S 0 (Const C) — reaches A, and C
        // through the projection structure.
        let proj = Expr::proj(nm("S"), Nat::from(0u64), cst("C"));
        let ty = Expr::forall_e(nm("x"), cst("A"), proj, BinderInfo::Default);
        let info = ArcConstantInfo::Axiom(AxiomVal {
            val: cval("ax", ty),
            is_unsafe: false,
        });
        let (st, used) = used(&info);
        assert!(contains(&st, &used, "A"));
        assert!(contains(&st, &used, "C"));
    }

    #[test]
    fn inductive_yields_ctor_names() {
        let info = ArcConstantInfo::Induct(InductiveVal {
            val: cval("I", cst("Sort")),
            num_params: Nat::from(0u64),
            num_indices: Nat::from(0u64),
            all: vec![nm("I")],
            ctors: vec![nm("I.a"), nm("I.b")],
            num_nested: Nat::from(0u64),
            is_rec: false,
            is_unsafe: false,
            is_reflexive: false,
        });
        let (st, used) = used(&info);
        assert!(contains(&st, &used, "I.a"));
        assert!(contains(&st, &used, "I.b"));
    }

    #[test]
    fn ctor_yields_own_name() {
        let info = ArcConstantInfo::Ctor(ConstructorVal {
            val: cval("I.a", cst("I")),
            induct: nm("I"),
            cidx: Nat::from(0u64),
            num_params: Nat::from(0u64),
            num_fields: Nat::from(0u64),
            is_unsafe: false,
        });
        let (st, used) = used(&info);
        assert!(contains(&st, &used, "I.a"));
        assert!(contains(&st, &used, "I")); // from the type
    }

    #[test]
    fn recursor_yields_all_and_rule_rhs() {
        let info = ArcConstantInfo::Rec(RecursorVal {
            val: cval("I.rec", cst("motiveTy")),
            all: vec![nm("I.rec")],
            num_params: Nat::from(0u64),
            num_indices: Nat::from(0u64),
            num_motives: Nat::from(1u64),
            num_minors: Nat::from(1u64),
            rules: vec![RecursorRule {
                ctor: nm("I.a"),
                nfields: Nat::from(0u64),
                rhs: cst("RhsConst"),
            }],
            k: false,
            is_unsafe: false,
        });
        let (st, used) = used(&info);
        assert!(contains(&st, &used, "I.rec")); // from `all`
        assert!(contains(&st, &used, "motiveTy")); // from the type
        assert!(contains(&st, &used, "RhsConst")); // from the rule rhs
    }

    #[test]
    fn deep_expr_does_not_overflow() {
        // A left-nested application spine 200k deep: the iterative walk
        // must not recurse into child ids.
        let mut e = cst("head");
        for _ in 0..200_000 {
            e = Expr::app(e, cst("x"));
        }
        let info = ArcConstantInfo::Axiom(AxiomVal {
            val: cval("ax", e),
            is_unsafe: false,
        });
        let (st, used) = used(&info);
        assert!(contains(&st, &used, "head"));
        assert!(contains(&st, &used, "x"));
    }

    #[test]
    fn anonymous_const_name_is_skipped() {
        // A `Const` node naming `Name::Anonymous` can never denote a
        // real dependency (decl.rs's module doc) — pin that the walk
        // skips it rather than pushing a bogus `NameId`.
        let anon_const = Expr::const_(Arc::new(Name::Anonymous), vec![], &mut g()).unwrap();
        let info = ArcConstantInfo::Axiom(AxiomVal {
            val: cval("ax", anon_const),
            is_unsafe: false,
        });
        let (_, used) = used(&info);
        assert!(used.is_empty());
    }
}
