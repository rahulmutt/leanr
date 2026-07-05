//! Port of `ConstantInfo.getUsedConstantsAsSet` (oracle:
//! src/Lean/Util/FoldConsts.lean:65-71), the dependency source replay
//! uses to admit declarations in the right order.
//!
//! The oracle collects (a) every `Const` name in the declaration's
//! `type`, (b) if it has a value (defn always; thm/opaque with
//! `allowOpaque := true`) every `Const` name in that value, and (c) when
//! it has *no* value, a per-kind name set: `inductInfo` → its `ctors`,
//! `ctorInfo` → its own name, `recInfo` → its `all`. We reproduce that
//! exactly, and additionally walk each recursor rule's `rhs` (the brief's
//! "type+value+rec rules"): that is a strict *superset* of the oracle's
//! dependency set, which is always safe — replay only ever needs a
//! declaration's true dependencies to be present *before* it, so extra
//! names (already destined for replay) only pull work earlier, never
//! change the outcome. A *missing* dependency, by contrast, would be a
//! real bug (admitting a decl whose reference is not yet in the env), so
//! erring toward a superset is the conservative choice.
//!
//! Recursion discipline (lib.rs): the `Expr` walk is an explicit-stack
//! loop, never guarded recursion — a plain traversal per the crate's
//! default. Attacker-controlled term depth cannot overflow the OS stack
//! because we never recurse into `Arc<Expr>` children.

use std::collections::HashSet;
use std::sync::Arc;

use crate::{ConstantInfo, Expr, ExprNode, Name};

/// Collect, deduplicated and in first-seen order, every constant name a
/// `ConstantInfo` depends on for replay ordering. See the module doc for
/// the exact field coverage (mirrors `ConstantInfo.getUsedConstantsAsSet`
/// plus recursor-rule right-hand sides).
pub fn used_constants(info: &ConstantInfo) -> Vec<Arc<Name>> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();

    // (a) constants in the declared type — always.
    collect_expr_consts(&info.constant_val().ty, &mut out, &mut seen);

    // (b)/(c) value consts when present, else the per-kind name set.
    match info {
        ConstantInfo::Defn(v) => collect_expr_consts(&v.value, &mut out, &mut seen),
        ConstantInfo::Thm(v) => collect_expr_consts(&v.value, &mut out, &mut seen),
        ConstantInfo::Opaque(v) => collect_expr_consts(&v.value, &mut out, &mut seen),
        // No value: the oracle's `getUsedConstantsAsSet` else-branch.
        ConstantInfo::Induct(v) => {
            for ctor in &v.ctors {
                push_name(ctor, &mut out, &mut seen);
            }
        }
        ConstantInfo::Ctor(v) => push_name(&v.val.name, &mut out, &mut seen),
        ConstantInfo::Rec(v) => {
            for n in &v.all {
                push_name(n, &mut out, &mut seen);
            }
            // Superset over the oracle: also the rule right-hand sides
            // (see module doc). Harmless and satisfies the brief.
            for rule in &v.rules {
                collect_expr_consts(&rule.rhs, &mut out, &mut seen);
            }
        }
        // Axiom / Quot carry no value and no extra names.
        ConstantInfo::Axiom(_) | ConstantInfo::Quot(_) => {}
    }

    out
}

fn push_name(name: &Arc<Name>, out: &mut Vec<Arc<Name>>, seen: &mut HashSet<Arc<Name>>) {
    if seen.insert(Arc::clone(name)) {
        out.push(Arc::clone(name));
    }
}

/// Iterative (explicit-stack) walk collecting every `Const` name in an
/// expression tree, deduped against `seen`.
fn collect_expr_consts(root: &Arc<Expr>, out: &mut Vec<Arc<Name>>, seen: &mut HashSet<Arc<Name>>) {
    let mut stack: Vec<Arc<Expr>> = vec![Arc::clone(root)];
    while let Some(e) = stack.pop() {
        match e.node() {
            ExprNode::Const { name, .. } => push_name(name, out, seen),
            ExprNode::App { f, arg } => {
                stack.push(Arc::clone(f));
                stack.push(Arc::clone(arg));
            }
            ExprNode::Lam {
                binder_type, body, ..
            }
            | ExprNode::ForallE {
                binder_type, body, ..
            } => {
                stack.push(Arc::clone(binder_type));
                stack.push(Arc::clone(body));
            }
            ExprNode::LetE {
                ty, value, body, ..
            } => {
                stack.push(Arc::clone(ty));
                stack.push(Arc::clone(value));
                stack.push(Arc::clone(body));
            }
            ExprNode::MData { expr, .. } => stack.push(Arc::clone(expr)),
            ExprNode::Proj { structure, .. } => stack.push(Arc::clone(structure)),
            // Leaves with no `Const` child.
            ExprNode::BVar { .. }
            | ExprNode::FVar { .. }
            | ExprNode::MVar { .. }
            | ExprNode::Sort { .. }
            | ExprNode::Lit(_) => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        AxiomVal, BinderInfo, ConstantVal, ConstructorVal, DefinitionSafety, DefinitionVal,
        InductiveVal, Nat, RecGuard, RecursorRule, RecursorVal, ReducibilityHints,
    };

    fn nm(s: &str) -> Arc<Name> {
        Arc::new(Name::Str {
            parent: Arc::new(Name::Anonymous),
            part: s.to_string(),
        })
    }

    fn g() -> RecGuard {
        RecGuard::new()
    }

    fn cst(name: &str) -> Arc<Expr> {
        Expr::const_(nm(name), vec![], &mut g()).unwrap()
    }

    fn cval(name: &str, ty: Arc<Expr>) -> ConstantVal {
        ConstantVal {
            name: nm(name),
            level_params: vec![],
            ty,
        }
    }

    #[test]
    fn walks_type_and_value_deduped() {
        // def d : A := app B B   (type uses A; value uses B twice)
        let value = Expr::app(cst("B"), cst("B"));
        let info = ConstantInfo::Defn(DefinitionVal {
            val: cval("d", cst("A")),
            value,
            hints: ReducibilityHints::Regular(0),
            safety: DefinitionSafety::Safe,
            all: vec![nm("d")],
        });
        let used = used_constants(&info);
        assert!(used.contains(&nm("A")));
        assert!(used.contains(&nm("B")));
        // `B` appears twice in the value but is deduped.
        assert_eq!(used.iter().filter(|n| ***n == *nm("B")).count(), 1);
    }

    #[test]
    fn walks_binders_and_proj() {
        // ty = ∀ (x : A), Proj S 0 (Const C)   — reaches A, and C through
        // the projection structure.
        let proj = Expr::proj(nm("S"), Nat::from(0u64), cst("C"));
        let ty = Expr::forall_e(nm("x"), cst("A"), proj, BinderInfo::Default);
        let info = ConstantInfo::Axiom(AxiomVal {
            val: cval("ax", ty),
            is_unsafe: false,
        });
        let used = used_constants(&info);
        assert!(used.contains(&nm("A")));
        assert!(used.contains(&nm("C")));
    }

    #[test]
    fn inductive_yields_ctor_names() {
        let info = ConstantInfo::Induct(InductiveVal {
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
        let used = used_constants(&info);
        assert!(used.contains(&nm("I.a")));
        assert!(used.contains(&nm("I.b")));
    }

    #[test]
    fn ctor_yields_own_name() {
        let info = ConstantInfo::Ctor(ConstructorVal {
            val: cval("I.a", cst("I")),
            induct: nm("I"),
            cidx: Nat::from(0u64),
            num_params: Nat::from(0u64),
            num_fields: Nat::from(0u64),
            is_unsafe: false,
        });
        let used = used_constants(&info);
        assert!(used.contains(&nm("I.a")));
        assert!(used.contains(&nm("I"))); // from the type
    }

    #[test]
    fn recursor_yields_all_and_rule_rhs() {
        let info = ConstantInfo::Rec(RecursorVal {
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
        let used = used_constants(&info);
        assert!(used.contains(&nm("I.rec"))); // from `all`
        assert!(used.contains(&nm("motiveTy"))); // from the type
        assert!(used.contains(&nm("RhsConst"))); // from the rule rhs
    }

    #[test]
    fn deep_expr_does_not_overflow() {
        // A left-nested application spine 200k deep: the iterative walk
        // must not recurse into `Arc<Expr>` children.
        let mut e = cst("head");
        for _ in 0..200_000 {
            e = Expr::app(e, cst("x"));
        }
        let info = ConstantInfo::Axiom(AxiomVal {
            val: cval("ax", e),
            is_unsafe: false,
        });
        let used = used_constants(&info);
        assert!(used.contains(&nm("head")));
        assert!(used.contains(&nm("x")));
    }
}
