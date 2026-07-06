//! Structural interning (hash-consing) for `Expr`/`Level`.
//!
//! A *transient* batch canonicalizer: build an `Interner`, rewrite the
//! decoded constants through it, then drop it. Structurally-identical
//! subterms collapse to one shared `Arc`, so the resulting `Arc` graph
//! (and the `Environment` built from it) holds each distinct subterm once.
//! No global state, no `Weak` refs, no hot-path cost (see
//! docs/superpowers/specs/2026-07-06-expr-hash-consing-design.md).
//!
//! Soundness: interning only ever replaces an `Arc<Expr>`/`Arc<Level>` with
//! a structurally-identical one. The kernel decides types by
//! `structural_eq`/`is_def_eq` (value comparison; `Arc::ptr_eq` is only a
//! fast path), so no verdict can change. Bucket comparison uses the
//! existing `structural_eq`, which compares every field (binder names,
//! `BinderInfo`, `non_dep`, `KVMap`), so merged nodes are fully identical.

use crate::{Expr, ExprNode, KernelError, Level, RecGuard};
use std::collections::HashMap;
use std::sync::Arc;

// `Interner` and its methods are only reachable from `#[cfg(test)]` until
// Task 3 wires up `intern_constants` as the crate's public entry point (see
// lib.rs); `allow(dead_code)` here is temporary scaffolding removed in Task 3.
#[derive(Default)]
#[allow(dead_code)]
pub struct Interner {
    /// Canonical levels, bucketed by `Level::hash_val`.
    levels: HashMap<u64, Vec<Arc<Level>>>,
    /// Input-`Arc`-address → canonical level, so a shared input subtree is
    /// interned once. Keys are live for the pass's lifetime only.
    level_memo: HashMap<usize, Arc<Level>>,
    /// Canonical exprs, bucketed by `ExprData::hash()` (structural hash).
    exprs: HashMap<u32, Vec<Arc<Expr>>>,
    /// Input-`Arc`-address → canonical expr (per-pass lifetime only).
    expr_memo: HashMap<usize, Arc<Expr>>,
}

#[allow(dead_code)]
impl Interner {
    pub fn new() -> Interner {
        Interner::default()
    }

    /// Canonicalize a level bottom-up. Returns the shared canonical `Arc`
    /// for `l`'s structural value.
    pub fn intern_level(
        &mut self,
        l: &Arc<Level>,
        g: &mut RecGuard,
    ) -> Result<Arc<Level>, KernelError> {
        let key = Arc::as_ptr(l) as usize;
        if let Some(c) = self.level_memo.get(&key) {
            return Ok(Arc::clone(c));
        }
        let canon = g.enter(|g| {
            // Rebuild with canonical children first (bottom-up).
            let rebuilt: Arc<Level> = match l.as_ref() {
                Level::Zero | Level::Param(_) | Level::MVar(_) => Arc::clone(l),
                Level::Succ(a) => Arc::new(Level::Succ(self.intern_level(a, g)?)),
                Level::Max(a, b) => Arc::new(Level::Max(
                    self.intern_level(a, g)?,
                    self.intern_level(b, g)?,
                )),
                Level::IMax(a, b) => Arc::new(Level::IMax(
                    self.intern_level(a, g)?,
                    self.intern_level(b, g)?,
                )),
            };
            let h = Level::hash_val(&rebuilt, g)?;
            let bucket = self.levels.entry(h).or_default();
            for existing in bucket.iter() {
                // With canonical children this short-circuits on ptr_eq.
                if Level::structural_eq(existing, &rebuilt, g)? {
                    return Ok(Arc::clone(existing));
                }
            }
            bucket.push(Arc::clone(&rebuilt));
            Ok(rebuilt)
        })?;
        self.level_memo.insert(key, Arc::clone(&canon));
        Ok(canon)
    }

    /// Canonicalize an expr bottom-up. Returns the shared canonical `Arc`
    /// for `e`'s structural value. Guarded recursion (untrusted depth).
    pub fn intern_expr(
        &mut self,
        e: &Arc<Expr>,
        g: &mut RecGuard,
    ) -> Result<Arc<Expr>, KernelError> {
        let key = Arc::as_ptr(e) as usize;
        if let Some(c) = self.expr_memo.get(&key) {
            return Ok(Arc::clone(c));
        }
        let canon = g.enter(|g| {
            // Rebuild with canonical children/levels first (bottom-up).
            // Smart constructors recompute `ExprData`, which is a pure
            // function of children + scalar fields, so the rebuilt node's
            // data equals the original's.
            let rebuilt: Arc<Expr> = match e.node() {
                ExprNode::BVar { .. }
                | ExprNode::FVar { .. }
                | ExprNode::MVar { .. }
                | ExprNode::Lit(_) => Arc::clone(e),
                ExprNode::Sort { level } => Expr::sort(self.intern_level(level, g)?, g)?,
                ExprNode::Const { name, levels } => {
                    let ls = levels
                        .iter()
                        .map(|l| self.intern_level(l, g))
                        .collect::<Result<Vec<_>, _>>()?;
                    Expr::const_(Arc::clone(name), ls, g)?
                }
                ExprNode::App { f, arg } => {
                    Expr::app(self.intern_expr(f, g)?, self.intern_expr(arg, g)?)
                }
                ExprNode::Lam {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => Expr::lam(
                    Arc::clone(binder_name),
                    self.intern_expr(binder_type, g)?,
                    self.intern_expr(body, g)?,
                    *binder_info,
                ),
                ExprNode::ForallE {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } => Expr::forall_e(
                    Arc::clone(binder_name),
                    self.intern_expr(binder_type, g)?,
                    self.intern_expr(body, g)?,
                    *binder_info,
                ),
                ExprNode::LetE {
                    decl_name,
                    ty,
                    value,
                    body,
                    non_dep,
                } => Expr::let_e(
                    Arc::clone(decl_name),
                    self.intern_expr(ty, g)?,
                    self.intern_expr(value, g)?,
                    self.intern_expr(body, g)?,
                    *non_dep,
                ),
                ExprNode::MData { data, expr } => {
                    Expr::mdata(data.clone(), self.intern_expr(expr, g)?)
                }
                ExprNode::Proj {
                    type_name,
                    idx,
                    structure,
                } => Expr::proj(
                    Arc::clone(type_name),
                    idx.clone(),
                    self.intern_expr(structure, g)?,
                ),
            };
            let h = rebuilt.data().hash();
            let bucket = self.exprs.entry(h).or_default();
            for existing in bucket.iter() {
                // `structural_eq` compares every field and short-circuits on
                // ptr_eq children — effectively shallow here.
                if Expr::structural_eq(existing, &rebuilt, g)? {
                    return Ok(Arc::clone(existing));
                }
            }
            bucket.push(Arc::clone(&rebuilt));
            Ok(rebuilt)
        })?;
        self.expr_memo.insert(key, Arc::clone(&canon));
        Ok(canon)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Level, RecGuard};
    use std::sync::Arc;

    fn name(s: &str) -> Arc<crate::Name> {
        Arc::new(crate::Name::Str {
            parent: Arc::new(crate::Name::Anonymous),
            part: s.to_string(),
        })
    }

    use crate::Expr;

    fn nat_const(g: &mut RecGuard) -> Arc<Expr> {
        Expr::const_(name("Nat"), vec![], g).unwrap()
    }

    #[test]
    fn level_merges_structurally_equal_distinct_pointers() {
        let mut it = Interner::new();
        let mut g = RecGuard::new();
        // Two independently-built `Succ Zero`s — structurally equal, distinct Arcs.
        let a = Arc::new(Level::Succ(Arc::new(Level::Zero)));
        let b = Arc::new(Level::Succ(Arc::new(Level::Zero)));
        assert!(!Arc::ptr_eq(&a, &b));
        let ca = it.intern_level(&a, &mut g).unwrap();
        let cb = it.intern_level(&b, &mut g).unwrap();
        assert!(
            Arc::ptr_eq(&ca, &cb),
            "equal levels must share one canonical Arc"
        );
        assert!(Level::structural_eq(&a, &ca, &mut g).unwrap());
    }

    #[test]
    fn level_distinct_params_not_merged() {
        let mut it = Interner::new();
        let mut g = RecGuard::new();
        let a = Arc::new(Level::Param(name("u")));
        let b = Arc::new(Level::Param(name("v")));
        let ca = it.intern_level(&a, &mut g).unwrap();
        let cb = it.intern_level(&b, &mut g).unwrap();
        assert!(!Arc::ptr_eq(&ca, &cb));
    }

    #[test]
    fn level_idempotent() {
        let mut it = Interner::new();
        let mut g = RecGuard::new();
        let a = Arc::new(Level::Succ(Arc::new(Level::Zero)));
        let ca = it.intern_level(&a, &mut g).unwrap();
        let cca = it.intern_level(&ca, &mut g).unwrap();
        assert!(
            Arc::ptr_eq(&ca, &cca),
            "interning a canonical level is a no-op"
        );
    }

    #[test]
    fn expr_merges_structurally_equal_distinct_pointers() {
        let mut it = Interner::new();
        let mut g = RecGuard::new();
        // f x built twice, independently → structurally equal, distinct Arcs.
        let a = Expr::app(nat_const(&mut g), nat_const(&mut g));
        let b = Expr::app(nat_const(&mut g), nat_const(&mut g));
        assert!(!Arc::ptr_eq(&a, &b));
        let ca = it.intern_expr(&a, &mut g).unwrap();
        let cb = it.intern_expr(&b, &mut g).unwrap();
        assert!(
            Arc::ptr_eq(&ca, &cb),
            "equal exprs must share one canonical Arc"
        );
    }

    #[test]
    fn expr_shares_common_subterms() {
        let mut it = Interner::new();
        let mut g = RecGuard::new();
        // App(Nat, Nat): after interning, both children are the same Arc.
        let e = Expr::app(nat_const(&mut g), nat_const(&mut g));
        let c = it.intern_expr(&e, &mut g).unwrap();
        let f = Expr::get_app_fn(&c); // the function child
        let args = Expr::get_app_args(&c);
        assert!(
            Arc::ptr_eq(f, &args[0]),
            "identical subterms collapse to one Arc"
        );
    }

    #[test]
    fn expr_preserves_structure_and_data() {
        let mut it = Interner::new();
        let mut g = RecGuard::new();
        let e = Expr::app(nat_const(&mut g), nat_const(&mut g));
        let c = it.intern_expr(&e, &mut g).unwrap();
        assert!(Expr::structural_eq(&e, &c, &mut g).unwrap());
        assert_eq!(e.data().hash(), c.data().hash());
    }

    #[test]
    fn expr_idempotent() {
        let mut it = Interner::new();
        let mut g = RecGuard::new();
        let e = Expr::app(nat_const(&mut g), nat_const(&mut g));
        let c = it.intern_expr(&e, &mut g).unwrap();
        let cc = it.intern_expr(&c, &mut g).unwrap();
        assert!(Arc::ptr_eq(&c, &cc));
    }

    #[test]
    fn expr_deep_chain_no_stack_overflow() {
        // A left-nested app chain deep enough to blow a naive stack;
        // RecGuard grows the stack so this returns Ok, and a second
        // identical chain dedups to the same Arc.
        let mut it = Interner::new();
        let mut g = RecGuard::new();
        let build = |g: &mut RecGuard| {
            let mut e = nat_const(g);
            for _ in 0..20_000 {
                e = Expr::app(e, nat_const(g));
            }
            e
        };
        let a = build(&mut g);
        let b = build(&mut g);
        let ca = it.intern_expr(&a, &mut g).unwrap();
        let cb = it.intern_expr(&b, &mut g).unwrap();
        assert!(Arc::ptr_eq(&ca, &cb));
    }
}
