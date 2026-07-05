//! Kernel local context: tracks fresh free variables introduced while
//! checking under a binder (each with its declared type/binder-info, or
//! a let-value), and rebuilds a term's Π/λ telescope over them once the
//! body has been checked in that extended context.
//!
//! Oracle: src/kernel/local_ctx.h, src/kernel/local_ctx.cpp (pinned
//! githash b4812ae53eea93439ad5dce5a5c26591c31cb697, toolchain
//! leanprover/lean4:v4.32.0-rc1 — see ARCHITECTURE.md for the pin).
//!
//! Panic-path safety (`decl_for` below): the invariant is one of SLICE
//! provenance, not fvar-node absence. The decoder CAN produce
//! `Expr::fvar` from attacker bytes (leanr_olean's interp.rs decodes
//! ctor tag 1 as `Expr::fvar(name)` with no rejection), so decoded
//! expressions may contain arbitrary FVar nodes. But the `fvars` SLICES
//! passed to `mk_pi`/`mk_lambda` are built exclusively by
//! kernel-internal callers (the type checker) out of the return values
//! of this module's own `mk_local_decl`/`mk_let_decl` — never out of
//! decoded expressions. A decoded FVar reaching the checker is looked up
//! via `LocalContext::get`, whose `None` feeds a `KernelError` path in
//! the caller; it never lands in an `fvars` slice. Additionally, the
//! admission pipeline rejects any declaration whose type/value contains
//! ANY fvar before checking begins (`KernelError::HasFVars`; oracle:
//! environment.cpp:87-100 `check_no_metavar_no_fvar`), so decoded FVar
//! nodes are stopped at admission. That two-layer invariant is what lets
//! `mk_binding` below treat a mismatched `fvars` entry as a
//! kernel-internal contract violation (documented panic, per the same
//! precedent as `name.rs`'s `.expect(...)` and `level.rs`'s
//! `unreachable!(...)`) rather than untrusted input needing a `Result`
//! (no existing `KernelError` variant fits, and the variant list is
//! frozen by Task 1's error.rs port).

use std::collections::HashMap;
use std::sync::Arc;

use crate::{abstract_fvars, BinderInfo, Expr, ExprNode, KernelError, Name, Nat, RecGuard};

/// oracle: local_ctx.h:20-47 (`local_decl` — the `cdecl`/`ldecl`
/// inductive in the header comment). `id` is the fresh fvar id
/// (`local_decl::get_name`); `binder_name` is the user-facing name
/// (`get_user_name`) kept purely for pretty-printing/re-elaboration, not
/// looked at by the kernel's own equality/reduction.
pub struct LocalDecl {
    pub id: Arc<Name>,
    pub binder_name: Arc<Name>,
    pub ty: Arc<Expr>,
    pub binder_info: BinderInfo,
    pub value: Option<Arc<Expr>>,
}

/// oracle: local_ctx.h:49+ (`local_ctx` — insertion-ordered map from
/// fvar id to `local_decl`). `decls` preserves declaration order (the
/// order `mk_pi`/`mk_lambda`'s telescope-folding relies on); `index`
/// gives O(1) lookup by id.
#[derive(Default)]
pub struct LocalContext {
    decls: Vec<LocalDecl>,
    index: HashMap<Arc<Name>, usize>,
}

/// Fresh ids `_kernel_fresh.<n>` (oracle: type_checker.cpp:24
/// `g_kernel_fresh`, constructed as `name_generator(*g_kernel_fresh)` at
/// type_checker.cpp:46; `util/name_generator.cpp:16-30` — `m_next_idx`
/// starts at 0 and each `next()` call returns `name(prefix, idx)` then
/// increments, so the first id minted is `_kernel_fresh.0`).
#[derive(Default)]
pub struct FVarIdGen {
    next: u64,
}

/// Builds the next `_kernel_fresh.<n>` name and advances the counter.
/// Kept as a free function (not a public method) since the brief's
/// interface for `FVarIdGen` exposes only the `next: u64` field — the
/// two `LocalContext` methods below are the only callers, and both live
/// in this module.
fn fresh_fvar_id(gen: &mut FVarIdGen) -> Arc<Name> {
    let idx = gen.next;
    gen.next += 1;
    let prefix = Arc::new(Name::Str {
        parent: Arc::new(Name::Anonymous),
        part: "_kernel_fresh".to_string(),
    });
    Arc::new(Name::Num {
        parent: prefix,
        part: Nat::from(idx),
    })
}

impl LocalContext {
    /// Record `decl` and return its `Expr::fvar` reference (oracle:
    /// `local_decl::mk_ref`, local_ctx.cpp:39-41 — `mk_fvar(get_name())`).
    fn push(&mut self, decl: LocalDecl) -> Arc<Expr> {
        let id = Arc::clone(&decl.id);
        self.index.insert(Arc::clone(&id), self.decls.len());
        self.decls.push(decl);
        Expr::fvar(id)
    }

    /// oracle: local_ctx.h:64-66 (`mk_local_decl(name_generator&, name
    /// const&, expr const&, binder_info)` — the `cdecl` overload).
    pub fn mk_local_decl(
        &mut self,
        gen: &mut FVarIdGen,
        binder_name: &Arc<Name>,
        ty: Arc<Expr>,
        bi: BinderInfo,
    ) -> Arc<Expr> {
        let id = fresh_fvar_id(gen);
        self.push(LocalDecl {
            id,
            binder_name: Arc::clone(binder_name),
            ty,
            binder_info: bi,
            value: None,
        })
    }

    /// oracle: local_ctx.h:68-70 (`mk_local_decl(name_generator&, name
    /// const&, expr const&, expr const& value)` — the `ldecl` overload).
    pub fn mk_let_decl(
        &mut self,
        gen: &mut FVarIdGen,
        binder_name: &Arc<Name>,
        ty: Arc<Expr>,
        value: Arc<Expr>,
    ) -> Arc<Expr> {
        let id = fresh_fvar_id(gen);
        self.push(LocalDecl {
            id,
            binder_name: Arc::clone(binder_name),
            ty,
            // oracle: local_ctx.cpp:35-37 — `get_info` reads the packed
            // runtime object regardless of cdecl/ldecl, but `mk_binding`
            // below never reads `binder_info` for a let-bound decl (its
            // `decl.value.is_some()` branch takes the `mk_let` path
            // unconditionally), so this value is inert; `Default` is
            // just a placeholder.
            binder_info: BinderInfo::Default,
            value: Some(value),
        })
    }

    /// oracle: local_ctx.h:76-78 (`get_local_decl`/`find_local_decl`).
    pub fn get(&self, fvar_id: &Arc<Name>) -> Option<&LocalDecl> {
        self.index.get(fvar_id).map(|&i| &self.decls[i])
    }

    /// Support for the type checker's `flet<local_ctx> save_lctx(m_lctx,
    /// m_lctx)` idiom (type_checker.cpp:117/135/199/693 etc.): the checker
    /// extends the context under a binder and must pop those decls again
    /// on the way out. `save` records the current decl count; `restore`
    /// drops every decl added since (fvar ids are globally unique via
    /// `FVarIdGen`, so a dropped id is never reintroduced — the truncation
    /// is exact). `pub(crate)`: only the in-crate checker uses it.
    pub(crate) fn save(&self) -> usize {
        self.decls.len()
    }

    /// Restore to a `save` checkpoint, removing later decls from both the
    /// insertion-ordered `decls` and the id `index`.
    pub(crate) fn restore(&mut self, checkpoint: usize) {
        for decl in self.decls.drain(checkpoint..) {
            self.index.remove(&decl.id);
        }
    }

    /// Look up the declaration for a telescope entry, or panic — see the
    /// module doc comment for why this is a documented internal-contract
    /// panic rather than a `Result`.
    fn decl_for<'a>(&'a self, fvar: &Arc<Expr>) -> &'a LocalDecl {
        match fvar.node() {
            ExprNode::FVar { id } => self.get(id).unwrap_or_else(|| {
                panic!("LocalContext::mk_pi/mk_lambda: fvar not declared in this context")
            }),
            _ => panic!("LocalContext::mk_pi/mk_lambda: fvars entry is not an Expr::fvar"),
        }
    }

    /// oracle: local_ctx.h:94-99 / local_ctx.cpp:93-121
    /// (`mk_binding<is_lambda=false>` via the `mk_pi` wrapper) — rebuild
    /// a Π-telescope over `fvars` around `e`.
    pub fn mk_pi(
        &self,
        fvars: &[Arc<Expr>],
        e: &Arc<Expr>,
        g: &mut RecGuard,
    ) -> Result<Arc<Expr>, KernelError> {
        self.mk_binding(fvars, e, false, g)
    }

    /// oracle: local_ctx.h:94-99 / local_ctx.cpp:93-121
    /// (`mk_binding<is_lambda=true>` via the `mk_lambda` wrapper).
    pub fn mk_lambda(
        &self,
        fvars: &[Arc<Expr>],
        e: &Arc<Expr>,
        g: &mut RecGuard,
    ) -> Result<Arc<Expr>, KernelError> {
        self.mk_binding(fvars, e, true, g)
    }

    /// oracle: local_ctx.cpp:93-115 (`local_ctx::mk_binding`). The
    /// oracle abstracts the WHOLE body once up front
    /// (`r = abstract(b, num, fvars)`, local_ctx.cpp:95) and then, right
    /// to left, wraps each binder using its decl's type abstracted
    /// against only the *earlier* fvars (`abstract(decl.get_type(), i,
    /// fvars)`, local_ctx.cpp:101/104/107 — `i` limits `abstract` to
    /// `fvars[0..i)`, per `abstract.cpp:14-27`'s own `n` parameter).
    ///
    /// We abstract the body one fvar at a time instead, as the fold
    /// reaches it (`abstract_fvars(&r, &[fvars[i]], g)`), rather than all
    /// `num` of them up front. This is equivalent: `abstract_fvars`'s
    /// walker (subst.rs) already bumps its binder-depth `offset` by one
    /// crossing into an already-wrapped `Lam`/`ForallE`/`LetE` body, so
    /// abstracting `fvars[i]` alone out of the partially-wrapped `r`
    /// lands it at the same bvar index it would have gotten from the
    /// oracle's single upfront `abstract(b, num, fvars)` call — verified
    /// against `mk_pi_roundtrips_a_telescope` below. Trades one extra
    /// `O(size(r))` walk per fvar for staying entirely inside Task 4's
    /// existing `abstract_fvars` instead of a new tree-walker.
    ///
    /// `non_dep` is always `false` for the rebuilt `LetE`, matching the
    /// oracle: local_ctx.cpp:107 calls the 4-arg `::lean::mk_let(name,
    /// type, value, r)`, whose default (expr.h:225) is `nondep = false`
    /// — `local_ctx::mk_binding` never computes a real `non_dep` bit.
    fn mk_binding(
        &self,
        fvars: &[Arc<Expr>],
        e: &Arc<Expr>,
        is_lambda: bool,
        g: &mut RecGuard,
    ) -> Result<Arc<Expr>, KernelError> {
        let mut r = Arc::clone(e);
        let mut i = fvars.len();
        while i > 0 {
            i -= 1;
            r = abstract_fvars(&r, std::slice::from_ref(&fvars[i]), g)?;
            let decl = self.decl_for(&fvars[i]);
            let ty = abstract_fvars(&decl.ty, &fvars[..i], g)?;
            r = if let Some(value) = &decl.value {
                let value = abstract_fvars(value, &fvars[..i], g)?;
                Expr::let_e(Arc::clone(&decl.binder_name), ty, value, r, false)
            } else if is_lambda {
                Expr::lam(Arc::clone(&decl.binder_name), ty, r, decl.binder_info)
            } else {
                Expr::forall_e(Arc::clone(&decl.binder_name), ty, r, decl.binder_info)
            };
        }
        Ok(r)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BinderInfo, Expr, ExprNode, Literal, Name, Nat, RecGuard};
    use std::sync::Arc;

    // `Name::from_str` doesn't exist (see name.rs / every prior task's
    // own test helpers): build a single-component name with an
    // `Anonymous` parent by hand instead of the brief's `Name::from_str`.
    fn nm(s: &str) -> Arc<Name> {
        Arc::new(Name::Str {
            parent: Arc::new(Name::Anonymous),
            part: s.to_string(),
        })
    }

    #[test]
    fn mk_pi_roundtrips_a_telescope() {
        let mut g = RecGuard::new();
        let mut lctx = LocalContext::default();
        let mut gen = FVarIdGen::default();
        let nat = Expr::const_(nm("Nat"), vec![], &mut g).unwrap();
        // x : Nat, y : (x = x)-shaped dependent type stand-in: Vec x
        let x = lctx.mk_local_decl(&mut gen, &nm("x"), Arc::clone(&nat), BinderInfo::Default);
        let vec_x = Expr::app(
            Expr::const_(nm("Vec"), vec![], &mut g).unwrap(),
            Arc::clone(&x),
        );
        let y = lctx.mk_local_decl(&mut gen, &nm("y"), Arc::clone(&vec_x), BinderInfo::Implicit);
        let body = Expr::app(Arc::clone(&y), Arc::clone(&x));
        let pi = lctx
            .mk_pi(&[Arc::clone(&x), Arc::clone(&y)], &body, &mut g)
            .unwrap();
        // Result must be closed and shaped Π (x : Nat), Π {y : Vec #0}, #0 #1
        assert_eq!(pi.data().loose_bvar_range(), 0);
        assert!(!pi.data().has_fvar());
        let ExprNode::ForallE {
            binder_type, body, ..
        } = pi.node()
        else {
            panic!()
        };
        assert!(Expr::structural_eq(binder_type, &nat, &mut g).unwrap());
        let ExprNode::ForallE {
            binder_info,
            binder_type: bt2,
            body: b2,
            ..
        } = body.node()
        else {
            panic!()
        };
        assert_eq!(*binder_info, BinderInfo::Implicit);
        assert_eq!(bt2.data().loose_bvar_range(), 1); // Vec #0
        assert_eq!(b2.data().loose_bvar_range(), 2); // #0 #1
    }

    #[test]
    fn fresh_ids_never_collide() {
        // Brief's draft declared an unused `let mut g = RecGuard::new();`
        // here (copy-pasted boilerplate from the other test — this test
        // never calls anything that takes a `RecGuard`): dropped, since
        // `mise run lint`'s `-D warnings` gate turns the resulting
        // unused-variable/unused-mut warnings into hard errors.
        let mut gen = FVarIdGen::default();
        let mut lctx = LocalContext::default();
        let t = Expr::lit(Literal::NatVal(Nat::from(0u64)));
        let a = lctx.mk_local_decl(&mut gen, &nm("x"), Arc::clone(&t), BinderInfo::Default);
        let b = lctx.mk_local_decl(&mut gen, &nm("x"), t, BinderInfo::Default);
        let (ExprNode::FVar { id: ia }, ExprNode::FVar { id: ib }) = (a.node(), b.node()) else {
            panic!()
        };
        assert_ne!(ia, ib);
        assert!(lctx.get(ia).is_some() && lctx.get(ib).is_some());
    }
}
