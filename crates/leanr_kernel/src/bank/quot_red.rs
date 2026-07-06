//! Quotient recursor reduction. Id-twin of `crate::quot_red` (a verbatim
//! port of the oracle's `quot_reduce_rec`, src/kernel/quot.h:39-70). The
//! kernel treats `Quot.lift` and `Quot.ind` as normalizer extensions: an
//! application whose `Quot.mk`-position argument whnfs to a
//! fully-applied `Quot.mk` reduces by feeding the wrapped value to the
//! lift/ind function.
//!
//! The Arc port keeps `whnf` as a bare `FnMut` closure and decomposes
//! app spines via free `Expr::get_app_fn`/`get_app_args` functions that
//! need no store — an `Arc<Expr>` decodes itself. In id space, the same
//! app-spine ops need `&Store` access, so a second borrow held alongside
//! an `FnMut` closure that already captures `&mut TypeChecker`
//! (exclusively, for the closure's whole lifetime) is not expressible
//! without a borrow-checker conflict. Bundling every operation this
//! function needs behind one `&mut impl QuotCtx` handle avoids the
//! split-borrow problem while keeping this file free of a `TypeChecker`
//! import — the same decoupling the Arc file's generic-`FnMut` design
//! achieves, adapted to id space.
use super::{ExprId, NameId};
use crate::KernelError;

/// The capability `quot_reduce_rec` needs from its caller (`TypeChecker`
/// implements this in `bank/tc.rs`).
// `#[allow(dead_code)]`: this module lands one commit (4a) before its
// only consumer (`bank::tc::TypeChecker`, migration Task 4's main
// commit) — dropped once that impl exists.
#[allow(dead_code)]
pub(crate) trait QuotCtx {
    fn get_app_fn(&self, e: ExprId) -> ExprId;
    fn get_app_args(&self, e: ExprId) -> Vec<ExprId>;
    /// The `Const`'s name if `e` is a `Const` node with a non-anonymous
    /// name, else `None` — collapses "not a `Const`" and "`Const` with
    /// an anonymous name" into one bucket, which is exactly what every
    /// caller below needs (an anonymous name can never equal one of the
    /// three real `Quot.*` targets).
    fn const_name(&self, e: ExprId) -> Option<NameId>;
    fn mk_app_spine(&mut self, f: ExprId, args: &[ExprId]) -> Result<ExprId, KernelError>;
    fn whnf(&mut self, e: ExprId) -> Result<ExprId, KernelError>;
    /// `(Quot.lift, Quot.ind, Quot.mk)`, interned fresh each call —
    /// matching the Arc port's own `mk_name2` calls, which likewise
    /// build fresh (unshared) `Arc<Name>`s on every invocation rather
    /// than caching them.
    fn quot_names(&mut self) -> Result<(NameId, NameId, NameId), KernelError>;
}

/// oracle: quot.h:39-70 (`quot_reduce_rec`). Try to reduce a `Quot.lift`
/// or `Quot.ind` application `e`; `ctx.whnf` reduces the major
/// (`Quot.mk`) argument. Argument positions are the header's
/// `mk_pos`/`arg_pos` (lift: `mk` at arg 5, `f` at arg 3; ind: `mk` at
/// arg 4, `f` at arg 3 — all 0-based).
#[allow(dead_code)] // see `QuotCtx`'s doc comment above
pub(crate) fn quot_reduce_rec<C: QuotCtx>(
    ctx: &mut C,
    e: ExprId,
) -> Result<Option<ExprId>, KernelError> {
    // quot.h:40-42.
    let fn0 = ctx.get_app_fn(e);
    let name = match ctx.const_name(fn0) {
        Some(n) => n,
        None => return Ok(None),
    };
    // quot.h:45-53.
    let (quot_lift, quot_ind, quot_mk) = ctx.quot_names()?;
    let (mk_pos, arg_pos): (usize, usize) = if name == quot_lift {
        (5, 3)
    } else if name == quot_ind {
        (4, 3)
    } else {
        return Ok(None);
    };
    // quot.h:54-57.
    let args = ctx.get_app_args(e);
    if args.len() <= mk_pos {
        return Ok(None);
    }
    // quot.h:59-62: the mk-position arg must whnf to `Quot.mk _ _ _`.
    let mk = ctx.whnf(args[mk_pos])?;
    let mk_fn = ctx.get_app_fn(mk);
    let mk_args = ctx.get_app_args(mk);
    if ctx.const_name(mk_fn) != Some(quot_mk) || mk_args.len() != 3 {
        return Ok(None);
    }
    // quot.h:64-69: `r := f (app_arg mk)`, then reapply the spine tail
    // past the eliminator arity (`mk_pos + 1`).
    let f = args[arg_pos];
    let a = mk_args[2]; // app_arg(mk): the wrapped value
    let mut r = ctx.mk_app_spine(f, std::slice::from_ref(&a))?;
    let elim_arity = mk_pos + 1;
    if args.len() > elim_arity {
        r = ctx.mk_app_spine(r, &args[elim_arity..])?;
    }
    Ok(Some(r))
}

// The Arc port (`crate::quot_red`) has no inline tests of its own — its
// behavior is exercised end-to-end through `tc/tests.rs`'s
// `quot_lift_beta`/`quot_ind_beta` (ported to the dual harness in
// `bank::tc::tests`). This module's `QuotCtx` indirection is new
// machinery the Arc side doesn't have, so it gets its own small direct
// unit tests here (in addition to, not instead of, the ported
// differential tests) covering the two `None`-returning guards that
// don't even reach `TypeChecker::whnf`.
#[cfg(test)]
mod tests {
    use super::*;
    use crate::bank::terms::Node;
    use crate::bank::Store;
    use crate::Nat;

    struct Ctx<'a> {
        st: &'a mut Store,
    }

    fn mk_name2(st: &mut Store, a: &str, b: &str) -> Result<NameId, KernelError> {
        let pa = st.intern_str(None, a)?;
        let p = st.name_str(None, None, pa)?;
        let pb = st.intern_str(None, b)?;
        st.name_str(None, Some(p), pb)
    }

    impl<'a> QuotCtx for Ctx<'a> {
        fn get_app_fn(&self, e: ExprId) -> ExprId {
            let mut cur = e;
            while let Node::App { f, .. } = self.st.expr_node(None, cur) {
                cur = f;
            }
            cur
        }
        fn get_app_args(&self, e: ExprId) -> Vec<ExprId> {
            let mut args = Vec::new();
            let mut cur = e;
            while let Node::App { f, arg } = self.st.expr_node(None, cur) {
                args.push(arg);
                cur = f;
            }
            args.reverse();
            args
        }
        fn const_name(&self, e: ExprId) -> Option<NameId> {
            match self.st.expr_node(None, e) {
                Node::Const { name, .. } => name,
                _ => None,
            }
        }
        fn mk_app_spine(&mut self, f: ExprId, args: &[ExprId]) -> Result<ExprId, KernelError> {
            let mut r = f;
            for &a in args {
                r = self.st.expr_app(None, r, a)?;
            }
            Ok(r)
        }
        fn whnf(&mut self, e: ExprId) -> Result<ExprId, KernelError> {
            Ok(e) // identity whnf suffices for these guard-only tests
        }
        fn quot_names(&mut self) -> Result<(NameId, NameId, NameId), KernelError> {
            Ok((
                mk_name2(self.st, "Quot", "lift")?,
                mk_name2(self.st, "Quot", "ind")?,
                mk_name2(self.st, "Quot", "mk")?,
            ))
        }
    }

    fn const_(st: &mut Store, name: NameId) -> ExprId {
        let no_levels = st.intern_level_list(None, &[]).unwrap();
        st.expr_const(None, Some(name), no_levels).unwrap()
    }

    #[test]
    fn head_not_const_returns_none() {
        let mut st = Store::persistent();
        let e = st.expr_bvar(None, &Nat::from(0u64)).unwrap();
        let mut ctx = Ctx { st: &mut st };
        assert_eq!(quot_reduce_rec(&mut ctx, e).unwrap(), None);
    }

    #[test]
    fn const_head_not_quot_returns_none() {
        let mut st = Store::persistent();
        let f = mk_name2(&mut st, "Foo", "bar").unwrap();
        let e = const_(&mut st, f);
        let mut ctx = Ctx { st: &mut st };
        assert_eq!(quot_reduce_rec(&mut ctx, e).unwrap(), None);
    }

    #[test]
    fn quot_lift_with_too_few_args_returns_none() {
        let mut st = Store::persistent();
        let lift = mk_name2(&mut st, "Quot", "lift").unwrap();
        let head = const_(&mut st, lift);
        // Only 2 args applied; `Quot.lift`'s mk-position is 5 (0-based).
        let a0 = st.expr_bvar(None, &Nat::from(0u64)).unwrap();
        let a1 = st.expr_bvar(None, &Nat::from(1u64)).unwrap();
        let e0 = st.expr_app(None, head, a0).unwrap();
        let e = st.expr_app(None, e0, a1).unwrap();
        let mut ctx = Ctx { st: &mut st };
        assert_eq!(quot_reduce_rec(&mut ctx, e).unwrap(), None);
    }
}
