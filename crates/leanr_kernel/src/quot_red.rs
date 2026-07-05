//! Quotient recursor reduction. A verbatim port of the oracle's
//! `quot_reduce_rec` (src/kernel/quot.h:39-70). The kernel treats
//! `Quot.lift` and `Quot.ind` as normalizer extensions: an application
//! whose `Quot.mk`-position argument whnfs to a fully-applied `Quot.mk`
//! reduces by feeding the wrapped value to the lift/ind function.
//!
//! The oracle passes `whnf` as a template callback; here it is a closure
//! borrowing the `TypeChecker`, so the function is generic over an
//! `FnMut` whnf and returns `Result` (whnf may raise a `KernelError`).

use std::sync::Arc;

use crate::{Expr, ExprNode, KernelError, Name};

fn mk_name2(a: &str, b: &str) -> Arc<Name> {
    Arc::new(Name::Str {
        parent: Arc::new(Name::Str {
            parent: Arc::new(Name::Anonymous),
            part: a.to_string(),
        }),
        part: b.to_string(),
    })
}

fn const_name(e: &Arc<Expr>) -> Option<&Arc<Name>> {
    match e.node() {
        ExprNode::Const { name, .. } => Some(name),
        _ => None,
    }
}

/// oracle: quot.h:39-70 (`quot_reduce_rec`). Try to reduce a `Quot.lift`
/// or `Quot.ind` application `e`; `whnf` reduces the major (`Quot.mk`)
/// argument. Argument positions are the header's `mk_pos`/`arg_pos`
/// (lift: `mk` at arg 5, `f` at arg 3; ind: `mk` at arg 4, `f` at arg 3
/// — all 0-based).
pub(crate) fn quot_reduce_rec<F>(
    e: &Arc<Expr>,
    mut whnf: F,
) -> Result<Option<Arc<Expr>>, KernelError>
where
    F: FnMut(&Arc<Expr>) -> Result<Arc<Expr>, KernelError>,
{
    // quot.h:40-42.
    let fn0 = Expr::get_app_fn(e);
    let name = match const_name(fn0) {
        Some(n) => n,
        None => return Ok(None),
    };
    // quot.h:45-53.
    let quot_lift = mk_name2("Quot", "lift");
    let quot_ind = mk_name2("Quot", "ind");
    let (mk_pos, arg_pos): (usize, usize) = if name == &quot_lift {
        (5, 3)
    } else if name == &quot_ind {
        (4, 3)
    } else {
        return Ok(None);
    };
    // quot.h:54-57.
    let args = Expr::get_app_args(e);
    if args.len() <= mk_pos {
        return Ok(None);
    }
    // quot.h:59-62: the mk-position arg must whnf to `Quot.mk _ _ _`.
    let mk = whnf(&args[mk_pos])?;
    let mk_fn = Expr::get_app_fn(&mk);
    let mk_args = Expr::get_app_args(&mk);
    let quot_mk = mk_name2("Quot", "mk");
    if const_name(mk_fn) != Some(&quot_mk) || mk_args.len() != 3 {
        return Ok(None);
    }
    // quot.h:64-69: `r := f (app_arg mk)`, then reapply the spine tail
    // past the eliminator arity (`mk_pos + 1`).
    let f = Arc::clone(&args[arg_pos]);
    let a = Arc::clone(&mk_args[2]); // app_arg(mk): the wrapped value
    let mut r = Expr::app(f, a);
    let elim_arity = mk_pos + 1;
    if args.len() > elim_arity {
        r = Expr::mk_app_spine(r, &args[elim_arity..]);
    }
    Ok(Some(r))
}
