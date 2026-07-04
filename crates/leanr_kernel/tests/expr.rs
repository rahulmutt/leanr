use std::sync::Arc;

use leanr_kernel::{BinderInfo, Expr, Level, Literal, Name, Nat};

fn bvar(idx: u64) -> Arc<Expr> {
    Arc::new(Expr::BVar {
        idx: Nat::from(idx),
    })
}

#[test]
fn constructing_a_small_term_works() {
    // fun (x : Sort 0) => x  (shape only; no checker yet)
    let lam = Expr::Lam {
        binder_name: Arc::new(Name::Str {
            parent: Arc::new(Name::Anonymous),
            part: "x".to_string(),
        }),
        binder_type: Arc::new(Expr::Sort {
            level: Arc::new(Level::Zero),
        }),
        body: bvar(0),
        binder_info: BinderInfo::Default,
    };
    match lam {
        Expr::Lam {
            binder_info: BinderInfo::Default,
            ..
        } => {}
        _ => panic!("pattern"),
    }
    let _lit = Expr::Lit(Literal::StrVal("hello".to_string()));
}

/// Untrusted input can produce arbitrarily deep terms; Drop must be
/// iterative for every Arc-recursive kernel type.
#[test]
fn deep_expr_and_level_drops_do_not_overflow() {
    const DEPTH: usize = 200_000;
    let mut e = bvar(0);
    for _ in 0..DEPTH {
        e = Arc::new(Expr::App { f: e, arg: bvar(1) });
    }
    // Format debug output to verify it doesn't recurse
    let debug_str = format!("{:?}", e);
    assert!(!debug_str.is_empty());
    drop(e);

    let mut l = Arc::new(Level::Zero);
    for _ in 0..DEPTH {
        l = Arc::new(Level::Succ(l));
    }
    // Format debug output to verify it doesn't recurse
    let debug_str = format!("{:?}", l);
    assert!(!debug_str.is_empty());
    drop(l);
}
