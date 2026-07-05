use std::sync::Arc;

use leanr_kernel::{
    BinderInfo, Expr, ExprNode, Level, Literal, Name, Nat, RecGuard, SourceInfo, Syntax,
};

fn bvar(idx: u64) -> Arc<Expr> {
    Expr::bvar(Nat::from(idx))
}

#[test]
fn constructing_a_small_term_works() {
    // fun (x : Sort 0) => x  (shape only; no checker yet)
    let mut g = RecGuard::new();
    let binder_name = Arc::new(Name::Str {
        parent: Arc::new(Name::Anonymous),
        part: "x".to_string(),
    });
    let binder_type = Expr::sort(Arc::new(Level::Zero), &mut g).unwrap();
    let lam = Expr::lam(binder_name, binder_type, bvar(0), BinderInfo::Default);
    match lam.node() {
        ExprNode::Lam {
            binder_info: BinderInfo::Default,
            ..
        } => {}
        _ => panic!("pattern"),
    }
    let _lit = Expr::lit(Literal::StrVal("hello".to_string()));
}

/// Untrusted input can produce arbitrarily deep terms; Drop must be
/// iterative for every Arc-recursive kernel type.
#[test]
fn deep_expr_and_level_drops_do_not_overflow() {
    const DEPTH: usize = 200_000;
    let mut e = bvar(0);
    for _ in 0..DEPTH {
        e = Expr::app(e, bvar(1));
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

/// `Syntax` is Arc-recursive through `Node.args`; like `Expr`, its Debug
/// and Drop must not recurse into children (node depth is
/// attacker-controlled in untrusted `.olean` bytes).
#[test]
fn deep_syntax_debug_and_drop_do_not_overflow() {
    const DEPTH: usize = 200_000;
    let mut s = Arc::new(Syntax::Missing);
    for _ in 0..DEPTH {
        s = Arc::new(Syntax::Node {
            info: SourceInfo::None,
            kind: Arc::new(Name::Anonymous),
            args: vec![s],
        });
    }
    // Debug must format without recursing into args.
    let debug_str = format!("{:?}", s);
    assert!(debug_str.starts_with("Syntax::Node"));
    drop(s);
}
