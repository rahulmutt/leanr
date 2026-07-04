use std::fmt;
use std::mem;
use std::sync::Arc;

use crate::{Int, Level, Name, Nat};

/// Binder annotation (oracle: src/Lean/Expr.lean:71-80).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinderInfo {
    Default,
    Implicit,
    StrictImplicit,
    InstImplicit,
}

/// Literal (oracle: src/Lean/Expr.lean:18-23).
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Literal {
    NatVal(Nat),
    StrVal(String),
}

/// A value in expression metadata (oracle: src/Lean/Data/KVMap.lean:18-25).
/// `ofSyntax` is not represented: the decoder rejects it as unsupported
/// in M1a; the stdlib sweep (Task 8) is the arbiter of whether real
/// kernel-relevant terms ever carry Syntax metadata.
#[derive(Debug, Clone)]
pub enum DataValue {
    OfString(String),
    OfBool(bool),
    OfName(Arc<Name>),
    OfNat(Nat),
    OfInt(Int),
}

/// Expression metadata map (oracle: src/Lean/Data/KVMap.lean:71-73; a
/// single-field structure, so its runtime representation is the entry
/// list itself).
#[derive(Debug, Clone, Default)]
pub struct KVMap(pub Vec<(Arc<Name>, DataValue)>);

/// Kernel expression (oracle: src/Lean/Expr.lean:321-471). The oracle
/// stores a computed `data` u64 per node (hash, flags, loose-bvar
/// range); we drop it on decode — M1b reintroduces cached metadata
/// behind this same enum.
///
/// No derived Eq/Hash (see `Level`); `Drop` is iterative because term
/// depth is attacker-controlled. Manual iterative Debug impl (see Name for
/// pattern): depth is attacker-controlled and recursion is forbidden.
pub enum Expr {
    BVar {
        idx: Nat,
    },
    FVar {
        id: Arc<Name>,
    },
    MVar {
        id: Arc<Name>,
    },
    Sort {
        level: Arc<Level>,
    },
    Const {
        name: Arc<Name>,
        levels: Vec<Arc<Level>>,
    },
    App {
        f: Arc<Expr>,
        arg: Arc<Expr>,
    },
    Lam {
        binder_name: Arc<Name>,
        binder_type: Arc<Expr>,
        body: Arc<Expr>,
        binder_info: BinderInfo,
    },
    ForallE {
        binder_name: Arc<Name>,
        binder_type: Arc<Expr>,
        body: Arc<Expr>,
        binder_info: BinderInfo,
    },
    LetE {
        decl_name: Arc<Name>,
        ty: Arc<Expr>,
        value: Arc<Expr>,
        body: Arc<Expr>,
        non_dep: bool,
    },
    Lit(Literal),
    MData {
        data: KVMap,
        expr: Arc<Expr>,
    },
    Proj {
        type_name: Arc<Name>,
        idx: Nat,
        structure: Arc<Expr>,
    },
}

/// Manual (non-derived) impl: iterative formatting instead of recursing
/// into Arc children, so it stays safe on adversarially deep chains.
/// Renders as `Expr::BVar { .. }`, etc.
impl fmt::Debug for Expr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Expr::BVar { idx } => write!(f, "Expr::BVar {{ idx: {:?} }}", idx),
            Expr::FVar { id } => write!(f, "Expr::FVar {{ id: {:?} }}", id),
            Expr::MVar { id } => write!(f, "Expr::MVar {{ id: {:?} }}", id),
            Expr::Sort { level: _ } => f.write_str("Expr::Sort { level: .. }"),
            Expr::Const { name, levels: _ } => {
                write!(f, "Expr::Const {{ name: {:?}, levels: .. }}", name)
            }
            Expr::App { f: _, arg: _ } => f.write_str("Expr::App { f: .., arg: .. }"),
            Expr::Lam {
                binder_name,
                binder_type: _,
                body: _,
                binder_info,
            } => {
                write!(f, "Expr::Lam {{ binder_name: {:?}, binder_type: .., body: .., binder_info: {:?} }}", binder_name, binder_info)
            }
            Expr::ForallE {
                binder_name,
                binder_type: _,
                body: _,
                binder_info,
            } => {
                write!(f, "Expr::ForallE {{ binder_name: {:?}, binder_type: .., body: .., binder_info: {:?} }}", binder_name, binder_info)
            }
            Expr::LetE {
                decl_name,
                ty: _,
                value: _,
                body: _,
                non_dep,
            } => {
                write!(
                    f,
                    "Expr::LetE {{ decl_name: {:?}, ty: .., value: .., body: .., non_dep: {} }}",
                    decl_name, non_dep
                )
            }
            Expr::Lit(lit) => write!(f, "Expr::Lit({:?})", lit),
            Expr::MData { data: _, expr: _ } => f.write_str("Expr::MData { data: .., expr: .. }"),
            Expr::Proj {
                type_name,
                idx,
                structure: _,
            } => {
                write!(
                    f,
                    "Expr::Proj {{ type_name: {:?}, idx: {:?}, structure: .. }}",
                    type_name, idx
                )
            }
        }
    }
}

impl Drop for Expr {
    fn drop(&mut self) {
        let mut stack: Vec<Arc<Expr>> = Vec::new();
        take_expr_children(self, &mut stack);
        while let Some(node) = stack.pop() {
            if let Ok(mut owned) = Arc::try_unwrap(node) {
                take_expr_children(&mut owned, &mut stack);
            }
        }
    }
}

fn take_expr_children(e: &mut Expr, stack: &mut Vec<Arc<Expr>>) {
    let leaf = || {
        Arc::new(Expr::BVar {
            idx: Nat::from(0u64),
        })
    };
    match e {
        Expr::BVar { .. }
        | Expr::FVar { .. }
        | Expr::MVar { .. }
        | Expr::Sort { .. }
        | Expr::Const { .. }
        | Expr::Lit(_) => {}
        Expr::App { f, arg } => {
            stack.push(mem::replace(f, leaf()));
            stack.push(mem::replace(arg, leaf()));
        }
        Expr::Lam {
            binder_type, body, ..
        }
        | Expr::ForallE {
            binder_type, body, ..
        } => {
            stack.push(mem::replace(binder_type, leaf()));
            stack.push(mem::replace(body, leaf()));
        }
        Expr::LetE {
            ty, value, body, ..
        } => {
            stack.push(mem::replace(ty, leaf()));
            stack.push(mem::replace(value, leaf()));
            stack.push(mem::replace(body, leaf()));
        }
        Expr::MData { expr, .. }
        | Expr::Proj {
            structure: expr, ..
        } => {
            stack.push(mem::replace(expr, leaf()));
        }
    }
}
