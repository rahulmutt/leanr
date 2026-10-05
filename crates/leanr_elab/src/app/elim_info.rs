//! oracle: `ElabElimInfo` / `getElabElimExprInfo` / `getElabElimInfo`
//! (`Lean/Elab/App.lean:976-1053`, v4.33.0-rc1) — where the motive is
//! and which parameters are "major" (elaborated eagerly because they can
//! inform motive inference). Consumed by P2's `elabAsElim?` gate and
//! `ElabElim`. Pure MetaM in the oracle; it lives here because the
//! oracle defines it in `Elab/App.lean`.

use std::collections::HashSet;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};

use crate::app::lval::{app_args, app_fn, node};
use crate::app::state::open_forall_telescope_reducing;
use crate::command::vars::collect_fvars;
use crate::elab::TermElabM;
use crate::error::{ElabError, EliminatorErrorReason as R};

/// oracle: `structure ElabElimInfo` (`App.lean:976-1004`).
#[derive(Debug, Clone)]
pub struct ElabElimInfo {
    /// oracle: `elimExpr` — the eliminator.
    pub elim_expr: ExprId,
    /// oracle: `elimType` — `inferType elimExpr`.
    pub elim_type: ExprId,
    /// oracle: `motivePos` — the motive's index in the telescope.
    pub motive_pos: usize,
    /// oracle: `majorsPos`, ascending. Every index that is neither the
    /// motive nor here is a "minor" premise.
    pub majors_pos: Vec<usize>,
}

/// oracle: `getElabElimInfo` (`App.lean:1052-1053`):
/// `getElabElimExprInfo (← mkConstWithFreshMVarLevels elimName)`.
pub fn get_elab_elim_info(
    elab: &mut TermElabM<'_>,
    name: NameId,
) -> Result<ElabElimInfo, ElabError> {
    let e = elab.mk_const_with_fresh_mvar_levels_of(name)?;
    get_elab_elim_expr_info(elab, e)
}

/// oracle: `getElabElimExprInfo` (`App.lean:1006-1050`). Leaves the
/// ambient `lctx` as it found it (the oracle's `forallTelescopeReducing`
/// scopes).
pub fn get_elab_elim_expr_info(
    elab: &mut TermElabM<'_>,
    elim_expr: ExprId,
) -> Result<ElabElimInfo, ElabError> {
    let elim_type = elab.mctx.infer_type(elim_expr)?;
    let cp = elab.mctx.lctx_checkpoint();
    let r = elim_info_in_telescope(elab, elim_expr, elim_type);
    elab.mctx.lctx_restore(cp);
    r
}

/// The body of `getElabElimExprInfo`'s outer `forallTelescopeReducing`
/// (`App.lean:1009-1050`). Pushes the telescope into the ambient `lctx`;
/// the caller restores it.
fn elim_info_in_telescope(
    elab: &mut TermElabM<'_>,
    elim_expr: ExprId,
    elim_type: ExprId,
) -> Result<ElabElimInfo, ElabError> {
    let (xs, ty) = open_forall_telescope_reducing(elab, elim_type)?;
    // oracle :1010-1013.
    let motive = app_fn(elab, ty);
    let motive_args = app_args(elab, ty);
    if !matches!(node(elab, motive), Node::FVar { .. }) || motive_args.is_empty() {
        return Err(ElabError::Eliminator {
            reason: R::UnexpectedResultingType,
        });
    }
    // oracle :1014-1019 — the inner telescope's checks only; nothing it
    // binds escapes.
    let motive_type = elab.mctx.infer_type(motive)?;
    let cp = elab.mctx.lctx_checkpoint();
    let shape = check_motive_type(elab, motive_type, motive_args.len());
    elab.mctx.lctx_restore(cp);
    shape?;
    // oracle :1020-1021 — `xs.idxOf? motive`.
    let Some(motive_pos) = xs.iter().position(|x| x.fvar == motive) else {
        return Err(ElabError::Eliminator {
            reason: R::UnexpectedEliminatorType,
        });
    };
    // oracle :1026-1032 — fvars of the motive's arguments, closed
    // right-to-left (`foldRevM`) under "x ∈ set ⇒ add fvars(type x)".
    // Right-to-left is what makes one pass a full transitive closure: a
    // binder's type only mentions binders to its left.
    let mut motive_fvars: HashSet<ExprId> = HashSet::new();
    for &a in &motive_args {
        collect_fvars(elab, a, &mut motive_fvars);
    }
    for x in xs.iter().rev() {
        if motive_fvars.contains(&x.fvar) {
            // oracle: `inferType x` — an fvar's decl type, `x.ty`.
            let x_ty = elab.mctx.infer_type(x.fvar)?;
            collect_fvars(elab, x_ty, &mut motive_fvars);
        }
    }
    // oracle :1034-1047.
    let mut majors_pos = Vec::new();
    for (i, x) in xs.iter().enumerate() {
        if i == motive_pos {
            continue;
        }
        // oracle: `x.fvarId!.getType` — the decl type.
        let x_ty = x.ty;
        if motive_fvars.contains(&x.fvar)
            || (is_first_order(elab, x_ty) && mentions_any(elab, x_ty, &motive_fvars))
        {
            majors_pos.push(i);
        }
    }
    Ok(ElabElimInfo {
        elim_expr,
        elim_type,
        motive_pos,
        majors_pos,
    })
}

/// oracle `App.lean:1015-1019`: the motive's type is a telescope of
/// exactly `arity` binders ending in a sort.
fn check_motive_type(
    elab: &mut TermElabM<'_>,
    motive_type: ExprId,
    arity: usize,
) -> Result<(), ElabError> {
    let (params, res) = open_forall_telescope_reducing(elab, motive_type)?;
    if params.len() != arity {
        return Err(ElabError::Eliminator {
            reason: R::UnexpectedMotiveArity,
        });
    }
    if !matches!(node(elab, res), Node::Sort { .. }) {
        return Err(ElabError::Eliminator {
            reason: R::MotiveResultNotSort,
        });
    }
    Ok(())
}

/// The immediate subterms `Expr.find?`/`collectFVars` descend into.
fn children(n: Node) -> impl DoubleEndedIterator<Item = ExprId> {
    let (a, b, c) = match n {
        Node::App { f, arg } => (Some(f), Some(arg), None),
        Node::Lam {
            binder_type, body, ..
        }
        | Node::Forall {
            binder_type, body, ..
        } => (Some(binder_type), Some(body), None),
        Node::LetE {
            ty, value, body, ..
        } => (Some(ty), Some(value), Some(body)),
        Node::MData { expr, .. } => (Some(expr), None, None),
        Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
            (Some(structure), None, None)
        }
        Node::BVar { .. }
        | Node::BVarBig { .. }
        | Node::FVar { .. }
        | Node::MVar { .. }
        | Node::Sort { .. }
        | Node::Const { .. }
        | Node::LitNat { .. }
        | Node::LitStr { .. } => (None, None, None),
    };
    [a, b, c].into_iter().flatten()
}

/// oracle: `Expr.find?` (`Lean/Util/FindExpr.lean`) as a predicate:
/// whether any subterm of `e` (itself included, binder bodies included)
/// satisfies `p`. Iterative, and each shared subterm is visited once
/// (hash-consing makes `ExprId` equality structural equality). `prune`
/// skips a subterm and everything under it.
pub(crate) fn any_subterm(
    elab: &TermElabM<'_>,
    e: ExprId,
    prune: impl Fn(&TermElabM<'_>, ExprId) -> bool,
    mut p: impl FnMut(&TermElabM<'_>, ExprId, &Node) -> bool,
) -> bool {
    let mut seen: HashSet<ExprId> = HashSet::new();
    let mut stack = vec![e];
    while let Some(e) = stack.pop() {
        if !seen.insert(e) || prune(elab, e) {
            continue;
        }
        let n = node(elab, e);
        if p(elab, e, &n) {
            return true;
        }
        // Reversed, so subterms pop in the oracle's left-to-right
        // pre-order (`f` before `a`, domain before body): the order
        // `collect_fvars` reports fvars in.
        stack.extend(children(n).rev());
    }
    false
}

/// Whether `e` contains no free variable (the `hasFVar` data bit).
pub(crate) fn has_no_fvar(elab: &TermElabM<'_>, e: ExprId) -> bool {
    !elab
        .mctx
        .store()
        .expr_data(Some(elab.view.store), e)
        .has_fvar()
}

/// oracle `App.lean:1043`, `isFirstOrder`:
/// `Option.isNone <| e.find? fun e => e.isApp && !e.getAppFn.isConst` —
/// every application anywhere in `e` has a constant head.
fn is_first_order(elab: &TermElabM<'_>, e: ExprId) -> bool {
    !any_subterm(
        elab,
        e,
        |_, _| false,
        |elab, e, n| {
            matches!(n, Node::App { .. })
                && !matches!(node(elab, app_fn(elab, e)), Node::Const { .. })
        },
    )
}

/// oracle `App.lean:1046`:
/// `Option.isSome (xType.find? fun e => e.isFVar && motiveFVars.fvarSet.contains e.fvarId!)`.
fn mentions_any(elab: &TermElabM<'_>, e: ExprId, set: &HashSet<ExprId>) -> bool {
    any_subterm(elab, e, has_no_fvar, |_, e, n| {
        matches!(n, Node::FVar { .. }) && set.contains(&e)
    })
}

#[cfg(test)]
mod tests {
    //! Hand-built eliminators over an empty environment, for the arms and
    //! the closure order no Elab0 declaration discriminates (the oracle
    //! gate is `tests/elim_info_oracle.rs`). Expected values follow the
    //! oracle's algorithm (`App.lean:1006-1050`) by hand.

    use leanr_kernel::bank::{ExprId, Store};
    use leanr_kernel::{BinderInfo, Environment, Nat};
    use leanr_meta::{Config, EnvExtensions, MetaCtx};

    use super::{get_elab_elim_expr_info, ElabElimInfo};
    use crate::elab::TermElabM;
    use crate::error::{ElabError, EliminatorErrorReason as R};

    fn with_elab<T>(k: impl FnOnce(&mut TermElabM<'_>) -> T) -> T {
        let env = Environment::default();
        let view = env.view();
        let mut scratch = Store::scratch();
        let mctx = MetaCtx::new(
            view,
            &mut scratch,
            Config::default(),
            EnvExtensions::default(),
        );
        let mut elab = TermElabM::new(mctx, view);
        k(&mut elab)
    }

    fn sort(elab: &mut TermElabM<'_>, succs: usize) -> ExprId {
        let s = elab.mctx.store_mut();
        let mut l = s.level_zero(None).unwrap();
        for _ in 0..succs {
            l = s.level_succ(None, l).unwrap();
        }
        s.expr_sort(None, l).unwrap()
    }

    fn bvar(elab: &mut TermElabM<'_>, i: u64) -> ExprId {
        elab.mctx
            .store_mut()
            .expr_bvar(None, &Nat::from(i))
            .unwrap()
    }

    fn app(elab: &mut TermElabM<'_>, f: ExprId, a: ExprId) -> ExprId {
        elab.mctx.store_mut().expr_app(None, f, a).unwrap()
    }

    fn pi(elab: &mut TermElabM<'_>, dom: ExprId, body: ExprId) -> ExprId {
        elab.mctx
            .store_mut()
            .expr_forall(None, None, dom, body, BinderInfo::Default)
            .unwrap()
    }

    fn local(elab: &mut TermElabM<'_>, ty: ExprId) -> ExprId {
        elab.mctx
            .push_local_decl(None, ty, BinderInfo::Default)
            .unwrap()
    }

    /// An ambient `T : Type`.
    fn ty_t(elab: &mut TermElabM<'_>) -> ExprId {
        let type0 = sort(elab, 1);
        local(elab, type0)
    }

    fn info_of_local_of_type(
        elab: &mut TermElabM<'_>,
        ty: ExprId,
    ) -> Result<ElabElimInfo, ElabError> {
        let elim = local(elab, ty);
        get_elab_elim_expr_info(elab, elim)
    }

    fn reason(r: Result<ElabElimInfo, ElabError>) -> R {
        match r {
            Err(ElabError::Eliminator { reason }) => reason,
            other => panic!("expected an Eliminator error, got {other:?}"),
        }
    }

    /// `elim : (m : T → T) → (n : T) → m n` — the motive returns `T`, not
    /// a sort (`App.lean:1018-1019`). No real declaration reaches this:
    /// the attribute validator rejects it.
    #[test]
    fn motive_result_not_a_sort() {
        with_elab(|elab| {
            let t = ty_t(elab);
            let m_ty = pi(elab, t, t);
            let (b1, b0) = (bvar(elab, 1), bvar(elab, 0));
            let m_n = app(elab, b1, b0);
            let inner = pi(elab, t, m_n);
            let elim_ty = pi(elab, m_ty, inner);
            let r = info_of_local_of_type(elab, elim_ty);
            assert_eq!(reason(r), R::MotiveResultNotSort);
        });
    }

    /// `elim : (m : T → Prop) → m` — the motive is applied to no
    /// arguments (`motiveArgs.size > 0`, `App.lean:1012-1013`). Without
    /// that check the walk would go on to report the motive's arity.
    #[test]
    fn motive_applied_to_nothing() {
        with_elab(|elab| {
            let t = ty_t(elab);
            let prop = sort(elab, 0);
            let m_ty = pi(elab, t, prop);
            let b0 = bvar(elab, 0);
            let elim_ty = pi(elab, m_ty, b0);
            let r = info_of_local_of_type(elab, elim_ty);
            assert_eq!(reason(r), R::UnexpectedResultingType);
        });
    }

    /// `elim : (m : T → Prop) → (a b : T) → m a b` — two arguments to a
    /// one-binder motive (`App.lean:1016-1017`).
    #[test]
    fn motive_arity_mismatch() {
        with_elab(|elab| {
            let t = ty_t(elab);
            let prop = sort(elab, 0);
            let m_ty = pi(elab, t, prop);
            let (b2, b1, b0) = (bvar(elab, 2), bvar(elab, 1), bvar(elab, 0));
            let m_a = app(elab, b2, b1);
            let m_a_b = app(elab, m_a, b0);
            let inner = pi(elab, t, m_a_b);
            let inner = pi(elab, t, inner);
            let elim_ty = pi(elab, m_ty, inner);
            let r = info_of_local_of_type(elab, elim_ty);
            assert_eq!(reason(r), R::UnexpectedMotiveArity);
        });
    }

    /// `elim : p t` for ambient `p : T → Prop`, `t : T` — a well-shaped
    /// motive that is not one of the eliminator's own binders
    /// (`xs.idxOf? motive = none`, `App.lean:1020-1021`).
    #[test]
    fn motive_bound_outside_the_telescope() {
        with_elab(|elab| {
            let t = ty_t(elab);
            let prop = sort(elab, 0);
            let p_ty = pi(elab, t, prop);
            let p = local(elab, p_ty);
            let x = local(elab, t);
            let elim_ty = app(elab, p, x);
            let r = info_of_local_of_type(elab, elim_ty);
            assert_eq!(reason(r), R::UnexpectedEliminatorType);
        });
    }

    /// `elim : (α : Type) → (β : α → Type) → (a : α) → (b : β a) →
    /// (motive : β a → Prop) → motive b`. The motive's argument mentions
    /// only `b`; `b`'s type adds `β` and `a`, and `a`'s type adds `α` —
    /// which only the right-to-left closure (`foldRevM`, `App.lean:1027`)
    /// reaches in one pass: a left-to-right pass visits `α` before `a`
    /// joins the set. So `majors = [0, 1, 2, 3]`, not `[1, 2, 3]`. Also
    /// checks that the call leaves the ambient `lctx` as it found it.
    #[test]
    fn closure_runs_right_to_left() {
        with_elab(|elab| {
            let type0 = sort(elab, 1);
            let prop = sort(elab, 0);
            // β : α → Type  (α = bvar 0)
            let b0 = bvar(elab, 0);
            let beta_ty = pi(elab, b0, type0);
            // a : α  (α β ⊢ α = bvar 1)
            let a_ty = bvar(elab, 1);
            // b : β a  (α β a ⊢ β = bvar 1, a = bvar 0)
            let (b1, b0) = (bvar(elab, 1), bvar(elab, 0));
            let b_ty = app(elab, b1, b0);
            // motive : β a → Prop  (α β a b ⊢ β = bvar 2, a = bvar 1)
            let (b2, b1) = (bvar(elab, 2), bvar(elab, 1));
            let beta_a = app(elab, b2, b1);
            let motive_ty = pi(elab, beta_a, prop);
            // motive b  (α β a b motive ⊢ motive = bvar 0, b = bvar 1)
            let (b0, b1) = (bvar(elab, 0), bvar(elab, 1));
            let body = app(elab, b0, b1);
            let e = pi(elab, motive_ty, body);
            let e = pi(elab, b_ty, e);
            let e = pi(elab, a_ty, e);
            let e = pi(elab, beta_ty, e);
            let elim_ty = pi(elab, type0, e);
            let elim = local(elab, elim_ty);
            let before = elab.mctx.lctx_checkpoint();
            let info = get_elab_elim_expr_info(elab, elim).unwrap();
            assert_eq!(elab.mctx.lctx_checkpoint(), before, "lctx restored");
            assert_eq!(info.elim_expr, elim);
            assert_eq!(info.elim_type, elim_ty);
            assert_eq!(info.motive_pos, 4);
            assert_eq!(info.majors_pos, vec![0, 1, 2, 3]);
        });
    }
}
