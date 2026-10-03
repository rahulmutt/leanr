//! oracle: universe-parameter bookkeeping for declarations (M4c-1 P1).
//! `Name.cmp` (`Lean/Data/Name.lean:67-80`), `Name.appendIndexAfter`
//! (`Init/Meta/Defs.lean:322-325`), `CollectLevelParams`
//! (`Lean/Util/CollectLevelParams.lean:17-72`), `sortDeclLevelParams`
//! (`Lean/Elab/DeclUtil.lean:79-89`) and `levelMVarToParam`
//! (`Lean/MetavarContext.lean:1403-1495`, namespace `LevelMVarToParam` plus
//! `UnivMVarParamResult`/`levelMVarToParam`; Task 3).

use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};

use leanr_kernel::bank::levels::LevelRow;
use leanr_kernel::bank::names::NameRow;
use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId, NameId, Store};
use leanr_kernel::Nat;

use crate::{LMVarId, MVarId, MetaCtx, MetaError};

/// oracle: `Name.cmp` (`Name.lean:67-80`): parents first; `num < str`;
/// strings by `compare` (code-point lexicographic, which `str::cmp`'s
/// byte order matches for UTF-8), nums numerically. `None` is
/// `Name.anonymous`.
pub fn name_cmp(
    st: &Store,
    base: Option<&Store>,
    a: Option<NameId>,
    b: Option<NameId>,
) -> Ordering {
    match (a, b) {
        (None, None) => Ordering::Equal,
        (None, Some(_)) => Ordering::Less,
        (Some(_), None) => Ordering::Greater,
        (Some(a), Some(b)) => match (st.name_row(base, a), st.name_row(base, b)) {
            (
                NameRow::Num {
                    parent: p1,
                    part: i1,
                },
                NameRow::Num {
                    parent: p2,
                    part: i2,
                },
            ) => name_cmp(st, base, *p1, *p2)
                .then_with(|| st.nat_at(base, *i1).0.cmp(&st.nat_at(base, *i2).0)),
            (NameRow::Num { .. }, NameRow::Str { .. }) => Ordering::Less,
            (NameRow::Str { .. }, NameRow::Num { .. }) => Ordering::Greater,
            (
                NameRow::Str {
                    parent: p1,
                    part: s1,
                },
                NameRow::Str {
                    parent: p2,
                    part: s2,
                },
            ) => name_cmp(st, base, *p1, *p2)
                .then_with(|| st.str_at(base, *s1).cmp(st.str_at(base, *s2))),
        },
    }
}

/// oracle: `Name.appendIndexAfter` (`Defs.lean:322-325`): `str p s` ->
/// `str p (s ++ "_" ++ idx)`; otherwise `str n ("_" ++ idx)`. leanr names
/// carry no macro scopes, so `modifyBase` is the identity.
pub(crate) fn append_index_after(
    st: &mut Store,
    base: Option<&Store>,
    n: NameId,
    idx: u64,
) -> Result<NameId, MetaError> {
    let (parent, s) = match *st.name_row(base, n) {
        NameRow::Str { parent, part } => (parent, format!("{}_{idx}", st.str_at(base, part))),
        NameRow::Num { .. } => (Some(n), format!("_{idx}")),
    };
    let sid = st.intern_str(base, &s)?;
    Ok(st.name_str(base, parent, sid)?)
}

/// oracle: `CollectLevelParams.State` (`CollectLevelParams.lean:17-20`).
#[derive(Default)]
pub struct CollectLevelParams {
    pub params: Vec<NameId>,
    visited_level: HashSet<LevelId>,
    visited_expr: HashSet<ExprId>,
}

impl MetaCtx<'_> {
    /// oracle: `visitExpr`/`main` (`CollectLevelParams.lean:43-57`) and
    /// `collectLevelParams` (`:72`). Composition `g ∘ f` applies `f`
    /// first, so every arm visits left to right.
    pub fn collect_level_params(
        &mut self,
        s: &mut CollectLevelParams,
        e: ExprId,
    ) -> Result<(), MetaError> {
        if !self.data(e).has_level_param() || !s.visited_expr.insert(e) {
            return Ok(());
        }
        self.step()?;
        match self.node(e) {
            Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                self.guarded(|c| c.collect_level_params(s, structure))
            }
            Node::Forall {
                binder_type, body, ..
            }
            | Node::Lam {
                binder_type, body, ..
            } => self.guarded(|c| {
                c.collect_level_params(s, binder_type)?;
                c.collect_level_params(s, body)
            }),
            Node::LetE {
                ty, value, body, ..
            } => self.guarded(|c| {
                c.collect_level_params(s, ty)?;
                c.collect_level_params(s, value)?;
                c.collect_level_params(s, body)
            }),
            Node::App { f, arg } => self.guarded(|c| {
                c.collect_level_params(s, f)?;
                c.collect_level_params(s, arg)
            }),
            Node::MData { expr, .. } => self.guarded(|c| c.collect_level_params(s, expr)),
            Node::Const { levels, .. } => {
                let ls = self
                    .scratch
                    .level_list_at(Some(self.view.store), levels)
                    .to_vec();
                for l in ls {
                    self.collect_level(s, l)?;
                }
                Ok(())
            }
            Node::Sort { level } => self.collect_level(s, level),
            _ => Ok(()),
        }
    }

    /// oracle: `visitLevel`/`collect` (`CollectLevelParams.lean:27-36`).
    /// Level flag bit `0b01` is "has param" (`bank/mod.rs` `level_param`).
    fn collect_level(&mut self, s: &mut CollectLevelParams, u: LevelId) -> Result<(), MetaError> {
        let base = Some(self.view.store);
        if self.scratch.level_flags(base, u) & 0b01 == 0 || !s.visited_level.insert(u) {
            return Ok(());
        }
        self.step()?;
        match *self.scratch.level_row(base, u) {
            LevelRow::Succ(v) => self.guarded(|c| c.collect_level(s, v)),
            LevelRow::Max(a, b) | LevelRow::IMax(a, b) => self.guarded(|c| {
                c.collect_level(s, a)?;
                c.collect_level(s, b)
            }),
            LevelRow::Param(Some(n)) => {
                s.params.push(n);
                Ok(())
            }
            _ => Ok(()),
        }
    }
}

/// oracle: `UnivMVarParamResult` (`MetavarContext.lean:1483-1487`); the
/// oracle's `mctx` field is updated in place on the `MetaCtx` instead.
pub struct LevelMVarToParamResult {
    pub expr: ExprId,
    pub new_param_names: Vec<NameId>,
    pub next_param_idx: u64,
}

/// oracle: `LevelMVarToParam.State` (`MetavarContext.lean:1410-1414`)
/// plus the reader `Context`'s `alreadyUsedPred` (`:1405-1408`).
struct L2P<'a> {
    already_used: &'a [NameId],
    next_idx: u64,
    names: Vec<NameId>,
    cache: HashMap<ExprId, ExprId>,
}

impl MetaCtx<'_> {
    /// oracle: `levelMVarToParam` (`MetavarContext.lean:1489-1495`) as
    /// called by `Term.levelMVarToParam` (`Elab/Term/TermElabM.lean:1059-1065`):
    /// prefix `u`, `except := fun _ => false`. The cache is keyed by
    /// `ExprId`, i.e. `ExprStructEq` for hash-consed terms.
    pub fn level_mvar_to_param(
        &mut self,
        e: ExprId,
        already_used: &[NameId],
        next_param_idx: u64,
    ) -> Result<LevelMVarToParamResult, MetaError> {
        let mut st = L2P {
            already_used,
            next_idx: next_param_idx,
            names: Vec::new(),
            cache: HashMap::new(),
        };
        let expr = self.l2p_main(&mut st, e)?;
        Ok(LevelMVarToParamResult {
            expr,
            new_param_names: st.names,
            next_param_idx: st.next_idx,
        })
    }

    /// oracle: `mkParamName` (`MetavarContext.lean:1426-1435`).
    fn l2p_param_name(&mut self, st: &mut L2P) -> Result<NameId, MetaError> {
        let base = Some(self.view.store);
        let u_str = self.scratch.intern_str(base, "u")?;
        let u = self.scratch.name_str(base, None, u_str)?;
        loop {
            let n = append_index_after(self.scratch, base, u, st.next_idx)?;
            st.next_idx += 1;
            if !st.already_used.contains(&n) {
                st.names.push(n);
                return Ok(n);
            }
        }
    }

    /// oracle: `visitLevel` (`MetavarContext.lean:1437-1454`).
    fn l2p_level(&mut self, st: &mut L2P, u: LevelId) -> Result<LevelId, MetaError> {
        let base = Some(self.view.store);
        match *self.scratch.level_row(base, u) {
            LevelRow::Succ(v) => {
                let v2 = self.guarded(|c| c.l2p_level(st, v))?;
                self.update_level_succ(u, v2)
            }
            LevelRow::Max(a, b) => {
                let a2 = self.guarded(|c| c.l2p_level(st, a))?;
                let b2 = self.guarded(|c| c.l2p_level(st, b))?;
                self.update_level_max(u, a2, b2)
            }
            LevelRow::IMax(a, b) => {
                let a2 = self.guarded(|c| c.l2p_level(st, a))?;
                let b2 = self.guarded(|c| c.l2p_level(st, b))?;
                self.update_level_imax(u, a2, b2)
            }
            LevelRow::Zero | LevelRow::Param(_) => Ok(u),
            LevelRow::MVar(name) => {
                let id =
                    LMVarId(name.ok_or_else(|| MetaError::MVar("anonymous level mvar".into()))?);
                match self.mctx.level_assignment(id) {
                    Some(v) => self.guarded(|c| c.l2p_level(st, v)),
                    None => {
                        let p = self.l2p_param_name(st)?;
                        let p = self.scratch.level_param(base, Some(p))?;
                        self.mctx.assign_level(id, p)?;
                        Ok(p)
                    }
                }
            }
        }
    }

    /// oracle: `main` (`MetavarContext.lean:1456-1471`). No binder is
    /// opened: loose bvars are walked directly, as in the oracle.
    fn l2p_main(&mut self, st: &mut L2P, e: ExprId) -> Result<ExprId, MetaError> {
        let d = self.data(e);
        if !d.has_expr_mvar() && !d.has_level_mvar() {
            return Ok(e);
        }
        if let Some(&r) = st.cache.get(&e) {
            return Ok(r);
        }
        self.step()?;
        let base = Some(self.view.store);
        let r = match self.node(e) {
            Node::Proj {
                type_name,
                idx,
                structure,
            } => {
                let s2 = self.guarded(|c| c.l2p_main(st, structure))?;
                self.scratch
                    .expr_proj(base, type_name, &Nat::from(idx as u64), s2)?
            }
            Node::ProjBig {
                type_name,
                idx,
                structure,
            } => {
                let n = self.scratch.nat_at(base, idx).clone();
                let s2 = self.guarded(|c| c.l2p_main(st, structure))?;
                self.scratch.expr_proj(base, type_name, &n, s2)?
            }
            Node::Forall {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let d2 = self.guarded(|c| c.l2p_main(st, binder_type))?;
                let b2 = self.guarded(|c| c.l2p_main(st, body))?;
                self.scratch
                    .expr_forall(base, binder_name, d2, b2, binder_info)?
            }
            Node::Lam {
                binder_name,
                binder_type,
                body,
                binder_info,
            } => {
                let d2 = self.guarded(|c| c.l2p_main(st, binder_type))?;
                let b2 = self.guarded(|c| c.l2p_main(st, body))?;
                self.scratch
                    .expr_lam(base, binder_name, d2, b2, binder_info)?
            }
            Node::LetE {
                decl_name,
                ty,
                value,
                body,
                non_dep,
            } => {
                let t2 = self.guarded(|c| c.l2p_main(st, ty))?;
                let v2 = self.guarded(|c| c.l2p_main(st, value))?;
                let b2 = self.guarded(|c| c.l2p_main(st, body))?;
                self.scratch
                    .expr_let(base, decl_name, t2, v2, b2, non_dep)?
            }
            Node::App { .. } => {
                let f = self.get_app_fn(e);
                let args = self.get_app_args(e);
                self.guarded(|c| c.l2p_visit_app(st, f, &args))?
            }
            Node::MData { data, expr } => {
                let b2 = self.guarded(|c| c.l2p_main(st, expr))?;
                self.scratch.expr_mdata(base, data, b2)?
            }
            Node::Const { name, levels } => {
                let ls = self.scratch.level_list_at(base, levels).to_vec();
                let mut out = Vec::with_capacity(ls.len());
                for l in ls {
                    out.push(self.l2p_level(st, l)?);
                }
                let ls2 = self.scratch.intern_level_list(base, &out)?;
                self.scratch.expr_const(base, name, ls2)?
            }
            Node::Sort { level } => {
                let l2 = self.l2p_level(st, level)?;
                self.scratch.expr_sort(base, l2)?
            }
            Node::MVar { .. } => self.guarded(|c| c.l2p_visit_app(st, e, &[]))?,
            _ => e,
        };
        st.cache.insert(e, r);
        Ok(r)
    }

    /// oracle: `main.visitApp` (`MetavarContext.lean:1472-1479`): an
    /// assigned expr-mvar head is replaced (args appended) and the result
    /// head-beta'd; otherwise `mkAppN (← main f) (← args.mapM main)`.
    fn l2p_visit_app(
        &mut self,
        st: &mut L2P,
        f: ExprId,
        args: &[ExprId],
    ) -> Result<ExprId, MetaError> {
        if let Node::MVar { id } = self.node(f) {
            let id = MVarId(id.ok_or_else(|| MetaError::MVar("anonymous mvar".into()))?);
            if let Some(v) = self.mctx.assignment(id) {
                // `visitApp v args`: `v` is NOT re-split (oracle `match f`).
                let r = self.guarded(|c| c.l2p_visit_app(st, v, args))?;
                return self.head_beta(r);
            }
            let out = self.l2p_args(st, args)?;
            return self.mk_app_spine(f, &out);
        }
        let f2 = self.guarded(|c| c.l2p_main(st, f))?;
        let out = self.l2p_args(st, args)?;
        self.mk_app_spine(f2, &out)
    }

    /// `args.mapM main`.
    fn l2p_args(&mut self, st: &mut L2P, args: &[ExprId]) -> Result<Vec<ExprId>, MetaError> {
        args.iter()
            .map(|&a| self.guarded(|c| c.l2p_main(st, a)))
            .collect()
    }
}

/// oracle: `sortDeclLevelParams` (`DeclUtil.lean:79-89`). `scope_params`
/// and `all_user_params` are in REVERSE declaration order. `Err(u)` is
/// the oracle's "unused universe parameter 'u'".
pub fn sort_decl_level_params(
    st: &Store,
    base: Option<&Store>,
    scope_params: &[NameId],
    all_user_params: &[NameId],
    used_params: &[NameId],
) -> Result<Vec<NameId>, NameId> {
    if let Some(&u) = all_user_params
        .iter()
        .find(|u| !used_params.contains(u) && !scope_params.contains(u))
    {
        return Err(u);
    }
    // foldl over the reversed list, consing -> user order.
    let mut result: Vec<NameId> = all_user_params
        .iter()
        .rev()
        .copied()
        .filter(|u| used_params.contains(u))
        .collect();
    let mut remaining: Vec<NameId> = used_params
        .iter()
        .copied()
        .filter(|p| !all_user_params.contains(p))
        .collect();
    remaining.sort_by(|a, b| name_cmp(st, base, Some(*a), Some(*b)));
    result.extend(remaining);
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::{app, cu, lit_level, lparam, with_ctx};
    use leanr_kernel::bank::NameId;
    use leanr_kernel::BinderInfo;

    fn nm(ctx: &mut MetaCtx, s: &str) -> NameId {
        let base = Some(ctx.view.store);
        let mut n = None;
        for part in s.split('.') {
            let id = ctx.scratch.intern_str(base, part).unwrap();
            n = Some(ctx.scratch.name_str(base, n, id).unwrap());
        }
        n.unwrap()
    }

    #[test]
    fn name_cmp_is_the_oracle_structural_order() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let (u, u_2, u_10, u_v) = (
                nm(ctx, "u"),
                nm(ctx, "u_2"),
                nm(ctx, "u_10"),
                nm(ctx, "u.v"),
            );
            use std::cmp::Ordering::*;
            // String components compare lexicographically: "u_10" < "u_2".
            assert_eq!(name_cmp(ctx.scratch, base, Some(u_10), Some(u_2)), Less);
            // A prefix (shorter parent chain) sorts first: `u` < `u.v`.
            assert_eq!(name_cmp(ctx.scratch, base, Some(u), Some(u_v)), Less);
            assert_eq!(name_cmp(ctx.scratch, base, None, Some(u)), Less);
            assert_eq!(name_cmp(ctx.scratch, base, Some(u), Some(u)), Equal);
        });
    }

    #[test]
    fn append_index_after_extends_the_last_string_component() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let proof = nm(ctx, "foo._proof");
            let got = append_index_after(ctx.scratch, base, proof, 1).unwrap();
            assert_eq!(got, nm(ctx, "foo._proof_1"));
        });
    }

    /// Visit order is the oracle's: app fn before arg, const levels left
    /// to right; each param once.
    #[test]
    fn collect_level_params_visits_in_oracle_order_and_dedupes() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let (u, v, w) = (lparam(ctx, "u"), lparam(ctx, "v"), lparam(ctx, "w"));
            let f = cu(ctx, "F", &[v, u]); // F.{v,u}
            let sw = ctx.scratch.expr_sort(base, w).unwrap(); // Sort w
            let fu = app(ctx, f, sw); // F.{v,u} (Sort w)
            let uu = ctx.scratch.level_max(base, u, u).unwrap();
            let su = ctx.scratch.expr_sort(base, uu).unwrap(); // Sort (max u u)
            let e = app(ctx, fu, su);
            let mut s = CollectLevelParams::default();
            ctx.collect_level_params(&mut s, e).unwrap();
            assert_eq!(s.params, vec![nm(ctx, "v"), nm(ctx, "u"), nm(ctx, "w")]);
        });
    }

    /// Ruling R1: forall/lam domain is visited before the body. Binder
    /// type and body carry different params so the order is observable.
    #[test]
    fn collect_level_params_visits_binder_domain_before_body() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let ls: Vec<_> = ["a", "b", "c", "d"]
                .iter()
                .map(|n| lparam(ctx, n))
                .collect();
            let sorts: Vec<_> = ls
                .iter()
                .map(|&l| ctx.scratch.expr_sort(base, l).unwrap())
                .collect();
            let bi = BinderInfo::Default;
            // (x : Sort a) → Sort b   and   fun (x : Sort c) => Sort d
            let pi = ctx
                .scratch
                .expr_forall(base, None, sorts[0], sorts[1], bi)
                .unwrap();
            let lam = ctx
                .scratch
                .expr_lam(base, None, sorts[2], sorts[3], bi)
                .unwrap();
            let e = app(ctx, pi, lam);
            let mut s = CollectLevelParams::default();
            ctx.collect_level_params(&mut s, e).unwrap();
            let want: Vec<_> = ["a", "b", "c", "d"].iter().map(|n| nm(ctx, n)).collect();
            assert_eq!(s.params, want);
        });
    }

    /// Review Focus 1: user names first in user order, then the rest by
    /// `Name.lt` -- so `u_10` precedes `u_2`.
    #[test]
    fn sort_decl_level_params_sorts_leftovers_lexicographically() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let (u, v, u_2, u_10) = (nm(ctx, "u"), nm(ctx, "v"), nm(ctx, "u_2"), nm(ctx, "u_10"));
            // `.{u, v}` declared in that order -> reverse order in the list.
            let all_user = [v, u];
            let used = [u_2, v, u_10, u];
            let got = sort_decl_level_params(ctx.scratch, base, &[], &all_user, &used).unwrap();
            assert_eq!(got, vec![u, v, u_10, u_2]);
        });
    }

    #[test]
    fn sort_decl_level_params_rejects_an_unused_user_param_outside_the_scope() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let (u, w) = (nm(ctx, "u"), nm(ctx, "w"));
            assert_eq!(
                sort_decl_level_params(ctx.scratch, base, &[], &[w, u], &[u]),
                Err(w)
            );
            // In scope (`universe w`), an unused `w` is fine and is not listed.
            assert_eq!(
                sort_decl_level_params(ctx.scratch, base, &[w], &[w, u], &[u]),
                Ok(vec![u])
            );
        });
    }

    fn sort_of(ctx: &mut MetaCtx, l: LevelId) -> ExprId {
        let base = Some(ctx.view.store);
        ctx.scratch.expr_sort(base, l).unwrap()
    }

    fn arrow(ctx: &mut MetaCtx, a: ExprId, b: ExprId) -> ExprId {
        ctx.mk_arrow(a, b).unwrap()
    }

    /// `Sort ?u -> Sort ?v -> Sort ?u` becomes `Sort u_1 -> Sort u_2 -> Sort u_1`;
    /// the mvars are ASSIGNED, so a second occurrence reuses the param.
    #[test]
    fn level_mvar_to_param_names_u_n_and_assigns() {
        with_ctx(|ctx| {
            let (mu, lu) = ctx.fresh_level_mvar().unwrap();
            let (_mv, lv) = ctx.fresh_level_mvar().unwrap();
            let (su, sv) = (sort_of(ctx, lu), sort_of(ctx, lv));
            let inner = arrow(ctx, sv, su);
            let e = arrow(ctx, su, inner);
            let r = ctx.level_mvar_to_param(e, &[], 1).unwrap();
            let (p1, p2) = (lparam(ctx, "u_1"), lparam(ctx, "u_2"));
            let (s1, s2) = (sort_of(ctx, p1), sort_of(ctx, p2));
            let inner2 = arrow(ctx, s2, s1);
            assert_eq!(r.expr, arrow(ctx, s1, inner2));
            assert_eq!(r.new_param_names, vec![nm(ctx, "u_1"), nm(ctx, "u_2")]);
            assert_eq!(r.next_param_idx, 3);
            assert_eq!(ctx.mctx().level_assignment(mu), Some(p1));
        });
    }

    #[test]
    fn level_mvar_to_param_skips_already_used_names() {
        with_ctx(|ctx| {
            let (_m, l) = ctx.fresh_level_mvar().unwrap();
            let e = sort_of(ctx, l);
            let used = [nm(ctx, "u_1")];
            let r = ctx.level_mvar_to_param(e, &used, 1).unwrap();
            let p2 = lparam(ctx, "u_2");
            assert_eq!(r.expr, sort_of(ctx, p2));
            assert_eq!(r.new_param_names, vec![nm(ctx, "u_2")]);
            assert_eq!(r.next_param_idx, 3);
        });
    }

    /// An assigned mvar is followed: `?w := succ ?u` gives `Sort (succ u_1)`.
    #[test]
    fn level_mvar_to_param_follows_level_assignments() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let (_mu, lu) = ctx.fresh_level_mvar().unwrap();
            let (mw, lw) = ctx.fresh_level_mvar().unwrap();
            let su = ctx.scratch.level_succ(base, lu).unwrap();
            ctx.mctx_mut().assign_level(mw, su).unwrap();
            let e = sort_of(ctx, lw);
            let r = ctx.level_mvar_to_param(e, &[], 1).unwrap();
            let p1 = lparam(ctx, "u_1");
            let sp1 = ctx.scratch.level_succ(base, p1).unwrap();
            assert_eq!(r.expr, sort_of(ctx, sp1));
            assert_eq!(r.new_param_names, vec![nm(ctx, "u_1")]);
        });
    }

    /// Binders, `const` levels and a mvar-free subterm: the domain and body
    /// of a `lam`/`forall` are both rebuilt; a closed term is returned as is.
    #[test]
    fn level_mvar_to_param_rebuilds_binders_and_const_levels() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let (_m, l) = ctx.fresh_level_mvar().unwrap();
            let c = cu(ctx, "F", &[l]);
            let bi = BinderInfo::Default;
            let lam = ctx.scratch.expr_lam(base, None, c, c, bi).unwrap();
            let e = ctx.scratch.expr_forall(base, None, lam, lam, bi).unwrap();
            let r = ctx.level_mvar_to_param(e, &[], 1).unwrap();
            let p = lparam(ctx, "u_1");
            let c2 = cu(ctx, "F", &[p]);
            let lam2 = ctx.scratch.expr_lam(base, None, c2, c2, bi).unwrap();
            let want = ctx.scratch.expr_forall(base, None, lam2, lam2, bi).unwrap();
            assert_eq!(r.expr, want);
            assert_eq!(r.new_param_names.len(), 1);
            // Closed term: untouched, no names consumed.
            let r2 = ctx.level_mvar_to_param(want, &[], 7).unwrap();
            assert_eq!(r2.expr, want);
            assert_eq!(r2.next_param_idx, 7);
        });
    }

    /// An assigned expr-mvar head is instantiated and head-beta'd:
    /// `?f (Sort ?u)` with `?f := fun x => x` gives `Sort u_1`.
    #[test]
    fn level_mvar_to_param_beta_reduces_assigned_mvar_heads() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let z = ctx.scratch.level_zero(base).unwrap();
            let ty = ctx.scratch.expr_sort(base, z).unwrap();
            let (f, mf) = crate::test_support::fresh_mvar(ctx, ty);
            let bv = crate::test_support::bvar(ctx, 0);
            let id = ctx
                .scratch
                .expr_lam(base, None, ty, bv, BinderInfo::Default)
                .unwrap();
            ctx.mctx_mut().assign(mf, id).unwrap();
            let (_m, l) = ctx.fresh_level_mvar().unwrap();
            let arg = sort_of(ctx, l);
            let e = app(ctx, f, arg);
            let r = ctx.level_mvar_to_param(e, &[], 1).unwrap();
            let p1 = lparam(ctx, "u_1");
            assert_eq!(r.expr, sort_of(ctx, p1));
        });
    }

    /// `update_level_max` on CHANGED children uses `mkLevelMax'`, which
    /// simplifies `max 1 0` to `1`; on UNCHANGED children it returns `orig`
    /// unless `simpLevelMax'` fires.
    #[test]
    fn update_level_max_simplifies_like_mk_level_max_prime() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let (zero, one) = (lit_level(ctx, 0), lit_level(ctx, 1));
            let u = lparam(ctx, "u");
            let orig = ctx.scratch.level_max(base, u, zero).unwrap(); // max u 0
            assert_eq!(ctx.update_level_max(orig, one, zero).unwrap(), one);
            let v = lparam(ctx, "v");
            let uv = ctx.scratch.level_max(base, u, v).unwrap();
            assert_eq!(ctx.update_level_max(uv, u, v).unwrap(), uv);
            // Unchanged children where `simpLevelMax'` fires: `max u 0` -> `u`.
            assert_eq!(ctx.update_level_max(orig, u, zero).unwrap(), u);
        });
    }

    /// `mkLevelIMaxCore` branch order, on changed AND unchanged children.
    #[test]
    fn update_level_imax_follows_mk_level_imax_core_branches() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = lit_level(ctx, 0);
            let (u, v) = (lparam(ctx, "u"), lparam(ctx, "v"));
            let sv = ctx.scratch.level_succ(base, v).unwrap();
            // isNeverZero v: `imax u (succ v)` -> `max u (succ v)` even unchanged.
            let orig = ctx.scratch.level_imax(base, u, sv).unwrap();
            let want = ctx.scratch.level_max(base, u, sv).unwrap();
            assert_eq!(ctx.update_level_imax(orig, u, sv).unwrap(), want);
            // isZero v -> v (= 0).
            let o2 = ctx.scratch.level_imax(base, u, v).unwrap();
            assert_eq!(ctx.update_level_imax(o2, u, zero).unwrap(), zero);
            // isZero u -> v.
            assert_eq!(ctx.update_level_imax(o2, zero, v).unwrap(), v);
            // u == v -> u.
            assert_eq!(ctx.update_level_imax(o2, u, u).unwrap(), u);
            // else: unchanged -> orig; changed -> raw imax.
            assert_eq!(ctx.update_level_imax(o2, u, v).unwrap(), o2);
            let w = lparam(ctx, "w");
            let want = ctx.scratch.level_imax(base, w, v).unwrap();
            assert_eq!(ctx.update_level_imax(o2, w, v).unwrap(), want);
        });
    }

    #[test]
    fn update_level_succ_keeps_orig_when_unchanged() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let u = lparam(ctx, "u");
            let su = ctx.scratch.level_succ(base, u).unwrap();
            assert_eq!(ctx.update_level_succ(su, u).unwrap(), su);
            let v = lparam(ctx, "v");
            let sv = ctx.scratch.level_succ(base, v).unwrap();
            assert_eq!(ctx.update_level_succ(su, v).unwrap(), sv);
        });
    }
}
