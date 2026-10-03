//! oracle: universe-parameter bookkeeping for declarations (M4c-1 P1).
//! `Name.cmp` (`Lean/Data/Name.lean:67-80`), `Name.appendIndexAfter`
//! (`Init/Meta/Defs.lean:322-325`), `CollectLevelParams`
//! (`Lean/Util/CollectLevelParams.lean:17-72`), `sortDeclLevelParams`
//! (`Lean/Elab/DeclUtil.lean:79-89`) and `levelMVarToParam`
//! (`Lean/MetavarContext.lean:1426-1497`; Task 3).

use std::cmp::Ordering;
use std::collections::HashSet;

use leanr_kernel::bank::levels::LevelRow;
use leanr_kernel::bank::names::NameRow;
use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId, NameId, Store};

use crate::{MetaCtx, MetaError};

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
#[allow(dead_code)] // consumed by later M4c-1 P1 tasks (`_proof_N` naming)
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
    use crate::test_support::{app, cu, lparam, with_ctx};
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
}
