//! Term-level universe-name scoping used by command elaboration.

use leanr_kernel::bank::{ExprId, NameId};

use crate::elab::TermElabM;
use crate::error::ElabError;

impl TermElabM<'_> {
    /// oracle: `withLevelNames` (`Elab/Term/TermElabM.lean:716-719`) — run
    /// `k` with `level_names` replaced, restored on both paths.
    pub(crate) fn with_level_names<R>(
        &mut self,
        names: Vec<NameId>,
        k: impl FnOnce(&mut Self) -> Result<R, ElabError>,
    ) -> Result<R, ElabError> {
        let prev = std::mem::replace(&mut self.level_names, names);
        let out = k(self);
        self.level_names = prev;
        out
    }

    /// oracle: `Term.levelMVarToParam` (`Elab/Term/TermElabM.lean:1059-1065`):
    /// fresh `u_i` avoiding `levelNames`, index from 1, and the new names
    /// prepended REVERSED (head = most recent).
    pub(crate) fn level_mvar_to_param(&mut self, e: ExprId) -> Result<ExprId, ElabError> {
        let r = self.mctx.level_mvar_to_param(e, &self.level_names, 1)?;
        let mut names = r.new_param_names;
        names.reverse();
        names.extend(self.level_names.iter().copied());
        self.level_names = names;
        Ok(r.expr)
    }
}

#[cfg(test)]
mod tests {
    use leanr_kernel::bank::{NameId, Store};
    use leanr_kernel::{BinderInfo, Environment};
    use leanr_meta::{Config, EnvExtensions, MetaCtx};

    use crate::elab::TermElabM;

    fn names(elab: &TermElabM, ns: &[NameId]) -> Vec<String> {
        let base = Some(elab.view.store);
        ns.iter()
            .map(|&n| elab.mctx.store().to_name(base, Some(n)).to_string())
            .collect()
    }

    /// `Term.levelMVarToParam` prepends the new names REVERSED
    /// (`TermElabM.lean:1063`): the head of `levelNames` is the most recent.
    /// On the def path the new `u_i` never reach `fix_level_params` (they
    /// sort as leftovers), so `oracle_decl_gate` cannot see this order
    /// (Task 6 mutation 1); the theorem path (Task 7) consumes it.
    #[test]
    fn level_mvar_to_param_prepends_new_names_most_recent_first() {
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
        let v = super::super::header::intern_atomic(&mut elab, "v").unwrap();
        // `Sort ?a → Sort ?b`: `?a` is met first, so it becomes `u_1`.
        let a = elab.mk_fresh_level_mvar().unwrap();
        let b = elab.mk_fresh_level_mvar().unwrap();
        let st = elab.mctx.store_mut();
        let sa = st.expr_sort(None, a).unwrap();
        let sb = st.expr_sort(None, b).unwrap();
        let e = st
            .expr_forall(None, None, sa, sb, BinderInfo::Default)
            .unwrap();
        let after = elab
            .with_level_names(vec![v], |elab| {
                elab.level_mvar_to_param(e)?;
                Ok(elab.level_names.clone())
            })
            .unwrap();
        assert_eq!(names(&elab, &after), ["u_2", "u_1", "v"]);
        assert!(elab.level_names.is_empty(), "with_level_names restores");
    }
}
