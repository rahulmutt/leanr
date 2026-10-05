//! Reporting unassigned metavariables: oracle `logUnassignedUsingErrorInfos`
//! / `logUnassignedLevelMVarsUsingErrorInfos` (`Elab/Term/TermElabM.lean:
//! 901-1013`) and `getMVars` (`Meta/CollectMVars.lean:25-39`). leanr returns
//! the FIRST error the oracle would log instead of logging. It stops at its
//! first error, so the oracle's `hasOtherErrors` is always false here.

use std::collections::HashSet;

use leanr_kernel::bank::levels::LevelRow;
use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId, NameId};
use leanr_meta::{LMVarId, MVarId};

use crate::elab::TermElabM;
use crate::error::ElabError;
use crate::synthetic::MVarErrorKind;

impl TermElabM<'_> {
    /// oracle: `getMVars` (`Meta/CollectMVars.lean:25-39`): the unassigned
    /// mvars of `instantiateMVars e` in order of first occurrence, and for
    /// each delayed-assigned one, those of its pending mvar too.
    pub fn get_mvars(&mut self, e: ExprId) -> Result<Vec<MVarId>, ElabError> {
        let mut out = Vec::new();
        self.collect_mvars(e, &mut out)?;
        Ok(out)
    }

    fn collect_mvars(&mut self, e: ExprId, out: &mut Vec<MVarId>) -> Result<(), ElabError> {
        let e = self.mctx.instantiate_mvars(e)?;
        let start = out.len();
        let base = Some(self.view.store);
        // `Expr.collectMVars`: pre-order, function before argument.
        let mut seen: HashSet<ExprId> = HashSet::new();
        let mut stack = vec![e];
        while let Some(t) = stack.pop() {
            if !self.mctx.store().expr_data(base, t).has_expr_mvar() || !seen.insert(t) {
                continue;
            }
            match self.mctx.store().expr_node(base, t) {
                Node::MVar { id: Some(n) } => {
                    if !out.contains(&MVarId(n)) {
                        out.push(MVarId(n));
                    }
                }
                Node::App { f, arg } => {
                    stack.push(arg);
                    stack.push(f);
                }
                Node::Lam {
                    binder_type, body, ..
                }
                | Node::Forall {
                    binder_type, body, ..
                } => {
                    stack.push(body);
                    stack.push(binder_type);
                }
                Node::LetE {
                    ty, value, body, ..
                } => {
                    stack.push(body);
                    stack.push(value);
                    stack.push(ty);
                }
                Node::MData { expr, .. } => stack.push(expr),
                Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                    stack.push(structure)
                }
                _ => {}
            }
        }
        let added: Vec<MVarId> = out[start..].to_vec();
        for m in added {
            let pending = self
                .mctx
                .mctx()
                .delayed_assignment(m)
                .map(|d| d.mvar_id_pending);
            if let Some(p) = pending {
                let pe = self
                    .mctx
                    .store_mut()
                    .expr_mvar(base, Some(p.0))
                    .map_err(leanr_meta::MetaError::from)?;
                self.collect_mvars(pe, out)?;
            }
        }
        Ok(())
    }

    /// oracle: `collectLevelMVars {} (← instantiateMVars e)`.
    /// `instantiate_mvars` also instantiates assigned level mvars
    /// (`assign.rs`, `instantiate_mvars_body`'s `Sort`/`Const` arms).
    pub fn get_level_mvars(&mut self, e: ExprId) -> Result<Vec<LMVarId>, ElabError> {
        let e = self.mctx.instantiate_mvars(e)?;
        let base = Some(self.view.store);
        let mut out = Vec::new();
        let mut seen: HashSet<ExprId> = HashSet::new();
        let mut stack = vec![e];
        while let Some(t) = stack.pop() {
            if !self.mctx.store().expr_data(base, t).has_level_mvar() || !seen.insert(t) {
                continue;
            }
            match self.mctx.store().expr_node(base, t) {
                Node::Sort { level } => self.collect_level_mvars_of(level, &mut out),
                Node::Const { levels, .. } => {
                    let ls = self.mctx.store().level_list_at(base, levels).to_vec();
                    for l in ls {
                        self.collect_level_mvars_of(l, &mut out);
                    }
                }
                Node::App { f, arg } => {
                    stack.push(arg);
                    stack.push(f);
                }
                Node::Lam {
                    binder_type, body, ..
                }
                | Node::Forall {
                    binder_type, body, ..
                } => {
                    stack.push(body);
                    stack.push(binder_type);
                }
                Node::LetE {
                    ty, value, body, ..
                } => {
                    stack.push(body);
                    stack.push(value);
                    stack.push(ty);
                }
                Node::MData { expr, .. } => stack.push(expr),
                Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                    stack.push(structure)
                }
                _ => {}
            }
        }
        Ok(out)
    }

    fn collect_level_mvars_of(&self, l: LevelId, out: &mut Vec<LMVarId>) {
        let base = Some(self.view.store);
        let mut stack = vec![l];
        while let Some(l) = stack.pop() {
            match *self.mctx.store().level_row(base, l) {
                LevelRow::Succ(a) => stack.push(a),
                LevelRow::Max(a, b) | LevelRow::IMax(a, b) => {
                    stack.push(b);
                    stack.push(a);
                }
                LevelRow::MVar(Some(n)) if !out.contains(&LMVarId(n)) => out.push(LMVarId(n)),
                _ => {}
            }
        }
    }

    /// oracle: `Name.hasMacroScopes` (`Init/Prelude.lean`): the last string
    /// component is `_hyg`, looking through numeric components. leanr's own
    /// fresh names (`_leanr_*`: `leanr_elab`'s `_leanr_elab_*`, `leanr_meta`'s
    /// `mkFreshBinderName` stand-in `_leanr_mkbinding_fresh.<n>`) stand in for
    /// the oracle's macro-scoped ones, so they count as well.
    pub(crate) fn name_has_macro_scopes(&self, n: NameId) -> bool {
        let base = Some(self.view.store);
        let s = self.mctx.store().to_name(base, Some(n)).to_string();
        if s.starts_with("_leanr_") {
            return true;
        }
        s.split('.')
            .rev()
            .find(|c| c.parse::<u64>().is_err())
            .is_some_and(|c| c == "_hyg")
    }

    /// `addArgName` (`TermElabM.lean:917-920`): `` " `{argName}`" `` (after
    /// `extra`) if a name is registered and has no macro scopes.
    fn arg_name_suffix(&self, m: MVarId, extra: &str) -> String {
        match self.mvar_arg_names.get(&m) {
            Some(&n) if !self.name_has_macro_scopes(n) => {
                let base = Some(self.view.store);
                format!("{extra} `{}`", self.mctx.store().to_name(base, Some(n)))
            }
            _ => String::new(),
        }
    }

    /// oracle: `logUnassignedUsingErrorInfos` (`TermElabM.lean:934-958`) +
    /// `MVarErrorInfo.logError`'s first line (`:901-912`).
    pub fn log_unassigned_using_error_infos(
        &mut self,
        pending: &[MVarId],
    ) -> Result<Option<ElabError>, ElabError> {
        if pending.is_empty() {
            return Ok(None);
        }
        let mut visited: HashSet<MVarId> = HashSet::new();
        // newest first: the oracle's list is consed (`:871`)
        let infos: Vec<_> = self.mvar_error_infos.iter().rev().cloned().collect();
        for info in infos {
            if !visited.insert(info.mvar_id) {
                continue;
            }
            let e = self
                .mctx
                .store_mut()
                .expr_mvar(Some(self.view.store), Some(info.mvar_id.0))
                .map_err(leanr_meta::MetaError::from)?;
            let deps = self.get_mvars(e)?;
            if !deps.iter().any(|d| pending.contains(d)) {
                continue;
            }
            let line = match &info.kind {
                MVarErrorKind::ImplicitArg { .. } => format!(
                    "don't know how to synthesize implicit argument{}",
                    self.arg_name_suffix(info.mvar_id, "")
                ),
                MVarErrorKind::Hole => format!(
                    "don't know how to synthesize placeholder{}",
                    self.arg_name_suffix(info.mvar_id, " for argument")
                ),
                MVarErrorKind::Custom(m) => m.lines().next().unwrap_or("").to_string(),
            };
            return Ok(Some(ElabError::UnassignedMVars(line)));
        }
        Ok(None)
    }

    /// oracle: `logUnassignedLevelMVarsUsingErrorInfos` (`TermElabM.lean:
    /// 997-1013`) + `LevelMVarErrorInfo.logError`'s first line (`:983-988`).
    pub fn log_unassigned_level_mvars_using_error_infos(
        &mut self,
        pending: &[LMVarId],
    ) -> Result<Option<ElabError>, ElabError> {
        if pending.is_empty() {
            return Ok(None);
        }
        let infos: Vec<_> = self.level_mvar_error_infos.iter().rev().cloned().collect();
        for info in infos {
            let lmvars = self.get_level_mvars(info.expr)?;
            if lmvars.iter().any(|l| pending.contains(l)) {
                let line = info.msg.unwrap_or_else(|| {
                    "don't know how to synthesize universe level metavariables".into()
                });
                return Ok(Some(ElabError::UnassignedLevelMVars(line)));
            }
        }
        Ok(None)
    }
}

#[cfg(test)]
mod tests {
    use leanr_kernel::bank::{NameId, Store};
    use leanr_kernel::{Environment, Nat};
    use leanr_meta::{Config, EnvExtensions, MetaCtx};

    use crate::elab::TermElabM;

    /// `a.b.<n>…` with numeric components where `parts` holds a number.
    fn name(elab: &mut TermElabM<'_>, parts: &[&str]) -> NameId {
        let s = elab.mctx.store_mut();
        let mut n = None;
        for p in parts {
            n = Some(match p.parse::<u64>() {
                Ok(k) => {
                    let k = s.intern_nat(None, &Nat::from(k)).unwrap();
                    s.name_num(None, n, k).unwrap()
                }
                Err(_) => {
                    let p = s.intern_str(None, p).unwrap();
                    s.name_str(None, n, p).unwrap()
                }
            });
        }
        n.unwrap()
    }

    /// leanr's fresh-name stand-ins for macro scopes count as macro-scoped:
    /// `leanr_elab`'s `_leanr_elab_*` and `leanr_meta`'s
    /// `mkFreshBinderName` stand-in `_leanr_mkbinding_fresh.<n>` (an
    /// auto-bound mvar binder is inaccessible, spec Amendment 1 item 1).
    #[test]
    fn leanr_fresh_names_count_as_macro_scoped() {
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
        let mk = name(&mut elab, &["_leanr_mkbinding_fresh", "3"]);
        let el = name(&mut elab, &["_leanr_elab_binder_fresh", "0"]);
        let hyg = name(&mut elab, &["x", "_@", "M", "_hyg", "2"]);
        let plain = name(&mut elab, &["α"]);
        assert!(elab.name_has_macro_scopes(mk));
        assert!(elab.name_has_macro_scopes(el));
        assert!(elab.name_has_macro_scopes(hyg));
        assert!(!elab.name_has_macro_scopes(plain));
    }
}
