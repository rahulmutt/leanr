//! Overloaded elaboration's selection. Oracle: `elabAppAux`
//! (`App.lean:2202-2219`) after `elabAppFn` returned two or more
//! results: `getSuccesses` (`:2141-2185`), then the single survivor
//! (`applyResult`), `Ambiguous term` (`:2217`), or `mergeFailures`
//! (`:2190-2200`).
//!
//! Every captured error is an oracle error. `TermElabM::observing`
//! rethrows seams and other non-oracle errors instead of capturing them,
//! because leanr cannot know whether the oracle accepts that candidate
//! (spec § Rule 1). The `catch _` inside stages 2 and 3 follows the same
//! rule.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;
use leanr_meta::MVarId;
use leanr_syntax::kind::KindInterner;

use crate::elab::TermElabM;
use crate::error::ElabError;
use crate::synthetic::{PostponeBehavior, SavedTermState, SyntheticMVarKind, TermElabResult};

/// `elabAppAux`'s multi-candidate arm (`App.lean:2207-2219`).
pub(crate) fn select(
    elab: &mut TermElabM,
    cands: Vec<TermElabResult>,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let ok = get_successes(elab, &cands, kinds)?;
    match ok.as_slice() {
        [i] => {
            let r = cands
                .into_iter()
                .nth(*i)
                .expect("an index get_successes returned");
            elab.apply_result(r)
        }
        // `mergeFailures`: no success at all means every candidate failed.
        [] => Err(ElabError::Overloaded(
            cands
                .into_iter()
                .map(|r| match r {
                    TermElabResult::Err(e, _) => e,
                    TermElabResult::Ok(..) => unreachable!("getSuccesses keeps every Ok in r₁"),
                })
                .collect(),
        )),
        _ => Err(ElabError::AmbiguousTerm),
    }
}

/// oracle: `getSuccesses` (`App.lean:2141-2185`), returning indices into
/// `cands`. Stages 2 and 3 each restore a success's state and synthesize.
/// Like the oracle, this leaves the elaborator in the last state it
/// restored; `select` either `apply_result`s the winner or throws.
fn get_successes(
    elab: &mut TermElabM,
    cands: &[TermElabResult],
    kinds: &KindInterner,
) -> Result<Vec<usize>, ElabError> {
    let oks: Vec<(usize, ExprId, &SavedTermState)> = cands
        .iter()
        .enumerate()
        .filter_map(|(i, r)| match r {
            TermElabResult::Ok(e, s) => Some((i, *e, s)),
            TermElabResult::Err(..) => None,
        })
        .collect();
    let r1: Vec<usize> = oks.iter().map(|&(i, _, _)| i).collect();
    if r1.len() <= 1 {
        return Ok(r1);
    }
    // Stage 2 (`:2144-2168`): drop a result that is still a delayed
    // coercion after `synthesizeSyntheticMVars` (default `postpone := .yes`).
    let mut r2 = Vec::new();
    for &(i, e, s) in &oks {
        if matches!(crate::app::lval::node(elab, e), Node::MVar { .. }) {
            elab.restore_term_state(s.clone());
            match elab.synthesize_synthetic_mvars(PostponeBehavior::Yes, kinds) {
                Ok(()) => {}
                // `catch _ => return false` (`:2160-2162`), oracle errors only.
                Err(err) if err.is_oracle_error() => continue,
                Err(err) => return Err(err),
            }
            let e = elab.mctx.instantiate_mvars(e)?;
            if let Node::MVar { id: Some(m) } = crate::app::lval::node(elab, e) {
                if matches!(
                    elab.synthetic_mvar_decl(MVarId(m)).map(|d| &d.kind),
                    Some(SyntheticMVarKind::Coe { .. })
                ) {
                    continue;
                }
            }
        }
        r2.push(i);
    }
    if r2.is_empty() {
        return Ok(r1);
    }
    if r2.len() == 1 {
        return Ok(r2);
    }
    // Stage 3 (`:2174-2185`): over ALL successes again (`candidates.filterM`,
    // not `r₂`), keep those whose pending work synthesizes with
    // `postpone := .no`.
    let mut r3 = Vec::new();
    for &(i, _, s) in &oks {
        elab.restore_term_state(s.clone());
        match elab.synthesize_synthetic_mvars(PostponeBehavior::No, kinds) {
            Ok(()) => r3.push(i),
            Err(err) if err.is_oracle_error() => {}
            Err(err) => return Err(err),
        }
    }
    Ok(if r3.is_empty() { r1 } else { r3 })
}

#[cfg(test)]
mod tests {
    use leanr_kernel::bank::Store;
    use leanr_kernel::{AxiomVal, ConstantInfo, ConstantVal, Environment};
    use leanr_meta::{Config, EnvExtensions, MVarKind, MetaCtx};

    use super::*;

    /// One axiom `Foo : Prop`.
    fn env_with_foo() -> Environment {
        let mut env = Environment::default();
        let prop = {
            let store = env.store_mut();
            let zero = store.level_zero(None).unwrap();
            store.expr_sort(None, zero).unwrap()
        };
        let foo = {
            let store = env.store_mut();
            let s = store.intern_str(None, "Foo").unwrap();
            store.name_str(None, None, s).unwrap()
        };
        env.admit_unchecked(ConstantInfo::Axiom(AxiomVal {
            val: ConstantVal {
                name: foo,
                level_params: vec![],
                ty: prop,
            },
            is_unsafe: false,
        }))
        .unwrap();
        env
    }

    /// `getSuccesses`' stage-3 `catch _` (`App.lean:2174-2185`) takes oracle
    /// errors only: a candidate whose pending work hits a seam (an omitted
    /// `autoParam`'s tactic) must rethrow it, not be dropped as a failure
    /// (spec Rule 1).
    #[test]
    fn stage_three_rethrows_a_non_oracle_error() {
        let env = env_with_foo();
        let view = env.view();
        let mut scratch = Store::scratch();
        let mctx = MetaCtx::new(
            view,
            &mut scratch,
            Config::default(),
            EnvExtensions::default(),
        );
        let mut elab = TermElabM::new(mctx, view);
        let foo = crate::builtin::op::mk_const_named(&mut elab, "Foo").unwrap();
        let prop = elab.mctx.infer_type(foo).unwrap();
        let snap = leanr_syntax::builtin::snapshot();
        let parsed = leanr_syntax::parse_term("Nat.zero", &snap);
        let syn = parsed.tree.root().first_child_or_token().unwrap();
        let kinds = (*parsed.tree.kinds).clone();
        let mut cands = Vec::new();
        for _ in 0..2 {
            let syn = syn.clone();
            let r = elab
                .observing(|e| {
                    let (_m, id) = e.mk_fresh_expr_mvar_of_kind(prop, MVarKind::Synthetic)?;
                    e.register_synthetic_mvar(
                        syn,
                        id,
                        SyntheticMVarKind::Tactic { param_name: None },
                    );
                    Ok(foo)
                })
                .unwrap();
            cands.push(r);
        }
        match get_successes(&mut elab, &cands, &kinds) {
            Err(ElabError::UnsupportedSyntax(_)) => {}
            other => panic!("the seam must propagate, got {other:?}"),
        }
    }
}
