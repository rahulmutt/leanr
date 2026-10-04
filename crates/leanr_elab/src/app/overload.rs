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
