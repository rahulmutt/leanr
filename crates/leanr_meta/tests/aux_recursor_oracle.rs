//! M4b-4c P1: `MetaCtx`'s `shouldElabAsElim` environment predicates
//! against the oracle's own answers for every constant of Elab0
//! (`tests/fixtures/elab/elim.jsonl`, written by `dump_elim.lean`).
//! `isRec` is a constant-kind test leanr_elab answers from
//! `ConstantInfo::Rec`; it is compared in leanr_elab's
//! `elim_info_oracle.rs`, not here.

mod support;

use leanr_kernel::bank::Store;
use leanr_meta::{Config, EnvExtensions, MetaCtx};
use serde_json::Value;
use support::*;

#[test]
fn aux_recursor_predicates_match_the_oracle_dump() {
    let r = replay_fixture_in("elab", "Elab0.olean");
    let view = r.env.view();
    let mut scratch = Store::scratch();
    let base = Some(view.store);
    let text = std::fs::read_to_string(fixture_in("elab", "elim.jsonl")).unwrap();
    let recs: Vec<Value> = text
        .lines()
        .map(|l| serde_json::from_str(l).unwrap())
        .collect();
    let ids: Vec<_> = recs
        .iter()
        .map(|rec| decode_name(&mut scratch, base, rec["n"].as_str().unwrap()))
        .collect();
    let ctx = MetaCtx::new(
        view,
        &mut scratch,
        Config::default(),
        EnvExtensions {
            aux_recs: &r.aux_recs,
            elab_as_elim: &r.elab_as_elim,
            ..Default::default()
        },
    );
    let mut failures = Vec::new();
    for (rec, &id) in recs.iter().zip(&ids) {
        let n = rec["n"].as_str().unwrap();
        let got = [
            ("aux", ctx.is_aux_recursor(id)),
            ("casesOn", ctx.is_cases_on_recursor(id)),
            ("recOn", ctx.is_rec_on_recursor(id)),
            ("brecOn", ctx.is_brec_on_recursor(id)),
            ("tag", ctx.has_elab_as_elim_tag(id)),
        ];
        for (k, g) in got {
            let want = rec[k].as_bool().unwrap();
            if g != want {
                failures.push(format!("{n}.{k}: leanr={g} oracle={want}"));
            }
        }
    }
    assert!(
        recs.len() > 800,
        "elim.jsonl covers all of Elab0: {}",
        recs.len()
    );
    assert!(
        failures.is_empty(),
        "{} divergences:\n{}",
        failures.len(),
        failures.join("\n")
    );
}
