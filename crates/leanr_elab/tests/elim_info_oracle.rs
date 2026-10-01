//! M4b-4c P1: `get_elab_elim_info` and the `isRec` disjunct against the
//! oracle for EVERY constant of Elab0 (`tests/fixtures/elab/elim.jsonl`,
//! `dump_elim.lean`). Errors compare by the oracle message's first line.
//!
//! One `TermElabM` serves every record (replaying `Elab0` per record
//! would cost a replay ×878); each call runs inside an mctx
//! checkpoint/rollback, and `get_elab_elim_expr_info` restores the
//! `lctx` itself. The answers do not depend on mvar numbering.

mod support;

use leanr_elab::app::elim_info::get_elab_elim_info;
use leanr_elab::error::ElabError;
use leanr_elab::TermElabM;
use serde_json::Value;

/// Records that diverge for a reason unrelated to `getElabElimInfo`.
/// Each must still diverge (asserted below), so the list cannot rot.
const KNOWN_GAPS: &[(&str, &str)] = &[
    (
        "lcAny",
        "unsafe axiom: replay admits no unsafe constants (leanr_kernel replay.rs:93), \
         so the constant is unknown to leanr",
    ),
    ("lcErased", "unsafe axiom: see lcAny"),
    ("lcVoid", "unsafe axiom: see lcAny"),
];

/// The record's divergence from the oracle, if any.
fn divergence(elab: &mut TermElabM, rec: &Value) -> Option<String> {
    let n = rec["n"].as_str().unwrap();
    let id = support::name_id(elab, n);
    let mut out = Vec::new();
    let is_rec = matches!(elab.view.get(id), Some(leanr_kernel::ConstantInfo::Rec(_)));
    if is_rec != rec["rec"].as_bool().unwrap() {
        out.push(format!("{n}.rec: leanr={is_rec}"));
    }
    let want = &rec["info"];
    let snap = elab.mctx.checkpoint();
    let got = get_elab_elim_info(elab, id);
    elab.mctx.rollback(snap);
    match (got, want.get("err")) {
        (Ok(i), None) => {
            let wm = want["motive"].as_u64().unwrap() as usize;
            let wj: Vec<usize> = want["majors"]
                .as_array()
                .unwrap()
                .iter()
                .map(|v| v.as_u64().unwrap() as usize)
                .collect();
            if i.motive_pos != wm || i.majors_pos != wj {
                out.push(format!(
                    "{n}: leanr motive={} majors={:?}; oracle motive={wm} majors={wj:?}",
                    i.motive_pos, i.majors_pos
                ));
            }
        }
        (Err(ElabError::Eliminator { reason }), Some(w)) => {
            if reason.oracle_first_line() != w.as_str().unwrap() {
                out.push(format!("{n}: leanr err {reason:?}; oracle {w}"));
            }
        }
        (got, _) => out.push(format!("{n}: leanr {got:?}; oracle {want}")),
    }
    (!out.is_empty()).then(|| out.join("; "))
}

#[test]
fn elab_elim_info_matches_the_oracle_dump() {
    let text = std::fs::read_to_string(support::fixture_in("elab", "elim.jsonl")).unwrap();
    let recs: Vec<Value> = text
        .lines()
        .map(|l| serde_json::from_str(l).unwrap())
        .collect();
    assert!(
        recs.len() > 800,
        "elim.jsonl covers all of Elab0: {}",
        recs.len()
    );
    // Non-vacuity: the success arm is exercised, not only the
    // "unexpected eliminator resulting type" arm.
    let oks = recs
        .iter()
        .filter(|r| r["info"].get("err").is_none())
        .count();
    assert!(oks > 100, "only {oks} eliminator records");
    let mut failures = Vec::new();
    support::with_elab_env(|elab| {
        for rec in &recs {
            let n = rec["n"].as_str().unwrap();
            let d = divergence(elab, rec);
            match (KNOWN_GAPS.iter().any(|(g, _)| *g == n), d) {
                (false, Some(d)) => failures.push(d),
                (true, None) => failures.push(format!("{n}: listed in KNOWN_GAPS but now agrees")),
                _ => {}
            }
        }
    });
    for (g, _) in KNOWN_GAPS {
        assert!(
            recs.iter().any(|r| r["n"] == *g),
            "KNOWN_GAPS lists {g}, absent from elim.jsonl"
        );
    }
    assert!(
        failures.is_empty(),
        "{} divergences:\n{}",
        failures.len(),
        failures.join("\n")
    );
}
