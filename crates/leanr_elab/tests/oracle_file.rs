//! M4c-2a file-corpus differential gate (spec
//! `docs/superpowers/specs/2026-10-04-m4c2a-file-loop-design.md`
//! § Harness). Every committed `{id, src, cmds}` record of
//! `file-queries.jsonl` (`tests/fixtures/elab/dump_decls.lean files`) is
//! one header-less multi-command source; leanr's parser must split it into
//! exactly the oracle's commands.

mod support;

/// `wc -l tests/fixtures/elab/file-queries.jsonl` at the last deliberate
/// regen (term-level `open … in`: 490). `>=`: adding a record is a one-line bump,
/// not a failing gate.
const CORPUS_FLOOR: usize = 532;

#[test]
fn file_corpus_sources_parse_into_the_oracle_commands() {
    let text = std::fs::read_to_string(support::fixture_in("elab", "file-queries.jsonl"))
        .expect("committed file corpus");
    let mut n = 0;
    for line in text.lines().filter(|l| !l.trim().is_empty()) {
        let q: serde_json::Value = serde_json::from_str(line).expect("valid JSONL");
        let id = q["id"].as_str().expect("id");
        let src = q["src"].as_str().expect("src field");
        let want = q["cmds"].as_array().expect("cmds").len();
        let (_, cmds) = support::parse_commands(src);
        assert_eq!(
            cmds.len(),
            want,
            "{id}: leanr parses {} command(s), oracle {want}",
            cmds.len()
        );
        n += 1;
    }
    assert!(
        n >= CORPUS_FLOOR,
        "file corpus shrank: {n} < {CORPUS_FLOOR}"
    );
}

fn outcome(
    src: &str,
) -> (
    Vec<Vec<String>>,
    Option<(usize, leanr_elab::ElabError)>,
    usize,
) {
    support::with_file_elab(src, |ce, cmds, kinds| {
        let before = ce.env().len();
        let out = ce.elab_commands(cmds, kinds);
        let st = ce.env().store();
        let done = out
            .done
            .iter()
            .map(|ns| {
                ns.iter()
                    .map(|&n| support::name_to_string(st, None, Some(n)))
                    .collect()
            })
            .collect();
        // How many constants the run admitted in total.
        (done, out.stopped, ce.env().len() - before)
    })
}

fn stop_seam(src: &str) -> (usize, String) {
    match outcome(src).1 {
        Some((i, leanr_elab::ElabError::UnsupportedSyntax(m))) => (i, m),
        other => panic!("{src:?}: expected a seam stop, got {other:?}"),
    }
}

#[test]
fn set_option_other_names_are_later_m4_seams() {
    let (at, m) = stop_seam("set_option pp.all true");
    assert_eq!(at, 0);
    assert!(
        m.contains("set_option") && m.ends_with(" — later M4"),
        "{m}"
    );
}

#[test]
fn an_error_mid_file_stops_the_loop() {
    // Oracle: `la` logs a type mismatch and is still added (`errToSorry`),
    // then `lb` and `lc` elaborate. leanr stops at `la` (spec decision 2).
    let (done, stopped, added) =
        outcome("def la : Nat := True.intro\ndef lb : Nat := Nat.zero\ndef lc : Nat := lb");
    assert!(done.is_empty(), "{done:?}");
    match stopped {
        Some((0, e)) => assert_eq!(e.oracle_first_line().as_deref(), Some("Type mismatch")),
        other => panic!("expected a stop at command 0, got {other:?}"),
    }
    assert_eq!(added, 0, "nothing at or after the stop is admitted");
}

#[test]
fn a_mid_file_error_after_successes_keeps_them() {
    let (done, stopped, added) =
        outcome("def la : Nat := Nat.zero\ndef lb : Nat := True.intro\ndef lc : Nat := la");
    assert_eq!(done, vec![vec!["la".to_string()]]);
    assert!(matches!(stopped, Some((1, _))), "{stopped:?}");
    assert_eq!(added, 1, "only `la`");
}

#[test]
fn variable_seams_carry_their_slice() {
    // Oracle: `variable {α}` with no prior `α` declares a hole-typed
    // variable (`replaceBinderAnnotation` returns the binder itself,
    // `BuiltinCommand.lean:413`; `expandBinderType`, `Binders.lean:24-28`).
    let (at, m) = stop_seam("variable {α}");
    assert_eq!(at, 0);
    assert!(
        m.contains("expandBinderType") && m.ends_with(" — later M4"),
        "{m}"
    );
    // The residue of an update (`z`, `:405-411`) is a typeless binder too
    // (oracle row `vu/residue`: `u9` elaborates).
    let (at, m) = stop_seam("variable (x : Nat)\nvariable {x z}\ndef u9 : Nat := x");
    assert_eq!(at, 1);
    assert!(
        m.contains("expandBinderType") && m.ends_with(" — later M4"),
        "{m}"
    );
}

#[test]
fn variable_binders_auto_bind() {
    // Oracle: `elabVariable`'s sanity run is `withAutoBoundImplicit`
    // (`BuiltinCommand.lean:419-425`), for identifiers and universes.
    for src in ["variable (x : β)", "variable (α : Sort w)"] {
        let (done, stopped, _) = outcome(src);
        assert!(stopped.is_none(), "{src:?}: {stopped:?}");
        assert_eq!(done.len(), 1, "{src:?}");
    }
}

#[test]
fn omit_type_pattern_without_uid_errors() {
    // Rebuild branch: `[Wrap Nat]` matches the anonymous instance, which
    // has no uid (stale `sectionFVars`). The oracle prints a hygienic
    // hash name (`inst._@.…`) the gate cannot pin; leanr must still
    // error, never `Ok` (spec Amendment 2).
    let (_, stopped, _) = outcome("variable (h : Eq a a) [Wrap Nat]\nomit [Wrap Nat]");
    match stopped {
        Some((1, leanr_elab::ElabError::OmitUndeclared(n))) => {
            assert_ne!(n, "[anonymous]", "rendered as a message fvar");
        }
        other => panic!("{other:?}"),
    }
}

#[test]
fn other_commands_are_later_m4_seams() {
    for src in [
        "#check Nat",
        "#print Nat",
        "mutual\ndef la : Nat := Nat.zero\nend",
    ] {
        let (_, m) = stop_seam(src);
        assert!(m.ends_with(" — later M4"), "{src:?}: {m}");
    }
}

#[test]
fn empty_source_elaborates_nothing() {
    for src in ["", "-- just a comment\n", "/- block -/"] {
        let (done, stopped, _) = outcome(src);
        assert!(
            done.is_empty() && stopped.is_none(),
            "{src:?}: {done:?} {stopped:?}"
        );
    }
}

/// `lth/`: staged by the letToHave plan's Task 1; Task 5 removes it.
const PENDING: &[&str] = &["lth/"];

/// Rows whose divergence is a known pre-existing gap, gated by EXACT id:
/// `(id, reason)`. Each `auto/*` reason names an oracle-probed variant
/// WITHOUT auto-bound that diverges the same way (the inline variant source
/// is the reproducer; the 2026-10-05 scratch probe files are not
/// committed); the `lvl/*` rows are their own reproducers. An entry leaves
/// when its gap is fixed.
const KNOWN_GAPS: &[(&str, &str)] = &[];

#[test]
fn oracle_file_gate() {
    let is_pending = |id: &str| PENDING.iter().any(|p| id.starts_with(p));
    let is_known = |id: &str| KNOWN_GAPS.iter().any(|(k, _)| *k == id);
    let checked =
        support::run_file_corpus("file-queries.jsonl", |id| !is_pending(id) && !is_known(id));
    let corpus =
        std::fs::read_to_string(support::fixture_in("elab", "file-queries.jsonl")).expect("corpus");
    let pending = corpus
        .lines()
        .filter(|l| PENDING.iter().any(|p| l.contains(&format!("\"id\":\"{p}"))))
        .count();
    let mut known = 0;
    for (id, reason) in KNOWN_GAPS {
        assert!(
            !reason.is_empty() && !is_pending(id),
            "{id}: KNOWN_GAPS entry"
        );
        let n = corpus
            .lines()
            .filter(|l| l.contains(&format!("\"id\":\"{id}\"")))
            .count();
        assert_eq!(n, 1, "KNOWN_GAPS id {id} must name exactly one corpus row");
        known += n;
    }
    assert!(
        checked + pending + known >= CORPUS_FLOOR,
        "file corpus shrank: checked {checked} + pending {pending} + known {known}, floor \
         {CORPUS_FLOOR}. Check `dump_decls.lean files`' stderr for a dropped record, or lower \
         the floor deliberately."
    );
}
