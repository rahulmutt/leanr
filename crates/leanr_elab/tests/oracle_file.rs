//! M4c-2a file-corpus differential gate (spec
//! `docs/superpowers/specs/2026-10-04-m4c2a-file-loop-design.md`
//! § Harness). Every committed `{id, src, cmds}` record of
//! `file-queries.jsonl` (`tests/fixtures/elab/dump_decls.lean files`) is
//! one header-less multi-command source; leanr's parser must split it into
//! exactly the oracle's commands.

mod support;

/// `wc -l tests/fixtures/elab/file-queries.jsonl` at the last deliberate
/// regen (M4c-2c-ii P1: 308). `>=`: adding a record is a one-line bump, not a
/// failing gate.
const CORPUS_FLOOR: usize = 308;

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
    // variable (`replaceBinderAnnotation`, `BuiltinCommand.lean:343`).
    let (at, m) = stop_seam("variable {α}");
    assert_eq!(at, 0);
    assert!(
        m.contains("binder-annotation update") && m.ends_with(" — later M4"),
        "{m}"
    );
    // `[inst]` naming an existing section variable is an update too
    // (`replaceBinderAnnotation`'s instBinder case): the second command.
    let (at, m) = stop_seam("variable {a : Type} [inst : Dflt a]\nvariable [inst]");
    assert_eq!(at, 1);
    assert!(
        m.contains("binder-annotation update") && m.ends_with(" — later M4"),
        "{m}"
    );
    // Oracle auto-binds `β` (`runTermElabM`'s `withAutoBoundImplicit`).
    let (at, m) = stop_seam("variable (x : β)");
    assert_eq!(at, 0);
    assert!(
        m.contains("`variable` binder") && m.ends_with(" — M4c-2c-ii"),
        "{m}"
    );
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

/// M4c-2c-ii P1 rows not yet passing: each task deletes its prefixes
/// (Task 4: `auto/ident` … `auto/with`; Task 5: `auto/level`; Task 6:
/// `auto/namedArg`; Task 7: `opt/`). Empty at the end of P1.
const PENDING: &[&str] = &[
    "auto/ident",
    "auto/mvar",
    "auto/neg",
    "auto/catch",
    "auto/with",
    "auto/level",
    "auto/namedArg",
    "opt/",
];

#[test]
fn oracle_file_gate() {
    let checked = support::run_file_corpus("file-queries.jsonl", |id| {
        !PENDING.iter().any(|p| id.starts_with(p))
    });
    let pending = std::fs::read_to_string(support::fixture_in("elab", "file-queries.jsonl"))
        .expect("corpus")
        .lines()
        .filter(|l| PENDING.iter().any(|p| l.contains(&format!("\"id\":\"{p}"))))
        .count();
    assert!(
        checked + pending >= CORPUS_FLOOR,
        "file corpus shrank: checked {checked} + pending {pending}, floor {CORPUS_FLOOR}. Check \
         `dump_decls.lean files`' stderr for a dropped record, or lower the floor deliberately."
    );
}
