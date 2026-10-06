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
    // ... and a universe name the same way (`Level.lean:79-86`), never
    // the body's "unknown universe level" (not a corpus row: P2's).
    let (at, m) = stop_seam("variable (α : Sort w)");
    assert_eq!(at, 0);
    assert!(
        m.contains("unbound universe `w` in a `variable` binder") && m.ends_with(" — M4c-2c-ii"),
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
/// `auto/namedArg`; Task 7: `opt/`). Empty: P1 complete.
const PENDING: &[&str] = &[];

/// Rows whose divergence is a pre-existing gap outside auto-bound, gated
/// by EXACT id: `(id, reason)`. Each reason names an oracle-probed variant
/// WITHOUT auto-bound that diverges the same way (scratch probes
/// `target/m4c2ciiprobe/v.jsonl`, `v2.jsonl`, 2026-10-05). Survives P1;
/// an entry leaves when its gap is fixed.
const KNOWN_GAPS: &[(&str, &str)] = &[
    (
        "auto/negDependsExplicit",
        "coercion gap: leanr StuckCoercion, oracle `Application type mismatch` (v2.jsonl \
         v/depNoAuto: `def f2 (y : _) (β : Type) (h : Eq (y : β) y) : Nat := Nat.zero`)",
    ),
    (
        "auto/negDependsExplicitAx",
        "coercion gap: leanr StuckCoercion, oracle `Application type mismatch` (v2.jsonl \
         v/depNoAutoAx: `axiom f2a (y : _) (β : Type) (h : Eq (y : β) y) : Nat`)",
    ),
    (
        "auto/catchInst",
        "resolution gap: dotted `Wrap.val` (no such field) is `Unknown identifier` in leanr, \
         `Unknown constant` in the oracle (v2.jsonl v/instNoAuto2: \
         `axiom f5 (h : Wrap.val Nat) : Nat`)",
    ),
    (
        "auto/withUsedVarThm",
        "level gap: header type has `Eq.{max(u_1,1)}`, oracle `Eq.{max(1,u_1)}` (v.jsonl \
         v/thmSortHole: `variable {β : Type} (b : β)` + `theorem t1 {α : Sort _} (x : α) : \
         Eq (PProd.mk x b) (PProd.mk x b) := rfl`)",
    ),
];

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
