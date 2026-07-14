//! The `tactic` category (surface table: 6 rows, `Lean/Parser/
//! Tactic.lean` + `Lean/Parser/Command.lean`'s tactic-scoped `«open»`/
//! `«set_option»`) + the `tacticSeq`/`tacticSeq1Indented`/
//! `tacticSeqBracketed`/`tacticSeqIndentGt` machinery (`Lean/Parser/
//! Term/Basic.lean`) `Term.byTactic` needs. ORACLE-PORT, cross-checked
//! against fresh oracle dumps (task-9 report has the probe
//! transcripts) — the builtin tactic set is deliberately TINY:
//! elaborating any interesting tactic body needs `Init`-declared
//! tactics (`exact`/`intro`/`simp`/…), M3b's job. This task's `by`-block
//! fixture coverage is therefore syntactic — `by` + `tacticSeq` +
//! `«match»`/`introMatch`/`nestedTactic`, not tactic breadth (spec's own
//! scope line).
//!
//! **Deferred, with reason**: `Tactic.«open»`/`Tactic.«set_option»`
//! (`Command.lean:1032,1037` — `open Foo in <tactic>`/`set_option .. in
//! <tactic>`) need the SAME `... in <command|term|tactic>` wrapper
//! machinery `term.rs`'s own `Term.«open»`/`Term.«set_option»` rows
//! defer for (Task 10's real command dispatcher); the task-9 brief's
//! own enumeration of "the builtin tactic set" names only `unknown`/
//! `nestedTactic`/`«match»`/`introMatch` — these two aren't in it.
//!
//! **`«unknown»`'s `errorAtSavedPos`, NOT modeled**: the oracle's
//! `errorAtSavedPos "unknown tactic" true` genuinely injects a
//! Parser-level message (confirmed: a fresh `lean` run over `by foo`
//! reports `error: unknown tactic` — NOT just an elaboration diagnostic;
//! task-9 report has the probe). This port still parses the SAME tree
//! shape (an `ident` wrapped in `Lean.Parser.Tactic.unknown`,
//! ALWAYS-succeeding — never pushed to `self.errors`, since that Vec
//! models genuine parse failures, not this row's semantic-only
//! diagnostic), but never fires the message itself — there is no
//! `Prim` for "succeed, but leave a note". No COMMITTED fixture uses an
//! unrecognized tactic name (that's the whole reason `ByTac.lean`
//! bottoms every tactic body out in `«match» ... => _`/`introMatch ...
//! => _` instead — the honest caveat the task brief itself calls out),
//! so this divergence never surfaces in the golden gate; recorded here
//! for anyone who later feeds this row a non-clean fixture.

use super::term::{match_alts, match_discr, nd, synthetic_hole, term_hole};
use crate::grammar::*;
use std::sync::Arc;

// ================================================================
// tacticSeq machinery (`Term/Basic.lean`) — Term.byTactic's body, and
// `matchRhs`'s own `tacticSeq` alternative.
// ================================================================

/// `tacticSeq1Indented := leading_parser sepBy1IndentSemicolon
/// tacticParser`.
fn tactic_seq1_indented(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Tactic.tacticSeq1Indented");
    nd(k, sep_by1_indent(cat("tactic", 0), ";"))
}
/// `tacticSeqBracketed`'s UNWRAPPED body — hoisted out of
/// `tactic_seq_bracketed` below so `register`'s `nestedTactic` row (a
/// BARE alias of `tacticSeqBracketed`, see its own doc comment) can
/// register the identical shape as its own tactic-category leading
/// candidate via `leading2` (which does its own node-wrap), without a
/// double-wrap-then-unwrap dance.
fn tactic_seq_bracketed_body() -> Prim {
    seq([sym("{"), sep_by_indent(cat("tactic", 0), ";"), sym("}")])
}
/// `tacticSeqBracketed := leading_parser "{ " >> sepByIndentSemicolon
/// tacticParser >> ppDedent ppLine >> "}"`.
fn tactic_seq_bracketed(b: &mut SnapshotBuilder) -> Prim {
    let k = b.kind("Lean.Parser.Tactic.tacticSeqBracketed");
    nd(k, tactic_seq_bracketed_body())
}
/// `tacticSeq := leading_parser tacticSeqBracketed <|> tacticSeq1Indented`
/// — bare `leading_parser`, so this DOES double-wrap (confirmed: a
/// fresh dump of `by match h with | hp => nested (hp)` shows
/// `Lean.Parser.Tactic.tacticSeq{ Lean.Parser.Tactic.tacticSeq1Indented{
/// .. } }`, task-9 report) — unlike `Term.doSeq`, which bypasses its own
/// wrap via `withAntiquot`.
pub(super) fn tactic_seq(b: &mut SnapshotBuilder) -> Prim {
    let bracketed = tactic_seq_bracketed(b);
    let indented = tactic_seq1_indented(b);
    let k = b.kind("Lean.Parser.Tactic.tacticSeq");
    nd(k, or_else([bracketed, indented]))
}
/// `tacticSeqIndentGt := withAntiquot (..) <| node ``tacticSeq <|
/// tacticSeqBracketed <|> (checkColGt >> tacticSeq1Indented) <|> node
/// ``tacticSeq1Indented pushNone` — `Term.byTactic`'s ONLY call site.
/// The explicit `node \`\`tacticSeq (...)`  reuses the SAME kind name
/// plain `tacticSeq` wraps in (not a distinct `tacticSeqIndentGt` kind);
/// the final `pushNone` fallback (`= mkNullNode`, an always-empty
/// `null`) is `opt(never())`'s established idiom, matching the empty
/// tactic-sequence-on-elaboration-error behavior the oracle's own doc
/// comment describes — never hit by a clean fixture (every `by` this
/// port's fixtures use has a real, properly-indented tactic).
pub(super) fn tactic_seq_indent_gt(b: &mut SnapshotBuilder) -> Prim {
    let bracketed = tactic_seq_bracketed(b);
    let indented = tactic_seq1_indented(b);
    let indented_k = b.kind("Lean.Parser.Tactic.tacticSeq1Indented");
    let k = b.kind("Lean.Parser.Tactic.tacticSeq");
    nd(
        k,
        or_else([
            bracketed,
            seq([Prim::CheckColGt, indented]),
            nd(indented_k, opt(never())),
        ]),
    )
}

/// `matchRhs := Term.hole <|> Term.syntheticHole <|> tacticSeq`
/// (Tactic.lean:34) — `«match»`/`introMatch`'s shared rhs; the base
/// case every `by`-block fixture bottoms a tactic-mode `match`/`intro`
/// alt out in (`| pat => _`), since the builtin tactic set is otherwise
/// too thin to end a `tacticSeq` without an unrecognized-tactic
/// diagnostic (see this file's module doc comment).
fn match_rhs(b: &mut SnapshotBuilder) -> Prim {
    let hole = term_hole(b);
    let synth = synthetic_hole(b);
    let seq_p = tactic_seq(b);
    or_else([hole, synth, seq_p])
}
/// `Tactic.matchAlts := Term.matchAlts (rhsParser := matchRhs)` —
/// shared by `«match»`/`introMatch` (Tactic.lean:35).
fn tactic_match_alts(b: &mut SnapshotBuilder) -> Prim {
    let rhs = match_rhs(b);
    match_alts(b, rhs)
}

// ================================================================
// The `tactic` category (4/6 rows — see module doc comment for the
// deferred 2).
// ================================================================

pub fn register(b: &mut SnapshotBuilder) {
    // «unknown» := leading_parser withPosition (ident >>
    // errorAtSavedPos "unknown tactic" true) — see module doc comment
    // for the `errorAtSavedPos` divergence (not modeled: this always
    // succeeds, never pushes to `self.errors`).
    b.leading2(
        "tactic",
        "Lean.Parser.Tactic.unknown",
        MAX_PREC,
        Prim::WithPosition(Arc::new(Prim::Ident)),
    );
    // nestedTactic := tacticSeqBracketed — a BARE alias (no
    // `leading_parser` of its own, so NO extra node: confirmed against
    // a fresh dump of `by tac1\n{ tac2 }` — the bracketed block is a
    // bare `Lean.Parser.Tactic.tacticSeqBracketed` node, never wrapped
    // in a further `nestedTactic` kind; task-9 report). Registering the
    // SAME `tactic_seq_bracketed(b)` shape a second time (once here,
    // once inside `tactic_seq`/`tactic_seq_indent_gt` above) is exactly
    // what the oracle's own `nestedTactic := tacticSeqBracketed`
    // (literal parser-value reuse, same prec) does.
    b.leading2(
        "tactic",
        "Lean.Parser.Tactic.tacticSeqBracketed",
        MAX_PREC,
        tactic_seq_bracketed_body(),
    );
    // «match» := leading_parser:leadPrec "match " >> optional
    // generalizingParam >> optional motive >> sepBy1 matchDiscr ", " >>
    // " with " >> ppDedent matchAlts. `generalizingParam`/`motive` not
    // transcribed (no fixture uses either) — same always-empty-optional
    // idiom `term.rs`'s `register_match` already established.
    let discr = match_discr(b);
    let alts = tactic_match_alts(b);
    b.leading2(
        "tactic",
        "Lean.Parser.Tactic.match",
        LEAD_PREC,
        seq([
            sym("match"),
            opt(never()),
            opt(never()),
            sep_by1(discr, ","),
            sym("with"),
            alts,
        ]),
    );
    // introMatch := leading_parser nonReservedSymbol "intro" >>
    // matchAlts.
    let alts = tactic_match_alts(b);
    b.leading2(
        "tactic",
        "Lean.Parser.Tactic.introMatch",
        MAX_PREC,
        seq([Prim::NonReservedSymbol("intro".into()), alts]),
    );
}

#[cfg(test)]
mod tests {
    use crate::builtin;
    use crate::parse_module;

    fn parse_ok(src: &str) -> String {
        let snap = builtin::snapshot();
        let full = format!("prelude\n\n{src}");
        let result = parse_module(&full, &snap);
        assert!(
            result.errors.is_empty(),
            "expected clean parse of {src:?}, got {:?}",
            result.errors
        );
        assert_eq!(result.tree.text(), full, "round-trip failed for {src:?}");
        crate::canon::canon_jsonl(&result.tree)
    }

    #[test]
    fn smoke_by_tactic_match() {
        let out = parse_ok("def t1 := fun (h : P) => by\n  match h with\n  | hp => _");
        assert!(out.contains("Lean.Parser.Term.byTactic"), "{out}");
        assert!(out.contains("Lean.Parser.Tactic.tacticSeq"), "{out}");
        assert!(
            out.contains("Lean.Parser.Tactic.tacticSeq1Indented"),
            "{out}"
        );
        assert!(out.contains("Lean.Parser.Tactic.match"), "{out}");
    }

    #[test]
    fn smoke_by_tactic_intro_match() {
        let out = parse_ok("def t2 := fun (h : P) => by\n  intro\n  | hp => _");
        assert!(out.contains("Lean.Parser.Tactic.introMatch"), "{out}");
    }

    #[test]
    fn smoke_nested_tactic_bracket() {
        let out = parse_ok(
            "def t3 := fun (h : P) => by\n  match h with\n  | hp => _\n  { match h with\n    | hp2 => _ }",
        );
        assert!(
            out.contains("Lean.Parser.Tactic.tacticSeqBracketed"),
            "{out}"
        );
    }

    #[test]
    fn smoke_show_by_tactic_prime() {
        let out = parse_ok("def t4 := fun (h : P) => show P by\n  match h with\n  | hp => _");
        assert!(out.contains("Lean.Parser.Term.byTactic'"), "{out}");
    }
}
