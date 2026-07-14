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
//! **`Tactic.«open»`/`Tactic.«set_option»`, now real (M3a Task 10)**:
//! (`Command.lean:1032,1037` — `open Foo in <tactic>`/`set_option .. in
//! <tactic>`) share the same `Command.openDecl`/`Command.optionValue`
//! sub-grammar the command-category `«open»`/`«set_option»` use
//! (re-exported from `command.rs`) — 2 of the 4 "wrapper rows owned by
//! nobody in writing" Task 9's review flagged (the other 2,
//! `Term.«open»`/`Term.«set_option»`, register into the `term`
//! category, `term.rs`). Previously deferred pending Task 10's command
//! dispatcher (see this file's original module doc comment); the
//! task-9 brief's own enumeration of "the builtin tactic set" as just
//! `unknown`/`nestedTactic`/`«match»`/`introMatch` predates this task's
//! discovery that these two belong here too.
//!
//! **`«unknown»`'s `errorAtSavedPos`, now modeled (Task 9 review finding
//! 2 fix)**: the oracle's `errorAtSavedPos "unknown tactic" true`
//! genuinely injects a Parser-level message (confirmed: a fresh `lean`
//! run over `by foo` reports `error: unknown tactic` — NOT just an
//! elaboration diagnostic; task-9 report has the probe). A prior
//! version of this port parsed the SAME tree shape (an `ident` wrapped
//! in `Lean.Parser.Tactic.unknown`) but ALWAYS succeeded silently —
//! never pushing to `self.errors` — which meant `by foo` parsed clean
//! with zero diagnostics: the tactic category accepted any identifier
//! as a valid tactic, defeating the one row the M3a builtin-surface
//! spec assigns to prove "parse errors are values" for tactics (spec
//! ~L408/L504). The dedicated `Prim::UnknownTacticIdent` (see its own
//! doc comment and `parse.rs`'s interpreter arm) now pushes a
//! `ParseError` (code `E0301`, msg "unknown tactic") at the ident's
//! start, alongside an `EmitMissing` node matching `errorAtSavedPos`'s
//! `pushMissing` side effect — this production still always SUCCEEDS
//! (never aborts the whole parse), matching this crate's "parse errors
//! are values" architecture rather than the oracle's genuine parser-
//! level failure; see the interpreter arm for the remaining documented
//! divergences (position-of-report rounding, no backward position
//! rewind). No COMMITTED golden fixture uses an unrecognized tactic
//! name (that's the whole reason `ByTac.lean` bottoms every tactic body
//! out in `«match» ... => _`/`introMatch ... => _` instead — the honest
//! caveat the task brief itself calls out); coverage for THIS row lives
//! in a Rust unit test instead (`unknown_tactic_reports_error_and_round_
//! trips`, this file's test module). NOT because the oracle CLI itself
//! rejects the source — checked directly (`lean --run
//! tests/fixtures/syntax/dump_syntax.lean` over a scratch `by foo`
//! file): it exits 0 and dumps a tree (`dump_syntax.lean` never
//! inspects the parser's message log, only the `Syntax` value, so a
//! recovered parse error doesn't stop it), and that dump's
//! `Lean.Parser.Tactic.unknown` node is exactly `[ident "foo",
//! <missing>]`, confirming this fix's tree shape byte-for-byte. The
//! real blocker is `tests/oracle_golden.rs`'s own harness invariant:
//! ANY fixture with a committed `.stx.jsonl` dump is asserted
//! `result.errors.is_empty()` (that assertion is what backs "oracle-
//! compared fixtures must parse clean" for the other 7 fixtures) — a
//! committed dump for this row would trip that assertion by design,
//! since this row's whole point is a NON-empty `errors`. Loosening
//! that harness invariant to allow specific expected-error fixtures is
//! out of scope for this fix wave (it would weaken the guarantee for
//! every other committed fixture too); a plain Rust test asserting
//! node kind + error + round-trip directly is the narrower fix.

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
    // errorAtSavedPos "unknown tactic" true) — Task 9 review finding 2
    // fix: `Prim::UnknownTacticIdent` is the dedicated primitive that
    // ports this row's whole body, INCLUDING the `errorAtSavedPos`
    // diagnostic (a prior version stopped at a bare `WithPosition(Ident)`,
    // silently accepting ANY identifier as a valid tactic with zero
    // diagnostics — see module doc comment, updated alongside this fix,
    // for what's now modeled vs. still deliberately divergent).
    b.leading2(
        "tactic",
        "Lean.Parser.Tactic.unknown",
        MAX_PREC,
        Prim::WithPosition(Arc::new(Prim::UnknownTacticIdent)),
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

    // Tactic.«open»/Tactic.«set_option» (M3a Task 10 — the two of the
    // Task 9-review's 4 "wrapper rows owned by nobody in writing" that
    // land in the `tactic` category; `Command.lean:1032-1038`, DISTINCT
    // kinds from both the command-category and term-category `«open»`/
    // `«set_option»` despite sharing names and the same `Command.
    // openDecl`/`Command.optionValue` sub-grammar (re-exported from
    // `command.rs`, same reuse `term.rs`'s own copies use). Previously
    // deferred (see this file's own module doc comment, written before
    // Task 10's command dispatcher existed) — now real.
    let decl = super::command::open_decl(b);
    let seq_p = tactic_seq(b);
    b.leading2(
        "tactic",
        "Lean.Parser.Tactic.open",
        LEAD_PREC,
        seq([sym("open"), decl, sym("in"), seq_p]),
    );
    let value = super::command::option_value();
    let ident_dot = super::command::ident_with_partial_trailing_dot();
    let seq_p = tactic_seq(b);
    b.leading2(
        "tactic",
        "Lean.Parser.Tactic.set_option",
        LEAD_PREC,
        seq([sym("set_option"), ident_dot, value, sym("in"), seq_p]),
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

    /// Task 9 review finding 2 regression: an unrecognized tactic name
    /// must round-trip through `Lean.Parser.Tactic.unknown` (an `ident`
    /// PLUS a `.missing` sibling — `errorAtSavedPos`'s `pushMissing`
    /// side effect, see `Prim::UnknownTacticIdent`'s doc comment) AND
    /// yield a diagnostic — the whole property this row exists to make
    /// testable ("parse errors are values" — M3a builtin-surface spec
    /// ~L408/L504). Not committed as a golden `.stx.jsonl` fixture: the
    /// oracle CLI itself tolerates this source fine (checked directly,
    /// see module doc comment), but `tests/oracle_golden.rs`'s harness
    /// asserts `result.errors.is_empty()` for ANY fixture with a
    /// committed dump, which this row's very point (a non-empty
    /// `errors`) would trip — so this coverage lives here instead.
    #[test]
    fn unknown_tactic_reports_error_and_round_trips() {
        let snap = builtin::snapshot();
        let src = "prelude\n\ndef t1 := fun (h : A) => by foo";
        let result = parse_module(src, &snap);

        // Round-trip: byte-exact, same invariant every fixture (clean
        // or not) is held to.
        assert_eq!(result.tree.text(), src, "round-trip failed");

        // Diagnostic: exactly one error, the stable E0301 (unexpected-
        // token) family — no new code minted, per the review finding.
        assert_eq!(
            result.errors.len(),
            1,
            "expected exactly one diagnostic, got {:?}",
            result.errors
        );
        assert_eq!(result.errors[0].code, "E0301");
        assert_eq!(result.errors[0].msg, "unknown tactic");

        // Tree shape: `Lean.Parser.Tactic.unknown{ ident "foo",
        // <missing> }` — matches a fresh oracle dump byte-for-byte
        // (`lean --run tests/fixtures/syntax/dump_syntax.lean` over
        // `by foo`, probed while implementing this fix): its
        // `Lean.Parser.Tactic.unknown` node is exactly
        // `[{"i":"foo",...},{"k":"<missing>"}]`.
        let out = crate::canon::canon_jsonl(&result.tree);
        assert!(out.contains(r#""k":"Lean.Parser.Tactic.unknown""#), "{out}");
        assert!(out.contains(r#""i":"foo""#), "{out}");
        assert!(out.contains(r#""k":"<missing>""#), "{out}");
    }

    /// M3a Task 10 review Finding 3 — investigated, NOT reproducible as
    /// stated. The finding claimed `by match z with | a => a` parses to
    /// a "spurious trailing `Tactic.unknown` + E0301 ... on VALID
    /// input" (a false error the golden gate's zero-error assertion
    /// would trip). Directly checked against the pinned oracle CLI
    /// (`lean --run tests/fixtures/syntax/dump_syntax.lean` — NOT just
    /// this crate's own tests) over exactly this shape
    /// (`def f (z : Nat) : Nat := by match z with\n  | a => a\n`): the
    /// real compiler ALSO reports a single parser-level "unknown
    /// tactic" diagnostic (`lean`'s own CLI: "error: unknown tactic")
    /// and the dump's tree is BYTE-IDENTICAL to this crate's own
    /// output — one `Lean.Parser.Tactic.unknown{ident "a", <missing>}`
    /// node, nested exactly once inside the match alt's RHS (`matchRhs
    /// := Term.hole <|> Term.syntheticHole <|> tacticSeq`,
    /// `Tactic.lean:34` — a bare `a` matches neither `hole` nor
    /// `syntheticHole`, so it falls through to `tacticSeq`, same as
    /// this port). This is expected: `a` is not a registered builtin
    /// tactic in EITHER engine (this crate's tactic set deliberately
    /// excludes `Init`-declared tactics like `exact`, per this file's
    /// own module doc comment and the M3a/M3b scope line) — NOT a
    /// false error, and not something a "zero errors" fixture could
    /// ever cover (the oracle itself doesn't parse it clean). No
    /// registration-order/dispatch-tie mechanism (`longest_match`,
    /// `sep_by_indent`'s loop) was found to leak errors from a
    /// discarded/losing candidate either: `Ps::restore` truncates both
    /// `events` AND `errors` back to the shared savepoint at the START
    /// of every `longest_match` iteration (parse.rs), so a losing
    /// candidate's side effects never survive to contaminate the
    /// winner or a sibling attempt.
    ///
    /// The regression coverage the finding actually asked for — "match
    /// as the WHOLE tactic block", zero errors — already exists:
    /// `ByTac.lean`'s committed `t1` (`by\n  match h with\n  | hp =>
    /// _`) is exactly that shape (a single tactic-mode `match`, no
    /// other tactics before or after it in the same `tacticSeq`,
    /// bottoming out in `Term.hole` per the established convention),
    /// oracle-verified byte-exact by the golden gate. This test locks
    /// in the SAME zero-error property directly (not via a fixture,
    /// since the true "valid" input already has fixture coverage) for
    /// extra assurance the tacticSeq loop cleanly terminates right
    /// after a `match` tactic with no trailing phantom tactic attempt.
    #[test]
    fn match_as_the_whole_tactic_block_is_zero_error_when_it_bottoms_out_validly() {
        let snap = builtin::snapshot();
        let src = "prelude\n\ndef t1 := fun (h : A) => by\n  match h with\n  | hp => _\n";
        let result = parse_module(src, &snap);
        assert_eq!(result.tree.text(), src, "round-trip failed");
        assert!(
            result.errors.is_empty(),
            "a valid match-as-whole-tactic-block must be zero-error, got {:?}",
            result.errors
        );
    }
}
