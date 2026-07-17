//! Quotation term shapes (M3b2b Task 2). ORACLE-PORT `Lean/Parser/
//! Command.lean` (`Term.quot`, `Term.precheckedQuot`, `Command.quot` —
//! despite the filename, these three live in `Command.lean`, not
//! `Term.lean`; the pinned toolchain's own namespacing) and
//! `Lean/Parser/Term.lean` (`Term.dynamicQuot`, `Tactic.quot`/
//! `Tactic.quotSeq` — the latter two, despite living in `Term.lean`,
//! are declared OUTSIDE `namespace Term`, hence their `Tactic.`-
//! qualified kind names). No antiquot behavior inside is ported here
//! (Task 3); bodies just parse at depth+1.
//!
//! **The single biggest surprise, confirmed against the Step 1 dump
//! (`QuotBasic.stx.jsonl`)**: this is NOT one `Term.quot` production
//! whose body tries `termParser <|> many1Unbox commandParser` (what a
//! naive read of just `Term.lean`'s `dynamicQuot` neighbor might
//! suggest). The real oracle registers FOUR separate `@[builtin_term_
//! parser]` productions, each its own node kind, dispatched by this
//! engine's `longest_match` (no priority system — the oracle's
//! `low`/`default`/`default+1` annotations have no counterpart here;
//! every fixture line happens to have exactly one candidate that can
//! possibly succeed, so plain longest-match reproduces the oracle
//! choice without needing one):
//!
//! - `Lean.Parser.Term.quot` (`a`, `b`): `` `(f x) ``/`` `(fun x => x)
//!   ``, body a plain `termParser`.
//! - `Lean.Parser.Tactic.quot` (`c`): `` `(tactic| match h with | hp =>
//!   _) `` — its OWN dedicated leading token `` `(tactic| `` (a single
//!   atom, distinct from `` `( ``; the dump's atom span for line `c` is
//!   exactly `` `(tactic| `` with no trailing space, matching this
//!   codebase's established `sym()` convention of dropping a
//!   `leading_parser` string literal's pretty-print-only trailing
//!   space), so it never even competes with the other three at
//!   DISPATCH time — the lexer's own maximal munch already picks the
//!   longer token. (The fixture body is a real `Tactic.match`, NOT a
//!   bare unrecognized ident: `Tactic.unknown`'s `errorAtSavedPos`
//!   genuinely fails the parse in the real oracle too — confirmed the
//!   hard way, see `ByTac.lean`'s own module doc for the same call —
//!   so it's ineligible for an oracle-clean fixture line.)
//! - `Lean.Parser.Term.dynamicQuot` (`d`): `` `(term| 42) `` — the
//!   GENERIC ident-named-category fallback (`Prim::DynamicQuotBody`),
//!   sharing the bare `` `( `` token with `Term.quot`/`Command.quot`;
//!   disambiguated from them by `longest_match` (a plain `termParser`
//!   parsing `term| 42)` only ever consumes the bare ident `term`, then
//!   fails to find the required closing `")"` right after — see
//!   `dynamicQuot`'s own doc comment on `Prim::DynamicQuotBody`).
//! - `Lean.Parser.Command.quot` (`e`): `` `(#check 1) `` — body
//!   `many1Unbox commandParser`; `#check` isn't a term, so `Term.quot`'s
//!   alternative fails outright and this is the only survivor.
//!
//! `Term.precheckedQuot := "`" >> Term.quot` (double-backtick) is
//! genuinely out of scope: no fixture line uses it, and the dump
//! confirms line `a` is `Term.quot` directly, NOT precheckedQuot-
//! wrapped. `Tactic.quotSeq` (`` `(tactic| t1; t2) ``-style sequences)
//! is likewise unexercised and not ported.
//!
//! `withoutPosition` (every one of the four bodies) is omitted — this
//! engine has no `WithPosition` frame to be transparent THROUGH in the
//! first place unless one is explicitly pushed (see `Prim::WithPosition`),
//! and no fixture body exercises a column check that would prove
//! otherwise.
//!
//! `many1Unbox` (`Command.quot`'s body) needed a genuinely NEW
//! primitive, `Prim::Many1Unbox` — see its own doc comment in
//! `grammar/mod.rs` for why the existing `many1` combinator (which
//! ALWAYS wraps in a `null` node) can't reproduce the dump's 3-child
//! `Command.quot{ "`(", <command>, ")" }` shape for a single command.

use crate::grammar::*;

pub(super) fn register(b: &mut SnapshotBuilder) {
    // Term.quot := leading_parser "`(" >> withoutPosition (incQuotDepth
    // termParser) >> ")"` (Command.lean:20-21). Confirmed against the
    // QuotBasic dump lines `a`/`b`: `Lean.Parser.Term.quot` has exactly
    // 3 children (open atom, the term itself, close atom) — no extra
    // node wrap around the body.
    b.leading2(
        "term",
        "Lean.Parser.Term.quot",
        MAX_PREC,
        seq([sym("`("), inc_quot_depth(cat("term", 0)), sym(")")]),
    );
    // Command.quot := leading_parser low "`(" >> withoutPosition
    // (incQuotDepth (many1Unbox commandParser)) >> ")"` (Command.lean:
    // 50-51). Confirmed against dump line `e`: `Lean.Parser.Command.
    // quot` has exactly 3 children — the single `Command.check` node
    // sits directly as the 2nd child, no wrapping `null` (that's
    // `many1Unbox`'s whole point; see `Prim::Many1Unbox`).
    b.leading2(
        "term",
        "Lean.Parser.Command.quot",
        MAX_PREC,
        seq([
            sym("`("),
            inc_quot_depth(many1_unbox(cat("command", 0))),
            sym(")"),
        ]),
    );
    // Term.dynamicQuot := withoutPosition <| leading_parser "`(" >>
    // ident >> "| " >> incQuotDepth (parserOfStack 1) >> ")"`
    // (Term.lean:1028-1029). `Prim::DynamicQuotBody` folds the
    // `ident >> "| " >> incQuotDepth (category ..)` tail into one
    // engine-special primitive (the category is named by input text —
    // see its own doc comment); its runtime `"|"` check goes through
    // `expect_atom` directly rather than a `Prim::Symbol` node, so it
    // relies on `"|"` already being snapshot-wide registered by every
    // `matchAlt`-shaped production elsewhere (see `walk_symbols`'s
    // `DynamicQuotBody` arm in `grammar/mod.rs`). Confirmed against
    // dump line `d`: `Lean.Parser.Term.dynamicQuot` is 5 FLAT children
    // (open atom, ident, "|" atom, the category body, close atom) — no
    // extra node wrap around the `ident >> "|" >> body` tail.
    b.leading2(
        "term",
        "Lean.Parser.Term.dynamicQuot",
        MAX_PREC,
        seq([sym("`("), Prim::DynamicQuotBody, sym(")")]),
    );
    // Tactic.quot := leading_parser default+1 "`(tactic| " >>
    // withoutPosition (incQuotDepth tacticParser) >> ")"` (Term.lean:
    // 1123-1124, outside `namespace Term`). Confirmed against dump
    // line `c`: the open atom is the FUSED 9-byte token "`(tactic|"
    // (not "`(" + ident "tactic" + "|" separately) — this is Lean's own
    // per-category quotation convenience, a dedicated literal token,
    // not an instance of `dynamicQuot`'s generic ident-based mechanism.
    b.leading2(
        "term",
        "Lean.Parser.Tactic.quot",
        MAX_PREC,
        seq([sym("`(tactic|"), inc_quot_depth(cat("tactic", 0)), sym(")")]),
    );
}
