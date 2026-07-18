//! The builtin grammar snapshot (spec §Architecture / builtin) —
//! Rust ports of the pinned toolchain's compiled `@[builtin_*_parser]`
//! set, per docs/superpowers/specs/2026-07-13-m3a-builtin-surface.md.
//! Kind names MUST match Lean's byte-for-byte (oracle equality).

pub mod attr;
pub mod command;
pub mod do_notation;
pub mod level;
pub mod tactic;
pub mod term;

use crate::grammar::{GrammarSnapshot, LeadingIdentBehavior, SnapshotBuilder};

/// The pre-registered builtin `SnapshotBuilder` — everything `snapshot()`
/// does up to (but not including) `finish()`. M3b2a Task 4: exposed so
/// `leanr_grammar` (imported-extension registration, downstream tasks)
/// can append entries — e.g. an imported module's interpreted
/// `notation`/`ParserDescr`-derived `Prim`s via `leading_prim`/
/// `trailing_prim` — onto the SAME builtin base before calling
/// `finish()` itself, rather than only being able to grow an
/// already-`finish`ed `GrammarSnapshot` (which has no builder-shaped
/// mutation API at all). `snapshot() == builder().finish()` by
/// construction (see `snapshot`, below) — proven behavior-identical by
/// `builder_finish_equals_builtin_snapshot`'s fingerprint-equality test.
pub fn builder() -> SnapshotBuilder {
    let mut b = SnapshotBuilder::new();
    // "module" is OUR OWN synthetic root kind — never oracle-compared
    // (canon.rs's `canon_jsonl` only emits the root's *children*: the
    // header, then each command in turn). It stands in for what real
    // Lean calls `Lean.Parser.Module.module`, a `leading_parser` the
    // toolchain itself documents as never actually run (`Module.lean`:
    // "We never actually run this parser but instead use the imperative
    // definitions...").
    b.kind("module");
    b.kind("Lean.Parser.Command.eoi");
    // M3b2b Task 4 — antiquot-splice suffix tokens (`many`/`sepBy`'s
    // `withAntiquotSpliceAndSuffix` alternative, `parse.rs`'s
    // `antiquot_splice`): these can't ride along with the rest of the
    // token table (every OTHER token is auto-collected by `finish()`'s
    // `walk_symbols` pass over the registered `Prim` tree — see that
    // fn's own doc comment — because it walks `Prim::Symbol` NODES a
    // real production's grammar contains); `antiquot_splice`'s suffix
    // atoms are parsed by bare `expect_atom` calls in `parse.rs` itself,
    // never wrapped in a `Prim::Symbol` any builtin production
    // registers, so they need this explicit registration or the
    // tokenizer would never maximal-munch them.
    // - `"*"` — ORACLE `many(p)`/`many1(p)`'s shared suffix (`Extra.lean:
    //   42,52,67`: `withAntiquotSpliceAndSuffix `many p (symbol "*")`).
    //   Pinned: `QuotSplice.stx.jsonl` line b (`f $args*`), atom span
    //   `[42,43]` — one char, one atom (no sibling registration collides
    //   with it: `?`/`[`/`]` are already registered by unrelated
    //   productions, e.g. `term.rs`'s synthetic-hole/binder-update/`open`
    //   rows).
    // - `",*"` — ORACLE `sepByElemParser p sep := withAntiquotSpliceAndSuffix
    //   `sepBy p (symbol (sep.trimAscii.copy ++ "*"))` (`Basic.lean:
    //   1895-1896`), instantiated here for `sep = ","` (`anonymousCtor`/
    //   `matchDiscr`'s own separator — `term.rs`/`tactic.rs`'s `sep_by1(
    //   .., ",")` call sites): pinned as ONE combined atom, not two
    //   (`,` then `*` separately) — `QuotSplice.stx.jsonl` lines a/c/d,
    //   atom spans `[17,19]`/`[64,66]`/`[102,104]`, each TWO bytes wide
    //   under one `"a"` span, confirming Lean's own maximal-munch
    //   registers the literal string `",*"` as a single token (same
    //   mechanism any other multi-char symbol like `"=>"`/`"::"` uses),
    //   not a token-table LOOKUP collision with the separately-registered
    //   bare `","` (`term.rs`/`tactic.rs`'s own `sep_by1(.., ",")`)
    //   forcing a two-token read. Only `sep = ","` is registered here —
    //   this crate's OTHER `sepBy`/`sepBy1` separators hardcoded directly
    //   in Rust (`"|"` — `term.rs:502`; `"▸"` — `term_app.rs:121`) still
    //   get their own `"|*"`/`"▸*"` combined-token registration on
    //   demand, when (if) a future fixture actually exercises a splice
    //   suffix at one of those positions — same "don't force it"
    //   discipline this crate already applies to
    //   `CATEGORY_LEAF_ANTIQUOT_NAMES` (`parse.rs`). This crate's builtin
    //   productions are hand-assembled via `SnapshotBuilder::leading2`/
    //   `trailing2` (`nd`/`seq`/`sep_by1` calls throughout `builtin/`),
    //   which deliberately do NOT run the M3b3 Task 8 suffix-derivation
    //   walk below — doing so would auto-register `"|*"`/`"▸*"` as a
    //   side effect of this refactor, an untested behavior change no
    //   oracle dump has pinned for THOSE two separators, so the gap
    //   documented here stays open for them on purpose.
    //
    //   M3b3 Task 8 CLOSES this gap for every OTHER separator, i.e. one
    //   a `syntax`/`macro` declaration introduces at the source level
    //   (same-file, via `Overlay::register`) or an imported module's
    //   `ParserDescr` carries (via `SnapshotBuilder::leading_prim`/
    //   `trailing_prim`/`scoped_leading_prim`/`scoped_trailing_prim`):
    //   `sepby_suffix_tokens` (`grammar/mod.rs`) walks a production's body
    //   for `SepBy`/`SepBy1` and derives `format!("{sep}*")` for each,
    //   generalizing the ONE hand-written case below (`",*"`) to an
    //   ARBITRARY separator — pinned against a real oracle dump by
    //   `StxSepCustom.lean`'s `sepBy(term, "|")` declaration (`"|*"`,
    //   `StxSepCustom.stx.jsonl`'s `sepBy.antiquot_suffix_splice`/
    //   `sepBy.antiquot_scope` lines). Failure mode while unregistered,
    //   named explicitly (M3b2b Task 4 review fix; still applies to the
    //   builtin `"|"`/`"▸"` cases above): this is NOT a hard error at
    //   parse time. `antiquot_splice`'s suffix-splice form (`parse.rs`)
    //   still runs `scope_body` and checks `top_level_is_antiquot` on
    //   whatever it produced, then attempts `expect_atom(suf, false)` for
    //   the combined suffix text (e.g. `"|*"`) — with no such token
    //   registered, the tokenizer can never maximal-munch it as one atom,
    //   so that `expect_atom` fails and is treated as "suffix doesn't
    //   apply" (see `antiquot_splice`'s own doc comment, alternative 2):
    //   the element's already-parsed result stands UNWRAPPED (no
    //   `.antiquot_suffix_splice` node), and the stray `|`/`*` text is
    //   left in the stream for whatever runs next to trip over — a
    //   silent misparse, not a diagnosed one.
    b.token("*");
    b.token(",*");
    // Each category's `LeadingIdentBehavior` (M3a Task 10 review Finding
    // 1) is read off its own `registerBuiltinParserAttribute` call site
    // in the pin — the `behavior` parameter defaults to `.default` when
    // omitted:
    //   - `command`  — `Extension.lean:595` (omitted → `.default`)
    //   - `term`     — `Extension.lean:590` (omitted → `.default`)
    //   - `level`    — `Level.lean:17` (omitted → `.default`)
    //   - `tactic`   — `Term/Basic.lean:33` (`.both`, explicit)
    //   - `doElem`   — `Do.lean:16` (omitted → `.default`)
    //   - `structInstFieldDecl` — `Term/Basic.lean:272` (omitted →
    //     `.default`)
    //   - `attr`     — `Attr.lean:20` (`.symbol`, explicit)
    //   - `prio`     — `Attr.lean:16` (`.both`, explicit)
    b.category("command", LeadingIdentBehavior::Default);
    b.category("term", LeadingIdentBehavior::Default);
    b.category("level", LeadingIdentBehavior::Default);
    b.category("tactic", LeadingIdentBehavior::Both);
    // `doElem` category (surface table: 27 rows, `Lean/Parser/Do.lean`)
    // — `do`-block statements (`let`/`for`/`if`/`match`/`return`/…),
    // populated by `do_notation::register` (M3a Task 9).
    b.category("doElem", LeadingIdentBehavior::Default);
    // `Term.structInst`'s field-decl slot recurses into its own tiny
    // category (surface table's "struct-instance-field-decl category",
    // 2 rows: `structInstFieldDef`/`structInstFieldEqns`) — registered
    // here alongside the others, populated by `term::register`.
    b.category("structInstFieldDecl", LeadingIdentBehavior::Default);
    // `attr`/`prio` categories (surface table's own `attr` category, 12
    // rows, + the `prio` misc singleton) — M3a Task 10: declModifiers'
    // `@[attr1, attr2]` slot and the `attribute` command both recurse
    // into `attr`; `Attr.simple`/`«instance»`/`default_instance`'s own
    // optional priority argument recurses into `prio`. `attr` = `.symbol`
    // is THE substantive fix of Task 10 review Finding 1 (see
    // `parse.rs::dispatch` and `LeadingIdentBehavior`'s own doc comment).
    b.category("attr", LeadingIdentBehavior::Symbol);
    b.category("prio", LeadingIdentBehavior::Both);
    // `stx` category (M3b2b Task 6, surface table's `syntax`-item
    // grammar, `Lean/Parser/Syntax.lean`'s `Syntax.paren`/`.cat`/
    // `.unary`/`.binary`/`.sepBy`/`.sepBy1`/`.atom`/`.nonReserved` +
    // the `+`/`*`/`?`/`,*` quantifier-suffix trailing productions,
    // `command_syntax.rs`) — `Syntax.lean:17`'s own registration,
    // `registerBuiltinParserAttribute \`builtin_syntax_parser
    // ``Category.stx .both`, is EXPLICIT `.both` (unlike `command`/
    // `term`/`level`/`doElem`/`structInstFieldDecl`, all omitted →
    // `.default`) — pinned here rather than left at the `#[default]`
    // `Default`, per this task's own brief instruction to read the
    // behavior off the oracle's category-registration call site
    // rather than assume.
    b.category("stx", LeadingIdentBehavior::Both);
    command::register(&mut b);
    level::register(&mut b);
    tactic::register(&mut b);
    term::register(&mut b);
    do_notation::register(&mut b);
    attr::register(&mut b);
    b
}

/// The builtin grammar snapshot (spec §Architecture / builtin): every
/// `@[builtin_*_parser]` this crate ports, pre-registered and finished.
/// `builder()` carries the whole body except `finish()` itself (M3b2a
/// Task 4), so this is now just that plus the one final call.
pub fn snapshot() -> GrammarSnapshot {
    builder().finish()
}
