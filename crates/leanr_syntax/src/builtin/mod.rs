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
