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

use crate::grammar::{GrammarSnapshot, SnapshotBuilder};

pub fn snapshot() -> GrammarSnapshot {
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
    b.category("command");
    b.category("term");
    b.category("level");
    b.category("tactic");
    // `doElem` category (surface table: 27 rows, `Lean/Parser/Do.lean`)
    // — `do`-block statements (`let`/`for`/`if`/`match`/`return`/…),
    // populated by `do_notation::register` (M3a Task 9).
    b.category("doElem");
    // `Term.structInst`'s field-decl slot recurses into its own tiny
    // category (surface table's "struct-instance-field-decl category",
    // 2 rows: `structInstFieldDef`/`structInstFieldEqns`) — registered
    // here alongside the others, populated by `term::register`.
    b.category("structInstFieldDecl");
    // `attr`/`prio` categories (surface table's own `attr` category, 12
    // rows, + the `prio` misc singleton) — M3a Task 10: declModifiers'
    // `@[attr1, attr2]` slot and the `attribute` command both recurse
    // into `attr`; `Attr.simple`/`«instance»`/`default_instance`'s own
    // optional priority argument recurses into `prio`.
    b.category("attr");
    b.category("prio");
    command::register(&mut b);
    level::register(&mut b);
    tactic::register(&mut b);
    term::register(&mut b);
    do_notation::register(&mut b);
    attr::register(&mut b);
    b.finish()
}
