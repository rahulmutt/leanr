//! The builtin grammar snapshot (spec §Architecture / builtin) —
//! Rust ports of the pinned toolchain's compiled `@[builtin_*_parser]`
//! set, per docs/superpowers/specs/2026-07-13-m3a-builtin-surface.md.
//! Kind names MUST match Lean's byte-for-byte (oracle equality).

pub mod command;
// Tasks 8–10 add: pub mod level; pub mod term; pub mod do_notation;
// pub mod tactic;

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
    command::register(&mut b);
    // Tasks 8–10: level::register(&mut b); term::register(&mut b); …
    b.finish()
}
