//! Lossless Lean 4 syntax trees + the extensible parser (M3a: foundations).
//! Spec: docs/superpowers/specs/2026-07-13-m3a-parser-foundations-design.md
//!
//! The parser interprets a combinator data structure (`grammar::Prim`) —
//! deliberately ParserDescr-shaped so M3b can feed `.olean`-decoded
//! grammar into the same machinery. All parser state is one explicit
//! `GrammarSnapshot` value (the query-ready firewall seam); nothing is
//! global. Source text is untrusted input: no panic, no non-termination,
//! on any byte sequence (docs/THREAT_MODEL.md).
//!
//! Task 1 (this commit) lands the crate scaffold: syntax kinds, rowan
//! trees, event-based tree building, and canonical JSON output. `lex`,
//! `grammar`, `parse`, and `builtin` are stub modules until later M3a
//! tasks fill them in; re-exports below cover only what exists so far.

pub mod builtin;
pub mod canon;
pub mod grammar;
pub mod kind;
pub mod lex;
pub mod parse;
pub mod tree;

pub use parse::{parse_module, render_error, ParseError, ParseResult};
pub use tree::SyntaxTree;
