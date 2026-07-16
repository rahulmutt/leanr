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
//! **Stack contract**: the parser recurses natively through nested input,
//! so that "no panic" promise needs a known amount of native stack
//! ([`MIN_STACK_BYTES`], the budget [`MAX_CATEGORY_DEPTH`] is calibrated
//! against). Callers do not have to arrange it: [`parse_module`] runs the
//! parse on a worker thread it sizes itself — exactly as Lean sizes its
//! own parser threads (`lean --tstack`) — so the guarantee holds on any
//! thread, including a 2 MiB `libtest` or `tokio` one.
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

pub use parse::{
    parse_header_imports, parse_module, render_error, ParseError, ParseResult,
    MAX_CATEGORY_DEPTH, MIN_STACK_BYTES,
};
pub use tree::SyntaxTree;
