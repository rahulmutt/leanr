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
//! so that "no panic" promise has one precondition — call `parse_module`
//! only on a thread with at least [`MIN_STACK_BYTES`] of stack left. The
//! main thread's 8 MiB default is below that; spawn a worker
//! (`std::thread::Builder::new().stack_size(leanr_syntax::MIN_STACK_BYTES)`),
//! exactly as Lean itself sizes its parser threads (`lean --tstack`). See
//! [`MIN_STACK_BYTES`] and [`MAX_CATEGORY_DEPTH`].
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
    parse_module, render_error, ParseError, ParseResult, MAX_CATEGORY_DEPTH, MIN_STACK_BYTES,
};
pub use tree::SyntaxTree;
