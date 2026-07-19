//! The `leanr fmt` engine (M3c): a preserve-fallback source formatter
//! over `leanr_syntax` lossless trees. Consumes trees only; never
//! re-lexes source. See docs/superpowers/specs/2026-07-19-m3c-fmt-thin-slice-design.md.

pub mod doc;
pub mod render;
pub mod trivia;

use leanr_syntax::grammar::GrammarSnapshot;
use leanr_syntax::{parse_module, SyntaxTree};

pub const WIDTH: usize = 100;

#[derive(Debug)]
pub enum FormatError {
    /// The input did not parse clean; fmt never formats a broken tree.
    Unparseable(Vec<String>),
}

/// Format a parsed tree. Total: never panics, never bails.
pub fn format_tree(tree: &SyntaxTree) -> String {
    let doc = render::render_verbatim(tree);
    let laid_out = doc::layout(&doc, WIDTH);
    trivia::normalize(&laid_out)
}

/// Parse then format. Enforces the "parseable input" precondition.
pub fn format_src(src: &str, snap: &GrammarSnapshot) -> Result<String, FormatError> {
    let result = parse_module(src, snap);
    if !result.errors.is_empty() {
        let msgs = result
            .errors
            .iter()
            .map(|e| leanr_syntax::parse::render_error(src, e))
            .collect();
        return Err(FormatError::Unparseable(msgs));
    }
    Ok(format_tree(&result.tree))
}
