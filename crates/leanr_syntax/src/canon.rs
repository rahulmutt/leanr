//! Oracle-canonical form (spec §Oracle harness): serialize the red tree
//! as JSON lines matching `tests/fixtures/syntax/dump_syntax.lean`.
//! Locked schema (Global Constraints): keys ALPHABETICAL (Lean
//! `Json.compress` prints RBMap-sorted objects):
//!   node    {"c":[…],"k":"<kind name>"}
//!   atom    {"a":"<text>","s":[start,stop]}
//!   ident   {"i":"<raw text>","s":[start,stop]}
//!   missing {"k":"<missing>"}
//! Spans are byte offsets of the token text (trivia excluded). Trivia
//! tokens are skipped entirely — the byte round-trip gate owns trivia.

use crate::kind::{is_trivia, KindInterner, KIND_ATOM, KIND_ERROR_TOKEN, KIND_IDENT, KIND_MISSING};
use crate::tree::{SyntaxNode, SyntaxTree};

/// One JSON line per immediate child of the root (header node, then each
/// command) — the exact line structure the oracle dump emits.
pub fn canon_jsonl(tree: &SyntaxTree) -> String {
    let mut out = String::new();
    for child in tree.root().children() {
        node_json(&child, &tree.kinds, &mut out);
        out.push('\n');
    }
    out
}

pub fn node_json(node: &SyntaxNode, kinds: &KindInterner, out: &mut String) {
    out.push_str("{\"c\":[");
    let mut first = true;
    for el in node.children_with_tokens() {
        match el {
            rowan::NodeOrToken::Node(n) => {
                if !first {
                    out.push(',');
                }
                first = false;
                node_json(&n, kinds, out);
            }
            rowan::NodeOrToken::Token(t) => {
                let k = t.kind();
                if is_trivia(k) {
                    continue;
                }
                if !first {
                    out.push(',');
                }
                first = false;
                let range = t.text_range();
                let (s, e) = (u32::from(range.start()), u32::from(range.end()));
                if k == KIND_MISSING {
                    out.push_str("{\"k\":\"<missing>\"}");
                } else if k == KIND_IDENT {
                    out.push_str("{\"i\":");
                    json_str(t.text(), out);
                    push_span(s, e, out);
                } else {
                    // KIND_ATOM and (never oracle-compared) KIND_ERROR_TOKEN.
                    debug_assert!(k == KIND_ATOM || k == KIND_ERROR_TOKEN);
                    out.push_str("{\"a\":");
                    json_str(t.text(), out);
                    push_span(s, e, out);
                }
            }
        }
    }
    out.push_str("],\"k\":");
    json_str(kinds.name(node.kind()), out);
    out.push('}');
}

fn push_span(s: u32, e: u32, out: &mut String) {
    out.push_str(",\"s\":[");
    out.push_str(&s.to_string());
    out.push(',');
    out.push_str(&e.to_string());
    out.push_str("]}");
}

/// JSON string escaping per RFC 8259 minimal form: `"` `\` escaped,
/// control chars as \b \f \n \r \t or \u00XX. ORACLE-PORT: must match
/// Lean's `Json.compress` escaping — verified by the first golden
/// fixture diff in Task 7 (any mismatch shows up as a whole-line diff).
fn json_str(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\u{8}' => out.push_str("\\b"),
            '\u{c}' => out.push_str("\\f"),
            c if (c as u32) < 0x20 => {
                out.push_str(&format!("\\u{:04x}", c as u32));
            }
            c => out.push(c),
        }
    }
    out.push('"');
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kind::{KindInterner, KIND_ATOM, KIND_IDENT, KIND_WHITESPACE};
    use crate::tree::{build_tree, Event};
    use std::sync::Arc;

    #[test]
    fn canon_skips_trivia_and_orders_keys_alphabetically() {
        let src = "def x";
        let mut it = KindInterner::new();
        let root = it.intern("module");
        let decl = it.intern("Lean.Parser.Command.declaration");
        let events = vec![
            Event::Start(root),
            Event::Start(decl),
            Event::Token {
                kind: KIND_ATOM,
                offset: 0,
                len: 3,
            },
            Event::Token {
                kind: KIND_WHITESPACE,
                offset: 3,
                len: 1,
            },
            Event::Token {
                kind: KIND_IDENT,
                offset: 4,
                len: 1,
            },
            Event::Finish,
            Event::Finish,
        ];
        let tree = build_tree(src, &events, Arc::new(it));
        assert_eq!(
            canon_jsonl(&tree),
            "{\"c\":[{\"a\":\"def\",\"s\":[0,3]},{\"i\":\"x\",\"s\":[4,5]}],\"k\":\"Lean.Parser.Command.declaration\"}\n"
        );
    }

    #[test]
    fn json_escaping_covers_controls_and_quotes() {
        let mut out = String::new();
        json_str("a\"b\\c\nd\u{1}", &mut out);
        assert_eq!(out, "\"a\\\"b\\\\c\\nd\\u0001\"");
    }
}
