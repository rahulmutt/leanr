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

/// How to render the canonical form.
///
/// - `spans: true` emits `"s":[start,stop]` on every atom/ident — the
///   oracle-comparison form. `false` omits them: formatting legitimately
///   moves token positions, so offsets are layout, not semantics.
/// - `sort_kind: Some(k)` renders the sibling nodes of kind `k` in sorted
///   order of their own rendering, making a reordering of those siblings
///   invisible. Used for import commands, whose order is semantics-neutral
///   in Lean.
#[derive(Clone, Copy)]
pub struct CanonOpts<'a> {
    pub spans: bool,
    pub sort_kind: Option<&'a str>,
}

/// One JSON line per immediate child of the root (header node, then each
/// command) — the exact line structure the oracle dump emits.
pub fn canon_jsonl(tree: &SyntaxTree) -> String {
    canon_to_string(
        tree,
        CanonOpts {
            spans: true,
            sort_kind: None,
        },
    )
}

/// The canonical form under `opts`. `canon_jsonl` is the
/// `spans: true, sort_kind: None` configuration and MUST stay
/// byte-identical to it — it is what the oracle fixtures compare.
pub fn canon_to_string(tree: &SyntaxTree, opts: CanonOpts) -> String {
    let mut out = String::new();
    for child in tree.root().children() {
        node_json_opts(&child, &tree.kinds, opts, &mut out);
        out.push('\n');
    }
    out
}

pub fn node_json(node: &SyntaxNode, kinds: &KindInterner, out: &mut String) {
    node_json_opts(
        node,
        kinds,
        CanonOpts {
            spans: true,
            sort_kind: None,
        },
        out,
    );
}

/// Render one node. Children are rendered into their own strings first so
/// that `opts.sort_kind` can reorder a subset of them in place without
/// disturbing any other child's position.
fn node_json_opts(node: &SyntaxNode, kinds: &KindInterner, opts: CanonOpts, out: &mut String) {
    let mut parts: Vec<String> = Vec::new();
    let mut sort_slots: Vec<usize> = Vec::new();
    for el in node.children_with_tokens() {
        match el {
            rowan::NodeOrToken::Node(n) => {
                if let Some(k) = opts.sort_kind {
                    if kinds.name(n.kind()) == k {
                        sort_slots.push(parts.len());
                    }
                }
                let mut s = String::new();
                node_json_opts(&n, kinds, opts, &mut s);
                parts.push(s);
            }
            rowan::NodeOrToken::Token(t) => {
                let k = t.kind();
                if is_trivia(k) {
                    continue;
                }
                let mut s = String::new();
                if k == KIND_MISSING {
                    s.push_str("{\"k\":\"<missing>\"}");
                } else {
                    if k == KIND_IDENT {
                        s.push_str("{\"i\":");
                    } else {
                        // KIND_ATOM and (never oracle-compared) KIND_ERROR_TOKEN.
                        debug_assert!(k == KIND_ATOM || k == KIND_ERROR_TOKEN);
                        s.push_str("{\"a\":");
                    }
                    json_str(t.text(), &mut s);
                    if opts.spans {
                        let range = t.text_range();
                        push_span(u32::from(range.start()), u32::from(range.end()), &mut s);
                    } else {
                        s.push('}');
                    }
                }
                parts.push(s);
            }
        }
    }
    if sort_slots.len() > 1 {
        let mut rendered: Vec<String> = sort_slots.iter().map(|&i| parts[i].clone()).collect();
        rendered.sort();
        for (slot, &i) in sort_slots.iter().enumerate() {
            parts[i] = rendered[slot].clone();
        }
    }
    out.push_str("{\"c\":[");
    out.push_str(&parts.join(","));
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

/// JSON string escaping matching Lean's `Json.compress` (escapeAux).
/// Only short forms for `"`, `\`, `\n`, `\r`; all other control chars < 0x20
/// rendered as `\uXXXX`. Reference: Lean stdlib Lean/Data/Json/Printer.lean
/// lines 36–62 (escapeAux).
fn json_str(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
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
    fn canon_to_string_despans_and_sorts_named_kind() {
        use crate::{builtin, parse_module};
        let snap = builtin::snapshot();
        let despanned = CanonOpts {
            spans: false,
            sort_kind: Some("Lean.Parser.Module.import"),
        };
        let a = parse_module("import Foo.B\nimport Foo.A\n", &snap).tree;
        let b = parse_module("import Foo.A\nimport Foo.B\n", &snap).tree;
        // Despanned + import-order-normalized: reordering is invisible.
        assert_eq!(
            canon_to_string(&a, despanned),
            canon_to_string(&b, despanned)
        );
        // No span keys survive when spans: false.
        assert!(
            !canon_to_string(&a, despanned).contains("\"s\":"),
            "despanned form must not emit span keys"
        );
        // A corrupted import name is still caught.
        let c = parse_module("import Foo.C\n", &snap).tree;
        let d = parse_module("import Foo.D\n", &snap).tree;
        assert_ne!(
            canon_to_string(&c, despanned),
            canon_to_string(&d, despanned)
        );
    }

    #[test]
    fn canon_jsonl_equals_spanned_unsorted_canon_to_string() {
        use crate::{builtin, parse_module};
        let snap = builtin::snapshot();
        let tree = parse_module("import Foo.B\nimport Foo.A\ndef x := 1\n", &snap).tree;
        assert_eq!(
            canon_jsonl(&tree),
            canon_to_string(
                &tree,
                CanonOpts {
                    spans: true,
                    sort_kind: None
                }
            ),
            "canon_jsonl must be exactly the spanned, unsorted configuration"
        );
    }

    #[test]
    fn json_escaping_covers_controls_and_quotes() {
        let mut out = String::new();
        json_str("a\"b\\c\nd\u{1}", &mut out);
        assert_eq!(out, "\"a\\\"b\\\\c\\nd\\u0001\"");
    }

    #[test]
    fn json_escaping_matches_lean_printer_control_chars() {
        // Verify parity with Lean's escapeAux: only ", \, \n, \r get short forms;
        // tab (0x09), backspace (0x08), form-feed (0x0c), and other < 0x20
        // all use \uXXXX format (matching Lean/Data/Json/Printer.lean lines 36–62).
        let mut out = String::new();
        // String with: tab, backspace, form-feed, newline, carriage-return,
        // quote, backslash, and control byte 0x01.
        json_str("a\tb\u{8}c\u{c}d\ne\rf\"g\\h\u{1}i", &mut out);
        // Expected: tab→	, backspace→, form-feed→,
        // newline→\n, carriage-return→\r, quote→\", backslash→\\, 0x01→
        assert_eq!(
            out,
            "\"a\\u0009b\\u0008c\\u000cd\\ne\\rf\\\"g\\\\h\\u0001i\""
        );
    }
}
