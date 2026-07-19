//! Self-consistency checks (spec §Acceptance harness). Shared by the
//! hermetic fixture tests and the Mathlib corpus sweep.

use leanr_syntax::grammar::GrammarSnapshot;
use leanr_syntax::kind::{
    is_trivia, KIND_BLOCK_COMMENT, KIND_IDENT, KIND_LINE_COMMENT, KIND_MISSING,
};
use leanr_syntax::tree::{NodeOrToken, SyntaxNode};
use leanr_syntax::{parse_module, SyntaxTree};

use crate::{format_src, format_tree};

/// The interned kind name of Lean's module-import command node. Import
/// commands are order-normalized (sorted) in the semantic canonical form
/// because import reordering is semantics-neutral for Lean.
const IMPORT_KIND: &str = "Lean.Parser.Module.import";

/// Every comment token, in source order, right-trimmed. The comment
/// invariant compares this sequence modulo trailing whitespace.
pub fn comment_seq(tree: &SyntaxTree) -> Vec<String> {
    let mut out = Vec::new();
    for el in tree.root().descendants_with_tokens() {
        if let NodeOrToken::Token(t) = el {
            if t.kind() == KIND_LINE_COMMENT || t.kind() == KIND_BLOCK_COMMENT {
                out.push(t.text().trim_end().to_string());
            }
        }
    }
    out
}

/// Semantics oracle for invariant 3. Mirrors `leanr_syntax::canon::canon_jsonl`
/// (node `{"c":[..],"k":".."}`, atom `{"a":".."}`, ident `{"i":".."}`,
/// missing `{"k":"<missing>"}`, keys alphabetical, trivia skipped) with the
/// two changes that make it robust to *layout* while still catching genuine
/// corruption:
///
///  1. **Spans omitted** — raw `canon_jsonl` embeds absolute byte spans
///     (`"s":[start,stop]`) on every atom/ident. Formatting legitimately
///     moves token positions (spacing collapse, trailing-ws strip), so those
///     offsets are layout, not semantics. The token KIND + TEXT are the
///     semantic content and are kept.
///  2. **Import commands order-normalized** — the `import` command sibling
///     nodes are emitted in SORTED order (by their rendered sub-string), so
///     the formatter's alphabetical import sort is invisible here.
///
/// This still catches a dropped/renamed/restructured token, a corrupted
/// import name, or a changed command body — any of those alter the
/// despanned / import-sorted rendering. It tolerates exactly what the
/// formatter is allowed to change: layout and import order.
pub fn canon_semantic(tree: &SyntaxTree) -> String {
    let mut out = String::new();
    for child in tree.root().children() {
        node_semantic(&child, tree, &mut out);
        out.push('\n');
    }
    out
}

fn node_semantic(node: &SyntaxNode, tree: &SyntaxTree, out: &mut String) {
    // Render each child (node, or non-trivia token) to its own string, then
    // reassemble. Rendering children independently lets us sort the
    // import-command siblings without disturbing any other child's position.
    let mut parts: Vec<String> = Vec::new();
    let mut import_slots: Vec<usize> = Vec::new();
    for el in node.children_with_tokens() {
        match el {
            NodeOrToken::Node(n) => {
                if tree.kinds.name(n.kind()) == IMPORT_KIND {
                    import_slots.push(parts.len());
                }
                let mut s = String::new();
                node_semantic(&n, tree, &mut s);
                parts.push(s);
            }
            NodeOrToken::Token(t) => {
                let k = t.kind();
                if is_trivia(k) {
                    continue;
                }
                let mut s = String::new();
                if k == KIND_MISSING {
                    s.push_str("{\"k\":\"<missing>\"}");
                } else if k == KIND_IDENT {
                    s.push_str("{\"i\":");
                    json_str(t.text(), &mut s);
                    s.push('}');
                } else {
                    // KIND_ATOM (and never-oracle-compared KIND_ERROR_TOKEN).
                    s.push_str("{\"a\":");
                    json_str(t.text(), &mut s);
                    s.push('}');
                }
                parts.push(s);
            }
        }
    }
    // Order-normalize the import-command siblings: sort their rendered
    // strings among their own positions (contiguous in practice, but this
    // is correct regardless of contiguity).
    if import_slots.len() > 1 {
        let mut rendered: Vec<String> = import_slots.iter().map(|&i| parts[i].clone()).collect();
        rendered.sort();
        for (slot, &i) in import_slots.iter().enumerate() {
            parts[i] = rendered[slot].clone();
        }
    }
    out.push_str("{\"c\":[");
    out.push_str(&parts.join(","));
    out.push_str("],\"k\":");
    json_str(tree.kinds.name(node.kind()), out);
    out.push('}');
}

/// JSON string escaping identical to `leanr_syntax::canon`'s private
/// `json_str` (which mirrors Lean's `Json.compress` escapeAux): short forms
/// only for `"`, `\`, `\n`, `\r`; every other control char < 0x20 as
/// `\uXXXX`. Duplicated here (a handful of lines) rather than exported from
/// `leanr_syntax`, to keep the oracle self-contained in `leanr_fmt`.
fn json_str(s: &str, out: &mut String) {
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
}

/// Run all four self-consistency invariants over `src`, returning
/// `Err(description)` on the first failure. Re-parses `fmt(x)` once and
/// reuses that tree for invariants 2–4.
pub fn check_invariants(src: &str, snap: &GrammarSnapshot) -> Result<(), String> {
    // 1. Total — `format_src` returns Ok (parseable input formats cleanly).
    let once = format_src(src, snap).map_err(|e| format!("not total: {e:?}"))?;

    // Re-parse the formatted output once; reused by invariants 2–4.
    let after = parse_module(&once, snap);
    if !after.errors.is_empty() {
        return Err("formatted output does not re-parse clean".to_string());
    }

    // 2. Idempotent — fmt(fmt(x)) == fmt(x), byte-exact.
    let twice = format_tree(&after.tree);
    if twice != once {
        return Err("not idempotent: fmt(fmt(x)) != fmt(x)".to_string());
    }

    let before = parse_module(src, snap);

    // 3. Semantics-preserving — canonical tree equal modulo layout + import
    //    order (see `canon_semantic`).
    if canon_semantic(&after.tree) != canon_semantic(&before.tree) {
        return Err(
            "semantics changed: canonical tree differs (modulo layout + import order)".to_string(),
        );
    }

    // 4. Comment invariant — ordered comment sequence equal (modulo trailing
    //    whitespace).
    if comment_seq(&after.tree) != comment_seq(&before.tree) {
        return Err("comment invariant violated".to_string());
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use leanr_syntax::{builtin, parse_module};

    #[test]
    fn comment_seq_is_ordered_and_right_trimmed() {
        let snap = builtin::snapshot();
        let src = "-- a   \ndef x := 1 /- b -/\n";
        let tree = parse_module(src, &snap).tree;
        assert_eq!(super::comment_seq(&tree), vec!["-- a", "/- b -/"]);
    }

    fn canon_semantic(src: &str) -> String {
        let snap = builtin::snapshot();
        let tree = parse_module(src, &snap).tree;
        super::canon_semantic(&tree)
    }

    /// The semantics oracle proof (task-7-supplement §Validation): it must
    /// tolerate exactly layout + import order, and catch genuine corruption.
    #[test]
    fn canon_semantic_tolerates_layout_and_import_order_catches_corruption() {
        // Import reorder is invisible.
        assert_eq!(
            canon_semantic("import Foo.B\nimport Foo.A\n"),
            canon_semantic("import Foo.A\nimport Foo.B\n"),
            "import reorder must be invisible to canon_semantic"
        );
        // Spacing is invisible.
        assert_eq!(
            canon_semantic("def x :=   1\n"),
            canon_semantic("def x := 1\n"),
            "spacing must be invisible to canon_semantic"
        );
        // A corrupted literal MUST be caught.
        assert_ne!(
            canon_semantic("def x := 1\n"),
            canon_semantic("def x := 2\n"),
            "a corrupted literal must be caught"
        );
        // A corrupted import name MUST be caught.
        assert_ne!(
            canon_semantic("import Foo.A\n"),
            canon_semantic("import Foo.B\n"),
            "a corrupted import name must be caught"
        );
    }

    #[test]
    fn check_invariants_holds_for_reordering_and_spacing() {
        let snap = builtin::snapshot();
        super::check_invariants("import Foo.B\nimport Foo.A\n\ndef x := 1\n", &snap).unwrap();
        super::check_invariants("def a :=   1\ndef b := 2\n", &snap).unwrap();
    }
}
