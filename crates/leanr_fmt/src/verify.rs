//! Self-consistency checks (spec §Acceptance harness). Shared by the
//! hermetic fixture tests and the Mathlib corpus sweep.

use leanr_syntax::grammar::GrammarSnapshot;
use leanr_syntax::kind::{KIND_BLOCK_COMMENT, KIND_LINE_COMMENT};
use leanr_syntax::tree::NodeOrToken;
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

/// Semantics oracle for invariant 3: `leanr_syntax::canon`'s canonical
/// form, despanned and with import commands order-normalized.
///
///  1. **Spans omitted** — formatting legitimately moves token positions
///     (spacing collapse, trailing-ws strip), so those offsets are layout,
///     not semantics. The token KIND + TEXT are the semantic content and
///     are kept.
///  2. **Import commands order-normalized** — so the formatter's
///     alphabetical import sort is invisible here.
///
/// This still catches a dropped/renamed/restructured token, a corrupted
/// import name, or a changed command body. It tolerates exactly what the
/// formatter is allowed to change: layout and import order. Sharing
/// `canon`'s renderer (rather than mirroring it) removes the drift risk —
/// a divergence in a private copy could only ever false-negative.
pub fn canon_semantic(tree: &SyntaxTree) -> String {
    leanr_syntax::canon::canon_to_string(
        tree,
        leanr_syntax::canon::CanonOpts {
            spans: false,
            sort_kind: Some(IMPORT_KIND),
        },
    )
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
