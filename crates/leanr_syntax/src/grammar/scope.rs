//! Same-file namespace/section/open scope tracking (M3b3 Task 1).
//! Consulted by derived-kind naming (Task 2: `stxNodeKind :=
//! currNamespace ++ name`) and by scoped-entry activation (Task 4).
//! Updates are TOTAL: arbitrary stray/mismatched `end`s must never
//! panic — worst case the stack diverges from the oracle's and the
//! ratchet reports non-green trees, never a crash.

use crate::kind::{KindInterner, KIND_IDENT};
use crate::tree::SyntaxNode;

#[derive(Debug, Default)]
pub(crate) struct ScopeStack {
    entries: Vec<ScopeEntry>,
    /// Cached dot-joined namespace components; rebuilt on change —
    /// scope events are per-command, never per-token.
    current: String,
    /// Explicitly opened namespaces (Task 4 activation; `open Foo` and
    /// `open Foo in`-less forms). Snapshot length is recorded by
    /// sections so `end` rolls opens back with their scope.
    opens: Vec<String>,
}

#[derive(Debug)]
enum ScopeEntry {
    /// One dotted component of a `namespace` command; `namespace A.B`
    /// pushes two. Carries the `opens` length at entry for rollback.
    Namespace { part: String, opens_len: usize },
    /// `section` (anonymous or named). Contributes nothing to the
    /// current namespace. Carries the `opens` length at entry.
    Section { name: Option<String>, opens_len: usize },
}

impl ScopeStack {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    // M3b3 Task 2: `parse.rs`'s command loop passes this into
    // `derive_delta`'s new `current_ns` param at the grammar-growing
    // arm — no longer dead code outside `#[cfg(test)]`.
    pub(crate) fn current_namespace(&self) -> &str {
        &self.current
    }

    pub(crate) fn enter_namespace(&mut self, dotted: &str) {
        for part in dotted.split('.').filter(|p| !p.is_empty()) {
            self.entries.push(ScopeEntry::Namespace {
                part: part.to_string(),
                opens_len: self.opens.len(),
            });
        }
        self.rebuild();
    }

    pub(crate) fn enter_section(&mut self, name: Option<&str>) {
        self.entries.push(ScopeEntry::Section {
            name: name.map(str::to_string),
            opens_len: self.opens.len(),
        });
    }

    // Task 4 wires this into the `open` command arm below
    // (`scope_command_update`'s `Lean.Parser.Command.open` case is still
    // a deliberate no-op); nothing outside `#[cfg(test)]` calls it yet,
    // so the plain (non-test) lib target sees it as dead code even
    // though it's fully implemented and exercised by
    // `open_namespace_rolls_back_with_its_section_scope` below. Same
    // established idiom as the `Ps` impl blocks in parse.rs
    // (`#[cfg_attr(not(test), allow(dead_code))]`) rather than deleting
    // or stubbing out real, already-tested behavior.
    // consumed by Task 4
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn open_namespace(&mut self, dotted: &str) {
        self.opens.push(dotted.to_string());
    }

    /// Test-only view of the explicitly opened namespaces, in the order
    /// `open_namespace` recorded them — lets unit tests assert on
    /// `opens` rollback semantics without exposing the field itself.
    #[cfg(test)]
    fn opens(&self) -> &[String] {
        &self.opens
    }

    /// `end` (bare or with a dotted name). Rules, all total:
    /// - bare `end`: pops the innermost entry iff it is an anonymous
    ///   section; otherwise no-op.
    /// - `end X` / `end X.Y`: if the innermost entry is a section named
    ///   exactly the (single-component) name, pop it. Else if the top k
    ///   entries are namespace components spelling the dotted name in
    ///   order, pop those k. Else if the top entries suffix-match a
    ///   trailing subset of the dotted components, pop the matching
    ///   suffix. Otherwise no-op.
    pub(crate) fn end_scope(&mut self, dotted: Option<&str>) {
        match dotted {
            None => {
                if matches!(
                    self.entries.last(),
                    Some(ScopeEntry::Section { name: None, .. })
                ) {
                    self.pop_one();
                }
            }
            Some(d) => {
                let parts: Vec<&str> = d.split('.').filter(|p| !p.is_empty()).collect();
                if parts.len() == 1 {
                    if let Some(ScopeEntry::Section { name: Some(n), .. }) = self.entries.last() {
                        if n == parts[0] {
                            self.pop_one();
                            return;
                        }
                    }
                }
                // Longest suffix of `parts` matching the top namespace
                // components, matched innermost-outward.
                let mut k = 0;
                for (i, part) in parts.iter().rev().enumerate() {
                    match self.entries.iter().rev().nth(i) {
                        Some(ScopeEntry::Namespace { part: p, .. }) if p == part => k += 1,
                        _ => break,
                    }
                }
                for _ in 0..k {
                    self.pop_one();
                }
            }
        }
        self.rebuild();
    }

    fn pop_one(&mut self) {
        if let Some(e) = self.entries.pop() {
            let opens_len = match e {
                ScopeEntry::Namespace { opens_len, .. } => opens_len,
                ScopeEntry::Section { opens_len, .. } => opens_len,
            };
            self.opens.truncate(opens_len);
        }
    }

    fn rebuild(&mut self) {
        let mut s = String::new();
        for e in &self.entries {
            if let ScopeEntry::Namespace { part, .. } = e {
                if !s.is_empty() {
                    s.push('.');
                }
                s.push_str(part);
            }
        }
        self.current = s;
    }
}

/// First `KIND_IDENT` token anywhere under `node` — ANY depth, not just
/// direct children, unlike `notation::first_ident_token_text`. Needed
/// here because `namespace`/`section`/`end`'s name ident sits behind an
/// `opt(..)` in every one of their productions (`command_open.rs`), and
/// `Prim::Optional`'s `run` arm (`parse.rs`) always opens a `KIND_NULL`
/// wrapper node around its body regardless of whether it matched — so a
/// present name is a GRANDCHILD of the command node, never a direct
/// child (confirmed against a real `end Foo.Bar` parse: the ident sits
/// one `null` node deep). `namespace`'s own ident is a direct child
/// (`Prim::Ident` with no `opt` wrap), so this still finds it — a
/// descendant search is a strict superset of a direct-children one.
fn first_ident_anywhere(node: &SyntaxNode) -> Option<String> {
    node.descendants_with_tokens().find_map(|el| {
        let t = el.into_token()?;
        (t.kind() == KIND_IDENT).then(|| t.text().to_string())
    })
}

/// ALL `KIND_IDENT` descendant tokens under `node`, joined with `.` in
/// source order. Mirrors `parse_header_imports`' own import-name walk
/// (`parse.rs:307-314`, joining every `KIND_IDENT` child found under a
/// `Lean.Parser.Module.import` node) rather than `first_ident_anywhere`
/// above: `end`'s name goes through `ident_with_partial_trailing_dot()`
/// (`command_open.rs`) — `seq([Ident, opt(seq([CheckNoWsBefore, ".",
/// CheckNoWsBefore, Ident]))])` — which the oracle can split into TWO
/// `Ident` tokens around a `.` atom on some trailing-dot edge case;
/// taking only the first `Ident` (as `first_ident_anywhere` does) would
/// silently drop the second component whenever that split fires.
///
/// In THIS port that split is believed unreachable: `ident_len`
/// (`lex.rs`) greedily continues a dotted ident through `.` whenever the
/// following character `is_id_first` (or `«`), with no reserved-word or
/// token-table carve-out for the continuation segment — so any text
/// that could lex as a second `Ident` after the dot is, by that same
/// rule, already swallowed into the FIRST `Ident` token, never left for
/// a separate one. No fixture or hand-built input has been found that
/// splits it. Joining every `KIND_IDENT` descendant is still adopted
/// here, for parity with `parse_header_imports`' precedent and because
/// it is a strict superset of the first-token read (correct whether or
/// not this port's greedy-lexer assumption above ever turns out wrong).
fn dotted_ident_anywhere(node: &SyntaxNode) -> Option<String> {
    let mut parts = Vec::new();
    for el in node.descendants_with_tokens() {
        if let Some(t) = el.into_token() {
            if t.kind() == KIND_IDENT {
                parts.push(t.text().to_string());
            }
        }
    }
    (!parts.is_empty()).then(|| parts.join("."))
}

/// Applies one top-level command's scope effect, if any. Total on
/// arbitrary trees (missing idents → no-op).
pub(crate) fn scope_command_update(
    stack: &mut ScopeStack,
    root: &SyntaxNode,
    kinds: &KindInterner,
) {
    match kinds.name(root.kind()) {
        "Lean.Parser.Command.namespace" => {
            if let Some(name) = first_ident_anywhere(root) {
                stack.enter_namespace(&name);
            }
        }
        "Lean.Parser.Command.section" => {
            let name = first_ident_anywhere(root);
            stack.enter_section(name.as_deref());
        }
        "Lean.Parser.Command.end" => {
            // `end`'s name uses `ident_with_partial_trailing_dot()`
            // (`command_open.rs`): join every `KIND_IDENT` descendant,
            // not just the first (`dotted_ident_anywhere`'s doc comment)
            // — mirrors `parse_header_imports`' own join-all walk for
            // the same combinator. Trim a defensively-possible dangling
            // trailing `.` (never observed on this crate's fixtures, but
            // cheap to guard).
            let name = dotted_ident_anywhere(root).map(|n| n.trim_end_matches('.').to_string());
            stack.end_scope(name.as_deref());
        }
        // M3b3 Task 4: `open Foo` walk (all 5 sub-forms) fills this in —
        // scoped activation isn't wired yet, so recording nothing here
        // is a no-op, not a gap.
        "Lean.Parser.Command.open" => {}
        _ => {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn namespace_pushes_components_end_pops_them() {
        let mut s = ScopeStack::new();
        assert_eq!(s.current_namespace(), "");
        s.enter_namespace("A.B");
        assert_eq!(s.current_namespace(), "A.B");
        s.enter_namespace("C");
        assert_eq!(s.current_namespace(), "A.B.C");
        s.end_scope(Some("C"));
        assert_eq!(s.current_namespace(), "A.B");
        s.end_scope(Some("A.B"));
        assert_eq!(s.current_namespace(), "");
    }

    #[test]
    fn sections_do_not_contribute_to_namespace() {
        let mut s = ScopeStack::new();
        s.enter_namespace("N");
        s.enter_section(None);
        assert_eq!(s.current_namespace(), "N");
        s.end_scope(None); // bare `end` closes the anonymous section
        s.enter_section(Some("part"));
        s.end_scope(Some("part"));
        assert_eq!(s.current_namespace(), "N");
    }

    #[test]
    fn mismatched_end_is_total_and_best_effort() {
        let mut s = ScopeStack::new();
        s.end_scope(None); // stray bare end on empty stack: no-op, no panic
        s.end_scope(Some("Ghost")); // stray named end: no-op, no panic
        s.enter_namespace("A.B");
        s.end_scope(Some("Wrong")); // name mismatch: no-op (ratchet will
                                    // catch semantic divergence; never panic)
        assert_eq!(s.current_namespace(), "A.B");
        s.end_scope(Some("B")); // suffix match pops one component
        assert_eq!(s.current_namespace(), "A");
    }

    #[test]
    fn open_namespace_rolls_back_with_its_section_scope() {
        let mut s = ScopeStack::new();
        s.open_namespace("Top"); // top-level open: no enclosing scope to roll back with
        assert_eq!(s.opens(), ["Top".to_string()]);
        s.enter_section(Some("Sec"));
        s.open_namespace("Inner");
        assert_eq!(s.opens(), ["Top".to_string(), "Inner".to_string()]);
        s.end_scope(Some("Sec")); // truncates opens back to the section's opens_len
        assert_eq!(s.opens(), ["Top".to_string()]);
        s.end_scope(None); // stray bare end on the now-empty stack: no-op
        assert_eq!(s.opens(), ["Top".to_string()]); // top-level open persists
    }

    /// `end`'s name extraction must join EVERY `KIND_IDENT` descendant,
    /// not just the first (`dotted_ident_anywhere`'s doc comment) — a
    /// regression test for the bug where a genuine
    /// `ident_with_partial_trailing_dot()` split would silently drop
    /// the tail component. No input has been found that actually
    /// splits the combinator in this port (see that doc comment for
    /// why it's believed unreachable), so this exercises the join-all
    /// path against an ordinary multi-component dotted name instead,
    /// through the real parser + `scope_command_update` (not just
    /// `ScopeStack` directly) so it also pins the `end`-node shape the
    /// walk depends on.
    #[test]
    fn end_name_extraction_joins_every_ident_descendant() {
        let snap = crate::builtin::snapshot();
        let mut stack = ScopeStack::new();
        let src = "namespace A.B.C\nend A.B.C\n";
        let r = crate::parse_module(src, &snap);
        assert!(r.errors.is_empty(), "errs={:?}", r.errors);
        // Skip the module's own leading `Lean.Parser.Module.header` node
        // (`run_module` always emits exactly one, even header-less, per
        // `scope_updates_follow_parsed_commands`'s own comment above).
        let mut cmds = r.tree.root().children().skip(1);
        let ns_cmd = cmds.next().expect("namespace command");
        scope_command_update(&mut stack, &ns_cmd, &r.tree.kinds);
        assert_eq!(stack.current_namespace(), "A.B.C");
        let end_cmd = cmds.next().expect("end command");
        scope_command_update(&mut stack, &end_cmd, &r.tree.kinds);
        assert_eq!(
            stack.current_namespace(),
            "",
            "end A.B.C must pop all three namespace components, not just the \
             first ident token's worth"
        );
    }
}
