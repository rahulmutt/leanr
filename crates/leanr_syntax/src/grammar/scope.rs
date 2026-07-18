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

    pub(crate) fn open_namespace(&mut self, dotted: &str) {
        self.opens.push(dotted.to_string());
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
            // (`command_open.rs`): ordinarily the whole dotted name
            // lexes as ONE ident token, but its rare "partial trailing
            // dot" split can leave a dangling `.` on the first token —
            // trim it defensively (never observed on this crate's
            // fixtures, but cheap to guard).
            let name = first_ident_anywhere(root).map(|n| n.trim_end_matches('.').to_string());
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
}
