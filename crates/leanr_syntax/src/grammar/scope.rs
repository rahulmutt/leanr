//! Same-file namespace/section/open scope tracking (M3b3 Task 1).
//! Consulted by derived-kind naming (Task 2: `stxNodeKind :=
//! currNamespace ++ name`) and by scoped-entry activation (Task 4).
//! Updates are TOTAL: arbitrary stray/mismatched `end`s must never
//! panic — worst case the stack diverges from the oracle's and the
//! ratchet reports non-green trees, never a crash.

use crate::grammar::SpecScope;
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
    Section {
        name: Option<String>,
        opens_len: usize,
    },
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

    // M3b3 Task 4: wired into `scope_command_update`'s `open` arm below
    // — each opened namespace becomes a member of the active set that
    // `scoped` activation (`is_active`/`namespace_is_active`) consults.
    // Opens roll back with their enclosing scope via `opens_len` (see
    // `pop_one` + `open_namespace_rolls_back_with_its_section_scope`).
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

    /// Number of live scope entries (`namespace` components + `section`s)
    /// — `SpecScope::Local`'s activation depth (M3b3 Task 4). A `local`
    /// declared here captures this value; it stays active while at least
    /// this many entries remain (`is_active`).
    pub(crate) fn scope_len(&self) -> usize {
        self.entries.len()
    }

    /// M3b3 Task 4: is a grammar entry with activation tag `scope`
    /// currently in force? TOTAL — never panics, never allocates on the
    /// hot path (the `Scoped` arm walks the small `entries`/`opens`
    /// vectors, both bounded by same-file command nesting). Task 5
    /// reuses this verbatim for imported entries.
    pub(crate) fn is_active(&self, scope: &SpecScope) -> bool {
        match scope {
            SpecScope::Global => true,
            SpecScope::Scoped(ns) => self.namespace_is_active(ns),
            SpecScope::Local { scope_len } => self.scope_len() >= *scope_len,
        }
    }

    /// The active-namespace set for `scoped` activation (M3b3 Task 4,
    /// dump-pinned by `StxScoped.lean`): every PREFIX of the current
    /// namespace path (component-boundary aware — `Widg` is a prefix of
    /// `Widg.Inner` but not of `Widget`), plus every EXPLICIT `open`
    /// (matched exactly, not by prefix — `open Foo.Bar` activates
    /// `Foo.Bar`, not `Foo`). Empty `ns` (a degenerate `scoped` at top
    /// level, which real Lean rejects) matches nothing.
    fn namespace_is_active(&self, ns: &str) -> bool {
        if ns.is_empty() {
            return false;
        }
        // Allocation-free component-prefix test against the cached
        // dot-joined `current` (`rebuild` joins only namespace parts, so
        // this is exactly "is `ns` a prefix set member"): `ns == current`,
        // or `ns` is a leading run of components ending on a `.` boundary
        // (so `Widg` matches `Widg.Inner` but not `Widget`). Hot path —
        // `is_active` calls this per overlay candidate at every read
        // point, so it must not allocate.
        let cur = self.current.as_str();
        let prefix_match = cur == ns
            || (cur.len() > ns.len() && cur.as_bytes()[ns.len()] == b'.' && cur.starts_with(ns));
        prefix_match || self.opens.iter().any(|o| o == ns)
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
        // M3b3 Task 4: `open`'s single node child is one of the open
        // sub-forms (dump-pinned shapes, `dump_syntax` on the five
        // forms): `openSimple`/`openScoped` list one-or-more idents,
        // EACH its own dotted namespace (`open A B C` → three opens; a
        // dotted `A.B` is a single ident token); `openOnly`/`openHiding`/
        // `openRenaming` open exactly ONE namespace — their FIRST ident —
        // followed by declaration-name idents (the `(a b)`/`hiding a`/
        // `renaming a → b` lists) that are NOT namespaces and must be
        // ignored. Total on any tree: a missing sub-form (no node child)
        // or a form with no idents is a clean no-op.
        "Lean.Parser.Command.open" => {
            if let Some(decl) = root.children().next() {
                match kinds.name(decl.kind()) {
                    "Lean.Parser.Command.openSimple" | "Lean.Parser.Command.openScoped" => {
                        for el in decl.descendants_with_tokens() {
                            if let Some(t) = el.into_token() {
                                if t.kind() == KIND_IDENT {
                                    stack.open_namespace(t.text());
                                }
                            }
                        }
                    }
                    _ => {
                        if let Some(ns) = first_ident_anywhere(&decl) {
                            stack.open_namespace(&ns);
                        }
                    }
                }
            }
        }
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

    /// M3b3 Task 4: the shared activation predicate (`is_active`), across
    /// the `scoped` (namespace-prefix + explicit-open) and `local`
    /// (scope-depth) tags — the brief's own Step-1 sketch, oracle-pinned
    /// by `StxScoped.lean` for the `Scoped` arm.
    #[test]
    fn activation_predicate() {
        use crate::grammar::SpecScope;
        let mut s = ScopeStack::new();
        let sc = SpecScope::Scoped("Widg".into());
        assert!(!s.is_active(&sc));
        s.open_namespace("Widg");
        assert!(s.is_active(&sc)); // explicit open
        s.end_scope(None); // opens roll back with nothing on the stack: no-op
        assert!(s.is_active(&sc)); // top-level open persists (file scope)
        let mut s2 = ScopeStack::new();
        s2.enter_namespace("Widg.Inner");
        assert!(s2.is_active(&sc)); // namespace-prefix activation
        s2.end_scope(Some("Widg.Inner"));
        assert!(!s2.is_active(&sc));
        let mut s3 = ScopeStack::new();
        s3.enter_section(None);
        s3.open_namespace("Widg");
        assert!(s3.is_active(&sc));
        s3.end_scope(None); // section close rolls the open back
        assert!(!s3.is_active(&sc));
        // Local: active until its declaring scope pops.
        let mut s4 = ScopeStack::new();
        s4.enter_section(None);
        let loc = SpecScope::Local {
            scope_len: s4.scope_len(),
        };
        assert!(s4.is_active(&loc));
        s4.end_scope(None);
        assert!(!s4.is_active(&loc));
    }

    /// M3b3 Task 4: the `open` arm of `scope_command_update` records each
    /// opened namespace (dump-pinned open sub-form shapes) — driven
    /// through the real parser so it also pins the `open` node shape the
    /// walk depends on. `open A B` opens BOTH; `open Foo (bar)` opens
    /// only `Foo` (the parenthesized names are declarations, not
    /// namespaces).
    #[test]
    fn open_arm_records_namespaces_from_each_subform() {
        let snap = crate::builtin::snapshot();
        let src = "open A B\nopen Foo (bar)\n";
        let r = crate::parse_module(src, &snap);
        assert!(r.errors.is_empty(), "errs={:?}", r.errors);
        let mut stack = ScopeStack::new();
        for cmd in r.tree.root().children().skip(1) {
            scope_command_update(&mut stack, &cmd, &r.tree.kinds);
        }
        assert_eq!(
            stack.opens(),
            ["A".to_string(), "B".to_string(), "Foo".to_string()]
        );
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
