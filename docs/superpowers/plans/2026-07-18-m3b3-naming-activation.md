# M3b3 — Naming and Activation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Namespace-qualified derived kind names, `local`/`scoped` naming + activation (same-file and imported), and the remaining recorded surface mechanics (fingerprint intern-on-commit, separator suffix tokens, `sepByIndent`, `elab`-family arms, capped raw-`Parser` shims).

**Architecture:** A `ScopeStack` unit in parser state tracks namespace/section/open events at the command loop (co-located with the existing grammar-growth hook); the current namespace threads as one parameter through both derivation chains (`notation.rs`, `surface.rs`). Activation is one shared predicate ("is this entry active under the current scope state?") consulted at the grammar read points, fed by scope tags on both same-file overlay entries and imported snapshot entries. Mechanics items are independent engine tasks; shims are data-driven off sweep skip-reasons.

**Tech Stack:** Rust workspace (crates: `leanr_syntax`, `leanr_grammar`, `leanr_olean`); Lean toolchain oracle via `dump_syntax_elab.lean`; cargo-fuzz; mise tasks.

## Global Constraints

- **Oracle-first:** every new semantic is dump-pinned. Draft fixture lines in this plan are STARTING POINTS — if the oracle dump disagrees with a draft (name shape, tree shape, activation behavior), **the dump wins**; update the draft and document the deviation in the task report. Regenerate targeted dumps with `lean --run tests/fixtures/syntax/dump_syntax_elab.lean tests/fixtures/syntax/<file>.lean` (the elaborating dumper — all fixtures here grow the grammar). Fixture symbols must be novel (not in Init) or they acquire `_1` kind-name suffixes.
- **Naming invariant:** all EXISTING fixtures and tests stay byte-identical. Top-level (empty-namespace) derived names must not change: `qualify("", local) == local`.
- **Never-panic / never-hang:** no `debug_assert!` on input-reachable paths (fuzz runs debug); scope-stack updates total on arbitrary input; both fuzz targets and the storm suite stay green.
- `leanr_kernel::Name` is the crate-root re-export path (`leanr_kernel::name::Name` is private, does not compile).
- **Sweep hygiene:** full sweeps only via `target/full_sweep_watchdog.sh` (RAYON_NUM_THREADS=5 + 27G anon watchdog; 32Gi container). `passlist:update` sets `LEANR_SWEEP_LIMIT=""`. Bounded sweeps gate only swept entries; full sweeps also gate deleted entries.
- **No numeric pass-rate target.** Pass-list growth is recorded evidence.
- Commit messages follow repo convention (`feat(syntax):`, `fix(syntax):`, `test(syntax):`, with `(M3b3 Task N)` suffix).
- Covering-test command for engine tasks: `cargo test -p leanr_syntax -p leanr_grammar`. Full gates only in Task 12.

---

### Task 1: ScopeStack unit + command-loop wiring

**Files:**
- Create: `crates/leanr_syntax/src/grammar/scope.rs`
- Modify: `crates/leanr_syntax/src/grammar/mod.rs` (add `pub(crate) mod scope;`)
- Modify: `crates/leanr_syntax/src/parse.rs` (`Ps` field + command-loop hook)
- Test: unit tests in `scope.rs` + integration tests in `parse.rs` tests module

**Interfaces:**
- Consumes: existing command productions `Lean.Parser.Command.{namespace,section,end,open}` (`builtin/command/command_open.rs`); the command loop's flatten/build machinery (`flatten_events`, `build_tree`, the peek in `command_may_grow_grammar`).
- Produces: `ScopeStack` with `current_namespace() -> &str`, `enter_namespace(&str)`, `enter_section(Option<&str>)`, `end_scope(Option<&str>)`, `open_namespace(&str)`, `active_namespaces() -> impl Iterator<Item=&str>` (Task 4 consumes `open_namespace`/`active_namespaces`; Task 2 consumes `current_namespace`). `pub(crate) fn scope_command_update(stack: &mut ScopeStack, root: &SyntaxNode, kinds: &KindInterner)` in scope.rs. `Ps.scope: ScopeStack` field. `SCOPE_COMMAND_KINDS: &[&str]` const in parse.rs.

- [ ] **Step 1: Write failing unit tests for ScopeStack semantics**

In `crates/leanr_syntax/src/grammar/scope.rs` (new file, tests first at bottom):

```rust
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
```

- [ ] **Step 2: Run to verify failure** — `cargo test -p leanr_syntax scope::` — Expected: FAIL (module/type not defined).

- [ ] **Step 3: Implement ScopeStack**

```rust
//! Same-file namespace/section/open scope tracking (M3b3 Task 1).
//! Consulted by derived-kind naming (Task 2: `stxNodeKind :=
//! currNamespace ++ name`) and by scoped-entry activation (Task 4).
//! Updates are TOTAL: arbitrary stray/mismatched `end`s must never
//! panic — worst case the stack diverges from the oracle's and the
//! ratchet reports non-green trees, never a crash.

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
```

(`active_namespaces()` is added in Task 4 when activation needs it — YAGNI here.)

- [ ] **Step 4: Run unit tests** — `cargo test -p leanr_syntax scope::` — Expected: PASS.

- [ ] **Step 5: Write failing integration test for tree-driven updates**

`scope_command_update` maps a parsed command node onto stack ops. In `scope.rs`:

```rust
/// Applies one top-level command's scope effect, if any. Total on
/// arbitrary trees (missing idents → no-op).
pub(crate) fn scope_command_update(
    stack: &mut ScopeStack,
    root: &crate::SyntaxNode,
    kinds: &crate::kind::KindInterner,
) {
    // implemented in Step 6
}
```

Test in `parse.rs` tests module (uses the established `parse_module` + first-command pattern; see `same_file_command_syntax_is_usable_without_panicking` at parse.rs:5212 for the idiom):

```rust
#[test]
fn scope_updates_follow_parsed_commands() {
    use crate::grammar::scope::{scope_command_update, ScopeStack};
    let snap = crate::builtin::snapshot();
    let mut stack = ScopeStack::new();
    let src = "namespace Foo.Bar\nsection\nend\nend Foo.Bar\n";
    let r = crate::parse_module(src, &snap);
    assert!(r.errors.is_empty(), "errs={:?}", r.errors);
    let expected = ["Foo.Bar", "Foo.Bar", "Foo.Bar", ""];
    for (cmd, want) in r.tree.root().children().zip(expected) {
        scope_command_update(&mut stack, &cmd, &r.tree.kinds);
        assert_eq!(stack.current_namespace(), want);
    }
}
```

- [ ] **Step 6: Implement `scope_command_update` + run test**

Dispatch on `kinds.name(root.kind())`:
- `Lean.Parser.Command.namespace` → `enter_namespace(ident_text)` where `ident_text` is the first `Ident` token's text under the node (reuse/mirror `first_ident_token_text` from surface.rs — hoist it to a shared location in `grammar/mod.rs` if visibility requires, do not duplicate).
- `Lean.Parser.Command.section` → `enter_section(optional ident text)`.
- `Lean.Parser.Command.end` → `end_scope(optional ident text)` (note `end`'s ident uses `ident_with_partial_trailing_dot()` — take the token text as-is, trimming any trailing `.`).
- `Lean.Parser.Command.open` → for now record nothing (Task 4 fills in the open-decl walk; leave a `// M3b3 Task 4` marker arm returning unit).
- anything else → no-op.

Run: `cargo test -p leanr_syntax scope_updates_follow_parsed_commands` — Expected: PASS.

- [ ] **Step 7: Wire into `Ps` and the command loop**

In parse.rs: add `scope: crate::grammar::scope::ScopeStack` to `Ps` (init in the constructor). Add alongside `GRAMMAR_GROWING_KINDS`:

```rust
/// Commands whose successful parse updates `Ps::scope` (M3b3 Task 1).
/// Same cheap-peek mechanism as `command_may_grow_grammar`.
pub(crate) const SCOPE_COMMAND_KINDS: &[&str] = &[
    "Lean.Parser.Command.namespace",
    "Lean.Parser.Command.section",
    "Lean.Parser.Command.end",
    "Lean.Parser.Command.open",
];
```

Refactor the peek: extract the body of `command_may_grow_grammar` into `fn peek_command_kind_name(&self, from_event: usize) -> Option<&str>` (returns the resolved outer kind name, overlay-first — preserving commit 6807f05's overlay-aware resolution exactly); `command_may_grow_grammar` becomes `self.peek_command_kind_name(e).is_some_and(|n| GRAMMAR_GROWING_KINDS.contains(&n))`. In the command loop's `Ok(())` arms, when the peeked name is in `SCOPE_COMMAND_KINDS`, build the subtree (same `flatten_events` + `build_tree` calls the grow arm uses) and call `scope_command_update(&mut ps.scope, &subtree.root(), &subtree.kinds)`. Scope commands are rare; the extra tree build is bounded by their count.

- [ ] **Step 8: Run covering tests** — `cargo test -p leanr_syntax -p leanr_grammar` — Expected: PASS, zero behavior change anywhere (nothing consumes the stack yet).

- [ ] **Step 9: Commit** — `git add -A && git commit -m "feat(syntax): ScopeStack tracks namespace/section/end at the command loop (M3b3 Task 1)"`

---

### Task 2: Namespace-qualified derived kind names

**Files:**
- Modify: `crates/leanr_syntax/src/grammar/notation.rs` (`derive_delta` signature, `build_spec` naming, module doc)
- Modify: `crates/leanr_syntax/src/grammar/surface.rs` (thread the parameter; `build_from_items` naming)
- Modify: `crates/leanr_syntax/src/parse.rs` (call site passes `ps.scope.current_namespace()`)
- Create: `tests/fixtures/syntax/StxNamespace.lean` + committed `.stx.jsonl` dump
- Test: parse.rs tests module + `oracle_golden.rs` (globs pick the fixture up automatically; verify)

**Interfaces:**
- Consumes: `Ps.scope.current_namespace() -> &str` (Task 1).
- Produces: `derive_delta(root, kinds, current_ns: &str) -> Option<GrammarDelta>` (new third parameter — Tasks 3/4/10 keep it); `qualify_kind_name(current_ns: &str, local: &str) -> String` in notation.rs, `pub(crate)` (Task 3 reuses it).

- [ ] **Step 1: Write the failing test (mangled + explicit names inside a namespace)**

In parse.rs tests module:

```rust
#[test]
fn syntax_inside_namespace_derives_qualified_kind() {
    let snap = crate::builtin::snapshot();
    let src = "namespace Widgetish\nsyntax \"wobns\" : term\n\
               macro_rules | `(wobns) => `(42)\n#check wobns\nend Widgetish\n";
    let r = crate::parse_module(src, &snap);
    assert_eq!(r.tree.text(), src);
    assert!(r.errors.is_empty(), "errs={:?}", r.errors);
    // DRAFT: qualified = "Widgetish." ++ category-mangled local name.
    // The StxNamespace dump (Step 4) is the byte authority — if the
    // oracle disagrees (qualification order, escaping), the dump wins;
    // update this assertion and document.
    assert!(
        r.tree
            .root()
            .descendants()
            .any(|n| r.tree.kinds.name(n.kind()) == "Widgetish.termWobns"),
        "expected namespace-qualified derived kind"
    );
}
```

- [ ] **Step 2: Run to verify failure** — Expected: FAIL (kind is currently unqualified `termWobns`).

- [ ] **Step 3: Thread the namespace parameter**

notation.rs:

```rust
/// `stxNodeKind := currNamespace ++ name` (module doc above) — the
/// qualification this file's mangler deliberately omitted until M3b3.
/// Components of `current_ns` are already legal ident parts (they came
/// from parsed `Ident` tokens); `local` is already escaped.
pub(crate) fn qualify_kind_name(current_ns: &str, local: &str) -> String {
    if current_ns.is_empty() {
        local.to_string()
    } else {
        format!("{current_ns}.{local}")
    }
}
```

- `derive_delta(root, kinds)` → `derive_delta(root, kinds, current_ns: &str)`; it forwards to `derive_notation`/`derive_mixfix`/`derive_surface` (all gain the parameter).
- notation.rs `build_spec`: wrap the final kind-name expression in `qualify_kind_name(current_ns, ...)`. The `is_local` branch (private naming) also qualifies — DRAFT: `_private.0.` applies to the QUALIFIED name (`_private.0.Widgetish.«term...»` vs `Widgetish._private.0....` is dump-forced in Task 3's probe; leave the draft, Task 3 pins it).
- surface.rs `build_from_items`: both arms of the `kind_name` match wrap in `qualify_kind_name(current_ns, ...)` (explicit `(name := ...)` also qualifies per `stxNodeKind := currNamespace ++ name` — the fixture pins it).
- parse.rs call site (the grow arm): `derive_delta(&subtree.root(), &subtree.kinds, ps.scope.current_namespace())`. **Order note:** the scope update for a command and grammar growth for the SAME command never coincide (`SCOPE_COMMAND_KINDS` ∩ `GRAMMAR_GROWING_KINDS` = ∅), so no ordering hazard.

- [ ] **Step 4: Create the probe fixture + dump**

`tests/fixtures/syntax/StxNamespace.lean` (DRAFT — every construct here was proven in-scope in M3b2b except the namespace interplay this probe exists to pin; simplify-escape-hatch applies):

```lean
namespace Widgetish
syntax "wobns" : term
macro_rules | `(wobns) => `(42)
#check wobns
syntax (name := probeNamed) "wobnamed" : term
macro_rules | `(wobnamed) => `(43)
#check wobnamed
namespace Inner
notation "wobnest" => 44
#check wobnest
end Inner
end Widgetish
#check wobns
```

(The trailing `#check wobns` after `end` pins that a plain — non-scoped — declaration stays ACTIVE after its namespace closes, with only the NAME qualified.)

Run: `lean --run tests/fixtures/syntax/dump_syntax_elab.lean tests/fixtures/syntax/StxNamespace.lean` → commit the resulting `.stx.jsonl`. Read the dump: pin the exact kind names (`Widgetish.termWobns`? `Widgetish.probeNamed`? `Widgetish.Inner.termWobnest…`?) and reconcile Step 1's assertion and the Step 3 draft.

- [ ] **Step 5: Run tests** — `cargo test -p leanr_syntax -p leanr_grammar && cargo test -p leanr_syntax --test oracle_golden` — Expected: PASS, including the new fixture's oracle-tree equality; ALL pre-existing fixtures byte-identical (empty-namespace qualification is the identity).

- [ ] **Step 6: Update the notation.rs module doc** — delete the "returns the LOCAL (category-scoped) name only" out-of-scope paragraph (it is now false); note `qualify_kind_name` as the port of `currNamespace ++ name`.

- [ ] **Step 7: Commit** — `git commit -m "feat(syntax): namespace-qualified derived kind names (M3b3 Task 2)"`

---

### Task 3: `local` naming for the `syntax`/`macro` surface

**Files:**
- Modify: `crates/leanr_syntax/src/grammar/notation.rs` (make `is_local_attr_kind` `pub(crate)`; expose a shared private-name helper)
- Modify: `crates/leanr_syntax/src/grammar/surface.rs` (route `local` through private naming; delete the stale "Known gap" doc paragraph at surface.rs:111-119)
- Create: `tests/fixtures/syntax/StxLocal.lean` + dump
- Test: parse.rs tests module + oracle_golden

**Interfaces:**
- Consumes: `is_local_attr_kind(attr_kind_node, kinds) -> bool` (notation.rs:674, made `pub(crate)`); `qualify_kind_name` (Task 2).
- Produces: `pub(crate) fn private_kind_name(qualified: &str) -> String` in notation.rs (DRAFT shape `format!("_private.0.{qualified}")` — refactored out of `mangle_private_kind`, which becomes a thin caller; Task 4 tags these entries `Local`).

- [ ] **Step 1: Failing test**

```rust
#[test]
fn local_syntax_derives_private_kind_name() {
    let snap = crate::builtin::snapshot();
    let src = "local syntax \"wobloc\" : term\n\
               macro_rules | `(wobloc) => `(45)\n#check wobloc\n";
    let r = crate::parse_module(src, &snap);
    assert!(r.errors.is_empty(), "errs={:?}", r.errors);
    // DRAFT: same `_private.0.` prefix notation/mixfix already pin.
    // StxLocal dump is the authority.
    assert!(
        r.tree
            .root()
            .descendants()
            .any(|n| r.tree.kinds.name(n.kind()).starts_with("_private.0.")
                && r.tree.kinds.name(n.kind()).contains("termWobloc")),
        "local syntax must derive the private kind name"
    );
}
```

- [ ] **Step 2: Run to verify failure** — Expected: FAIL (plain name today; the recorded gap).

- [ ] **Step 3: Implement**

surface.rs `derive_syntax_cmd`/`derive_macro_cmd` already locate the `attrKind` anchor (surface.rs:122-124). Pass `is_local: is_local_attr_kind(&attr_kind_node, kinds)` down to `build_from_items` (new parameter), and in the `kind_name` assembly: `let qualified = qualify_kind_name(current_ns, &local_name); if is_local { private_kind_name(&qualified) } else { qualified }`. In notation.rs, refactor `mangle_private_kind` so the prefixing lives in `private_kind_name(qualified)` and both paths share it — notation/mixfix behavior must not change (their existing golden tests are the guard). **Namespace × local interplay is dump-forced:** the StxLocal fixture includes a `namespace` block with a `local syntax` inside; whatever the dump says about prefix order (`_private.0.Ns.x` vs `Ns._private.0.x`) wins over this draft.

- [ ] **Step 4: Fixture**

`tests/fixtures/syntax/StxLocal.lean` (DRAFT, simplify-escape-hatch applies):

```lean
local syntax "wobloc" : term
macro_rules | `(wobloc) => `(45)
#check wobloc
namespace Widgloc
local syntax "woblocns" : term
macro_rules | `(woblocns) => `(46)
#check woblocns
end Widgloc
local macro "woblocm" : term => `(47)
#check woblocm
```

Regen + commit the dump; reconcile drafts against it.

- [ ] **Step 5: Run** — `cargo test -p leanr_syntax -p leanr_grammar && cargo test -p leanr_syntax --test oracle_golden` — Expected: PASS; notation/mixfix goldens untouched.

- [ ] **Step 6: Commit** — `git commit -m "feat(syntax): local syntax/macro derive private kind names (M3b3 Task 3)"`

---

### Task 4: Activation model — scope tags, open-set, same-file `scoped`

**Files:**
- Modify: `crates/leanr_syntax/src/grammar/mod.rs` (`NotationSpec` gains `scope`; new `SpecScope` enum)
- Modify: `crates/leanr_syntax/src/grammar/overlay.rs` (`CategoryDelta` entries carry scope; `fingerprint_into` covers it)
- Modify: `crates/leanr_syntax/src/grammar/scope.rs` (`open_namespace` wiring from `open` trees; `is_active` predicate)
- Modify: `crates/leanr_syntax/src/grammar/surface.rs` + `notation.rs` (produce the tag from `attrKind`)
- Modify: `crates/leanr_syntax/src/parse.rs` (read-point filtering; cache clearing on scope events)
- Create: `tests/fixtures/syntax/StxScoped.lean` + dump
- Test: parse.rs tests + oracle_golden + scope.rs unit tests

**Interfaces:**
- Consumes: `ScopeStack` (Task 1), `is_local_attr_kind` (Task 3), qualified naming (Task 2).
- Produces:
```rust
// grammar/mod.rs
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SpecScope {
    Global,
    /// `scoped` — active iff its namespace is in the active set.
    Scoped(String),
    /// `local` — active while at least `scope_len` scope entries remain
    /// (deactivates when its declaring scope pops). DRAFT semantics;
    /// StxScoped/StxLocal dumps are the authority.
    Local { scope_len: usize },
}
// NotationSpec gains: pub scope: SpecScope
// scope.rs
impl ScopeStack {
    pub(crate) fn is_active(&self, scope: &SpecScope) -> bool;
    pub(crate) fn scope_len(&self) -> usize;
    /// Active namespaces: every prefix of the current namespace path,
    /// plus every explicit open. DRAFT; dump-pinned.
    fn namespace_is_active(&self, ns: &str) -> bool;
}
```
Task 5 reuses `SpecScope` + `is_active` verbatim for imported entries.

- [ ] **Step 1: Unit tests for the activation predicate (failing)**

In scope.rs tests:

```rust
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
    let loc = SpecScope::Local { scope_len: s4.scope_len() };
    assert!(s4.is_active(&loc));
    s4.end_scope(None);
    assert!(!s4.is_active(&loc));
}
```

- [ ] **Step 2: Run to verify failure**, then implement `is_active`/`scope_len`/`namespace_is_active` (prefix set = walk `entries` accumulating namespace components; opens = the `opens` vec) and fill the `open` arm of `scope_command_update` (walk the parsed `open` node's `openSimple`/other sub-forms for dotted idents; each becomes `open_namespace` — sub-forms other than plain `open A B C` (renaming/hiding/scoped-open) contribute their namespace idents the same way; DRAFT, dump pins). Run: PASS.

- [ ] **Step 3: Thread `SpecScope` through registration (failing integration test first)**

```rust
#[test]
fn scoped_syntax_activates_and_deactivates() {
    let snap = crate::builtin::snapshot();
    // Uses: inside namespace (active), after end (INACTIVE → the use
    // line must NOT parse via the production), after open (active).
    let src = "namespace Widgsc\nscoped syntax \"wobsc\" : term\n\
               macro_rules | `(wobsc) => `(48)\n#check wobsc\nend Widgsc\n\
               open Widgsc\n#check wobsc\n";
    let r = crate::parse_module(src, &snap);
    assert_eq!(r.tree.text(), src);
    // Both #check lines are in active scope in THIS source; a variant
    // with a use between `end` and `open` belongs in the fixture (its
    // oracle dump shows the error shape — errors compare via the dump,
    // not via this unit test).
    assert!(r.errors.is_empty(), "errs={:?}", r.errors);
}
```

Implementation: `attrKind`'s scoped detector mirrors `is_local_attr_kind` with `"Lean.Parser.Term.scoped"`; add `is_scoped_attr_kind` beside it. Producers set `NotationSpec.scope`: `Scoped(current_ns.to_string())` for `scoped` (a scoped declaration's activation namespace is the CURRENT namespace — dump-pinned), `Local { scope_len: ... }` for `local` (parse.rs passes `ps.scope.scope_len()` through `derive_delta` context — extend the new third parameter into a small `NamingCtx<'_> { current_ns: &str, scope_len: usize }` struct rather than adding a fourth positional), `Global` otherwise. `CategoryDelta` becomes:

```rust
pub struct CategoryDelta {
    pub leading: Vec<(FirstTok, Prim, SpecScope)>,
    pub trailing: Vec<(FirstTok, Prim, SpecScope)>,
}
```

`Overlay::register` pushes `spec.scope` alongside; every existing read point in parse.rs that iterates `cd.leading`/`cd.trailing` gains a `ps.scope.is_active(scope)` filter. **Tokens stay globally registered** (DRAFT: Lean's token table is scope-less; the StxScoped dump's lex behavior on the inactive-use variant pins this — if the oracle lexes the inactive atom as an ident instead, move token registration behind the predicate and document).

- [ ] **Step 4: Cache + fingerprint discipline**

- The command loop clears `cat_cache` after any `SCOPE_COMMAND_KINDS` command (same rationale as after grammar growth: memoized candidate sets may now include/exclude scoped entries). Add to the Task 1 wiring point: `ps.clear_category_cache();` after `scope_command_update`. This makes the memo key activation-safe WITHOUT touching `CatCacheKey` — activation only changes at command boundaries and the cache never spans a scope event. Add a test: same source text where a term parses differently before/after `open` (the Step 3 fixture source already does — assert the two `#check` trees differ in the expected way per the dump).
- `fingerprint_into`: after each prim's `encode_prim`, hash the scope tag: `b"\x00"` for Global, `b"\x01" ++ ns ++ b"\0"` for Scoped, `b"\x02" ++ scope_len.to_le_bytes()` for Local. Bump the domain string to `b"leanr-m3b3-overlay-v1\0"`. Add a unit test: two overlays identical except one entry's scope tag produce different fingerprints.

- [ ] **Step 5: Fixture**

`tests/fixtures/syntax/StxScoped.lean` (DRAFT; the between-end-and-open inactive USE is the key line — the oracle's error tree for it is the activation pin):

```lean
namespace Widgsc
scoped syntax "wobsc" : term
macro_rules | `(wobsc) => `(48)
#check wobsc
end Widgsc
open Widgsc
#check wobsc
namespace Widgsc.Inner
#check wobsc
end Widgsc.Inner
```

Plus `tests/fixtures/syntax/StxScopedInactive.lean` (expected-errors fixture, Errors0/1 pattern — route it the same way those are routed in mise regen loops and parse-acceptance; check the globs):

```lean
namespace Widgsc2
scoped syntax "wobsc2" : term
macro_rules | `(wobsc2) => `(49)
end Widgsc2
#check wobsc2
```

Regen dumps (elab dumper), commit, reconcile all DRAFTs.

- [ ] **Step 6: Run** — `cargo test -p leanr_syntax -p leanr_grammar && cargo test -p leanr_syntax --test oracle_golden && cargo test -p leanr_syntax --test never_hang` — Expected: PASS.

- [ ] **Step 7: Commit** — `git commit -m "feat(syntax): scoped/local activation for same-file declarations (M3b3 Task 4)"`

---

### Task 5: Imported scoped entries activate on open

**Files:**
- Modify: `crates/leanr_grammar/src/assemble.rs` (Scoped entries: emit, don't skip)
- Modify: `crates/leanr_syntax/src/grammar/mod.rs` (`GrammarSnapshot` at :501 and `SnapshotBuilder` at :827 — scoped storage next to the category tables; follow the existing builder API shape: add `scoped_leading_prim(cat, ns, p)` / `scoped_trailing_prim(cat, ns, p)` mirroring `leading_prim`/`trailing_prim`)
- Modify: `crates/leanr_syntax/src/parse.rs` (`category()` read path merges active scoped snapshot entries via the SAME `ps.scope.is_active` predicate)
- Test: `crates/leanr_grammar/tests/` unit + the import-corpus step of parse-acceptance

**Interfaces:**
- Consumes: `SpecScope`/`is_active` (Task 4); `EntryScope::Scoped(NameId)` (module_data.rs:73-79, already decoded).
- Produces: snapshot-side scoped entry storage `Vec<(FirstTok, Prim, String /* activation ns */)>` per category (exact struct placement follows the snapshot's existing per-category layout); `SkipReason::ScopedInactive` disappears for parser entries (delete the variant only if nothing else references it; otherwise leave it with a "no longer produced" note).

- [ ] **Step 1: Failing unit test at the assemble layer** — build a snapshot from a synthetic module containing a `Scoped` parser entry (follow the existing assemble unit-test pattern in `crates/leanr_grammar/tests/` — find the test that feeds `parser_entries` with `EntryScope::Global` and clone its scaffolding with `EntryScope::Scoped(ns)`); assert the entry lands in scoped storage tagged with its namespace and NOT in the active tables, and that no `ScopedInactive` skip is recorded.

- [ ] **Step 2: Implement the assemble side** — replace the `EntryScope::Scoped(_) => { ...skip... continue; }` arm (assemble.rs:56-99): resolve `ns = name_of(*ns_id)`, and route `ParserEntry::Parser` interpretation through the SAME `crate::descr::interpret` call, delivering results via the new scoped builder methods. Scoped `Token`/`Kind`/`Category` sub-entries: DRAFT = register globally (tokens/kinds/categories are identity, not activation — consistent with Task 4's global-token draft); the corpus pin below is the authority. Run Step 1's test: PASS.

- [ ] **Step 3: Failing test at the parse layer** — locate a real stdlib/Mathlib scoped notation for the pin: grep the M3b2b sweep's skip log (or run a LEANR_SWEEP_LIMIT=50 bounded sweep and read recorded `ScopedInactive` decls — they were logged with decl names). Choose the simplest (a `scoped notation` or `scoped prefix` from Std/Init reachable from the import corpus). Add to the import-corpus fixtures (follow the M3b2a import-corpus pattern — a small `.lean` file importing the module and USING the notation after `open`): file both with and without the `open` line; dump both with the elab dumper; oracle trees pin activation.

- [ ] **Step 4: Implement the parse read path** — where `category()` consults base tables + overlay delta, additionally iterate the snapshot's scoped entries for that category with `ps.scope.is_active(&SpecScope::Scoped(ns))`. Keep the hot path cheap: scoped entries are a separate short vec — iterating it per category call only when non-empty adds nothing to the common (no-scoped-entries) case. Run: corpus tests PASS.

- [ ] **Step 5: Full covering run** — `cargo test -p leanr_syntax -p leanr_grammar && mise run parse:acceptance` — Expected: all green (parse:acceptance includes the import corpus; ~150-200s).

- [ ] **Step 6: Commit** — `git commit -m "feat(grammar): imported scoped entries activate on open/namespace (M3b3 Task 5)"`

---

### Task 6: Hardening — scope storms, quotation interaction, fuzz

**Files:**
- Modify: `crates/leanr_syntax/tests/never_hang.rs`
- Modify: fuzz corpus seeds (locate the fuzz targets' corpus dirs under `fuzz/`)
- Test: never_hang suite + both fuzz targets (bounded local run)

**Interfaces:** consumes everything from Tasks 1-5; produces no new API.

- [ ] **Step 1: Storm tests (write, then run — these must pass immediately if Tasks 1-5 are total; any failure is a real bug)**

```rust
#[test]
fn scope_storms_terminate() {
    let snap = leanr_syntax::builtin::snapshot();
    let cases = [
        // deep namespace nesting + interleaved stray ends
        &format!("{}{}", "namespace A.B.C\n".repeat(400), "end\n".repeat(1200)),
        // end-storm on empty stack
        "end\n".repeat(2000),
        // open-storm
        "open A\n".repeat(2000),
        // section/namespace interleave with mismatched names
        &"namespace X\nsection s\nend X\nend s\n".repeat(300).to_string(),
        // namespace inside a quotation must NOT touch the scope stack:
        // the quotation parses as a TERM; the following top-level use
        // pins that no namespace was entered (kind stays unqualified).
        "def q := `(namespace Ghost end Ghost)\nsyntax \"wobqt\" : term\n",
    ];
    for src in cases {
        let t0 = std::time::Instant::now();
        let r = leanr_syntax::parse_module(src, &snap);
        assert_eq!(r.tree.text(), *src, "lossless");
        assert!(t0.elapsed() < std::time::Duration::from_secs(10));
    }
}
```

(Follow `dollar_storms_terminate`'s exact idioms — timing bound, losslessness; add an error-presence assertion on the stray-end storm.) For the quotation case, additionally assert the derived kind for `wobqt` has NO `Ghost.` prefix.

- [ ] **Step 2: Fuzz** — add seeds exercising namespace/scoped/open combinations to the syntax target's corpus; run both targets bounded: `cargo +nightly fuzz run <syntax-target> -- -max_total_time=120` and the olean target likewise (find exact target names via `cargo fuzz list`). Expected: 0 findings.

- [ ] **Step 3: Commit** — `git commit -m "test(syntax): scope-storm + quotation-isolation hardening (M3b3 Task 6)"`

---

### Task 7: Fingerprint intern-on-commit (overlay rollback in Savepoint)

**Files:**
- Modify: `crates/leanr_syntax/src/grammar/overlay.rs` (`kind_count`, `truncate_kinds`)
- Modify: `crates/leanr_syntax/src/parse.rs` (`Savepoint` gains `overlay_kinds`; `save`/`restore` cover it)
- Test: parse.rs tests + overlay.rs unit tests

**Interfaces:**
- Produces: `Overlay::kind_count(&self) -> usize`; `Overlay::truncate_kinds(&mut self, n: usize)` (removes interned names with overlay index ≥ n from both `kind_names` and `kind_map`). `Savepoint.overlay_kinds: usize`.

- [ ] **Step 1: Failing test — fingerprint unchanged after failed antiquot**

```rust
#[test]
fn failed_antiquot_leaves_fingerprint_untouched() {
    let snap = crate::builtin::snapshot();
    let clean = crate::parse_module("#check 1\n", &snap);
    // `$` storms inside a quotation force antiquot ATTEMPTS that fail
    // and restore — before this task they left interned kinds behind.
    let stormy = crate::parse_module("def q := `($ $ $)\n#check 1\n", &snap);
    let fp = |r: &crate::ParseResult| {
        let mut h = blake3::Hasher::new();
        r.overlay.fingerprint_into(&mut h); // adjust to the actual
        // public path for the overlay fingerprint — find how M2's
        // cache consumer reads it (grep fingerprint_into callers) and
        // use that route; if the overlay isn't reachable from
        // ParseResult, expose a test-only accessor.
        h.finalize()
    };
    assert_eq!(fp(&clean), fp(&stormy),
        "failed antiquot attempts must not perturb the overlay fingerprint");
}
```

- [ ] **Step 2: Run to verify failure** (the current behavior interns `term.pseudo.antiquot`-style kinds — PR #13's fingerprint_into comment documents exactly this).

- [ ] **Step 3: Implement**

```rust
// overlay.rs
pub(crate) fn kind_count(&self) -> usize {
    self.kind_names.len()
}
pub(crate) fn truncate_kinds(&mut self, n: usize) {
    for name in self.kind_names.drain(n..) {
        self.kind_map.remove(&name);
    }
}
```

`Savepoint` gains `overlay_kinds: usize`; `save()` records `self.overlay.kind_count()`; `restore()` calls `self.overlay.truncate_kinds(sp.overlay_kinds)`. **Soundness argument (verify while implementing, cite in the commit):** kinds interned after a savepoint are referenced only by events after `sp.events`, which the same `restore` truncates; `register` (grammar growth) never runs between a save/restore pair — it happens in the command loop after commands COMPLETE. Confirm the latter by checking `register` call sites (parse.rs grow arm only). If any counterexample exists, STOP and report BLOCKED with the call path.

- [ ] **Step 4: Run** — Step 1 test PASS + `cargo test -p leanr_syntax -p leanr_grammar` PASS. Also update overlay.rs's `fingerprint_into` comment (PR #13's widened-semantics note) — the semantics are now precise again; say so.

- [ ] **Step 5: Commit** — `git commit -m "fix(syntax): overlay kind interning rolls back with Savepoint::restore (M3b3 Task 7)"`

---

### Task 8: Non-`","` separator suffix tokens

**Files:**
- Modify: `crates/leanr_syntax/src/builtin/mod.rs` (the `",*"` registration site — its own comment names the gap)
- Modify: `crates/leanr_syntax/src/grammar/overlay.rs` (`register` derives suffix tokens from `SepBy` prims in the body)
- Modify: `crates/leanr_grammar/src/` builder equivalent (imported productions with custom separators get the same treatment — grep how `,*` reached the builder token table and mirror)
- Create: `tests/fixtures/syntax/StxSepCustom.lean` + dump
- Test: parse.rs tests + oracle_golden

**Interfaces:**
- Consumes: `Prim::SepBy`/`SepBy1` (existing), splice-suffix handling from M3b2b Task 4.
- Produces: `fn sepby_suffix_tokens(body: &Prim, out: &mut Vec<String>)` (walk shared by overlay register and snapshot builder): for each `SepBy{sep,..}` with separator atom `s`, emit `format!("{s}*")` (and the `,*`-parity forms M3b2b registered — read the `",*"` builder comment for the exact set: it documents which suffixes exist for `,`; mirror for `s`).

- [ ] **Step 1: Fixture-first (the failing state is a silent misparse, so pin via oracle):**

`tests/fixtures/syntax/StxSepCustom.lean` (DRAFT — `|` separator; simplify-escape-hatch applies):

```lean
syntax "wobalt" sepBy(term, "|") : term
macro_rules | `(wobalt $xs|*) => `(42)
#check wobalt 1 | 2 | 3
def s := `(wobalt $[1]|* )
```

Dump with the elab dumper. If `$xs|*`/`$[..]|*` splice forms are what the oracle rejects in this shape, simplify toward whatever the M3b2b QuotSplice fixture pattern used for `,*` with the separator swapped — the POINT is one committed fixture where a non-comma suffix token must lex as ONE token.

- [ ] **Step 2: Failing test** — parse the fixture source with `parse_module`; assert oracle-tree equality via the canon path (this fails today via the documented silent-misparse: element unwrapped + stray text).

- [ ] **Step 3: Implement** — `sepby_suffix_tokens` walk; call it in `Overlay::register` after the existing `spec.tokens` loop, and at the snapshot-builder site that handles imported `SepBy` productions. Delete/adjust the silent-misparse comment in builtin/mod.rs to describe the now-closed gap.

- [ ] **Step 4: Run** — new test PASS; all existing suites PASS (`,`-separated behavior byte-identical — its suffixes were already registered; verify zero fixture churn).

- [ ] **Step 5: Commit** — `git commit -m "feat(syntax): derive suffix splice tokens for non-comma separators (M3b3 Task 8)"`

---

### Task 9: `sepByIndent`

**Files:**
- Modify: `crates/leanr_syntax/src/grammar/alias.rs` (entries) — plus whatever `Prim` support the oracle shape demands
- Create: `tests/fixtures/syntax/StxSepIndent.lean` + dump
- Test: oracle_golden + parse.rs tests

**Interfaces:** consumes `AliasPrim::{Unary,Binary}`; produces alias entries `"sepByIndent"`/`"sepBy1Indent"`.

- [ ] **Step 1: Read the oracle first** — `Lean/Parser/Extra.lean` defines `sepByIndent p sep = withPosition ((checkColGe ... p) ...)`-shaped desugarings (exact definition in the pinned toolchain source; read it, note it in the task report). Decide the mapping: if it decomposes into EXISTING prims (`WithPosition`, `CheckColGe`, `SepBy` with `allowTrailingSep`), the alias entry is a pure-combinator `Binary`; only add a new `Prim` variant if the dump proves the tree shape needs one (encode tag continues the M3b2b sequence — last used tag was 45 for `WithoutAnonymousAntiquot`; check `encode_prim` for the current max before assigning).
- [ ] **Step 2: Fixture** (DRAFT; the canonical user is `macro_rules`-with-tactic-alternatives style — keep it minimal):

```lean
syntax "wobind" sepByIndent(term, "; ") : term
macro_rules | `(wobind $[$xs]*) => `(42)
#check wobind 1; 2
```

Dump-pin; simplify-escape-hatch applies (the separator string and splice form follow the dump).
- [ ] **Step 3: TDD as usual** — failing canon-equality test → alias entries (+ prim if forced) → PASS → existing suites PASS.
- [ ] **Step 4: Commit** — `git commit -m "feat(syntax): sepByIndent aliases (M3b3 Task 9)"`

---

### Task 10: `elab` / `binderPredicate` derivation arms

**Files:**
- Modify: `crates/leanr_syntax/src/grammar/surface.rs` (`derive_elab_cmd`, `derive_binder_predicate` real implementations)
- Modify: `crates/leanr_syntax/src/parse.rs` (`GRAMMAR_GROWING_KINDS` rejoin: add back `"Lean.Parser.Command.elab"`, `"Lean.Parser.Command.binderPredicate"` — reverting PR #13's temporary drop, with the const comment updated)
- Create: `tests/fixtures/syntax/StxElab.lean` + dump
- Test: parse.rs tests + oracle_golden

**Interfaces:**
- Consumes: `build_from_items` (Task 3's `is_local` + Task 2's ctx parameters), `NamingCtx`.
- Produces: grammar-side derivation only — `elab`/`binderPredicate` register productions exactly like `syntax`; NO elaborator semantics (spec: out of scope, M4).

- [ ] **Step 1: Pin the node layout from real data.** The full sweep's oracle cache now holds real `elab` dumps (Task 8/M3b2b's report names Mathlib files that declare these — check `.superpowers/sdd/progress.md`'s Task 8 entry and grep `target/leanr-stx-cache` dumps for `Command.elab`). Derive the child-slot layout (attrKind / prec? / name? / prio? / items / `=>` tail) the same anchored-off-attrKind way `derive_syntax_cmd`'s doc comment records. `binderPredicate` registers into the `binderPred` category (confirm the category name from the dump).
- [ ] **Step 2: Fixture** (DRAFT):

```lean
elab "wobel" : term => Lean.Elab.Term.elabTerm (← `(42)) none
#check wobel
binder_predicate wobbp x " wobpred" => `($x > 0)
```

Elaborating dumper; simplify-escape-hatch (the `elab` body's RHS just needs to elaborate — any well-typed term elaborator expression works; swap per the dump/toolchain if this draft fails).
- [ ] **Step 3: TDD** — failing test asserting the derived kind appears and the follow-up use parses (mirror `same_file_command_syntax_is_usable_without_panicking`); implement `derive_elab_cmd` (anchored slots → `build_from_items` with the target category read off the outer node like `derive_syntax_cmd` does) + `derive_binder_predicate`; rejoin `GRAMMAR_GROWING_KINDS`; PASS; suites PASS.
- [ ] **Step 4: Commit** — `git commit -m "feat(syntax): elab/binderPredicate grammar derivation (M3b3 Task 10)"`

---

### Task 11: Raw-`Parser` shims (data-driven, capped)

**Files:**
- Create: `crates/leanr_syntax/src/grammar/shims.rs` (the table)
- Modify: `crates/leanr_syntax/src/grammar/alias.rs` (miss path consults shims before `return None`)
- Create: one probe fixture per shim entry (`StxShim<Name>.lean`)
- Test: oracle_golden + a shim-table unit test

**Interfaces:**
- Consumes: `AliasPrim` (all arities).
- Produces: `pub(crate) fn shim_lookup(name: &str) -> Option<AliasPrim>` — same contract as `alias::lookup`; `alias::lookup`'s `_ =>` arm becomes `_ => return shim_lookup(alias)`.

- [ ] **Step 1: Rank candidates from data.** The M3b3 full sweep hasn't run yet, so use the M3b2b full sweep's recorded skip reasons: extract unknown-parser-function names and their blocked-file counts (the sweep records skips; if the counts aren't logged, run `LEANR_SWEEP_LIMIT=300 mise run parse:mathlib` and harvest from its skip output). Take the top entries, **cap at 10**. Record the ranked table (name → files blocked → chosen/deferred) in the task report AND as a comment atop shims.rs.
- [ ] **Step 2: Per entry, oracle-first:** read the toolchain definition of the parser function; map to prims; write a minimal probe fixture using it through a `syntax` command; dump-pin; add the entry; test green. Entries that would need new `Prim` machinery beyond one variant are DEFERRED (recorded in the table) — this task is a table, not an engine extension.
- [ ] **Step 3: Suites green; commit** — `git commit -m "feat(syntax): raw-Parser shim table, top sweep-ranked entries (M3b3 Task 11)"`

---

### Task 12: M3b3 final gate — sweep growth + acceptance recording

**Files:**
- Modify: `tests/fixtures/syntax/mathlib-passlist.txt` (grown), `docs/superpowers/specs/2026-07-18-m3b3-naming-activation-design.md` (acceptance recorded)
- Possibly modify: `scripts/parse-acceptance.sh` globs (the `Stx*` pattern from M3b2b Task 10 should already cover the new fixtures — verify `StxNamespace`/`StxLocal`/`StxScoped*`/`StxSep*`/`StxElab`/`StxShim*` all match; extend if not) and the mise regen loops (all new fixtures are grammar-growing → elab-dumper loop; `StxScopedInactive` follows the Errors0/1 expected-errors routing)

- [ ] **Step 1: Full hermetic gates** — `cargo test --workspace && mise run lint && mise run lint:deps` — all PASS.
- [ ] **Step 2: `mise run parse:acceptance`** — all steps green, new fixtures included.
- [ ] **Step 3: Full sweep** — via `target/full_sweep_watchdog.sh` ONLY (32Gi container; do not invoke `mise run passlist:update` bare). Then `mise run parse:mathlib`: 0 regressions. Record: files swept, green count, delta vs the M3b2b baseline, and the divergence-class breakdown (top remaining skip reasons).
- [ ] **Step 4: Spot-check honesty** — 3-5 newly-green files actually use M3b3 semantics (`grep -l 'scoped syntax\|scoped notation\|local syntax\|namespace' `on them).
- [ ] **Step 5: Record acceptance in the spec's Goal section** (M3b2b convention, real numbers) and commit:

```bash
git add tests/fixtures/syntax/mathlib-passlist.txt scripts/parse-acceptance.sh \
        docs/superpowers/specs/2026-07-18-m3b3-naming-activation-design.md mise.toml
git commit -m "test(syntax): grow Mathlib pass-list + record M3b3 acceptance (M3b3 Task 12)"
```

---

## Plan notes

- **Task order is binding** (naming-first): 1 → 2 → 3 → 4 → 5 form the naming/activation spine; 6 hardens it; 7-11 are independent of each other (any order) but come after the spine; 12 is last.
- **Deferred-by-design:** `withWeakNamespace` (skip-and-record), shim entries beyond the cap, elaborator semantics (M4), `mkUnusedBaseName` `_1`-collision de-dup (still out of contract — notation.rs module doc keeps saying so).
- **Small pins folded in:** the precedence-interaction fixture and `macro_arg` `checkNoWsBefore` were considered and EXCLUDED from this plan: the former stays unpinned until a sweep divergence implicates it (record in Task 12's divergence table if it shows up); the latter is a zero-width over-accept with no green-file impact — reconsider only on sweep evidence. This is a deliberate YAGNI cut, not an oversight.
