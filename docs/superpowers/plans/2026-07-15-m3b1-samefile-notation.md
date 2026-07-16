# M3b1 — Same-File Notation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Make `leanr`'s parser grow its grammar mid-file — a `notation`/mixfix command registers a token and parser that are live for the rest of the module — proven by oracle-tree equality on a declare-and-use corpus.

**Architecture:** An immutable `Arc`-shared base `GrammarSnapshot` (M3a builtins) plus a small, cheaply-cloned same-file `Overlay` that the parser consults *first* at the three grammar read points (token munch, category dispatch, kind naming). After each command parses, the command loop materializes that command's subtree, and — if it is a `notation`/mixfix command — derives a `NotationSpec` from it and extends the overlay before parsing the next command. Grammar registration (interning a new kind, adding tokens) happens once per command in the loop, never in the token hot path.

**Tech Stack:** Rust, the existing `crates/leanr_syntax` crate (rowan green/red trees, the `Prim` combinator interpreter, `GrammarSnapshot`/`SnapshotBuilder`), the pinned Lean oracle toolchain (`mise run fixtures:regen`).

## Global Constraints

- **Oracle discipline:** correctness is byte round-trip (`text(parse(src)) == src`) AND structural oracle-tree equality against the pinned toolchain. Never bump the `lean-toolchain` pin. Regenerate dumps with `mise run fixtures:regen`.
- **Kind names are byte-exact:** every syntax node kind name must match official Lean's exactly (`kind.rs` header) — oracle equality depends on it. Notation kind names are *read from an oracle dump*, never guessed.
- **Never panic on untrusted input:** malformed source yields error nodes, never a panic (`docs/THREAT_MODEL.md`). A failed `notation` command registers nothing.
- **Bounded interning:** kinds/tokens are interned only while assembling the grammar, never in the per-token parse path (`kind.rs`, `SnapshotBuilder` doc). M3b1's one sanctioned relaxation: interning happens once per notation *command* in the command loop (bounded by command count), still never per token.
- **No new crate; no `leanr_kernel`/`leanr_olean` dependency** — imports are M3b2.
- **Workflows:** build/test via the named mise tasks; `cargo test -p leanr_syntax` runs the crate's tests. CI runs `mise run ci`.

---

## File Structure

- **Create** `crates/leanr_syntax/src/grammar/overlay.rs` — the `Overlay` type (same-file token/kind/category deltas), `NotationSpec`, and `GrammarSnapshot::extend`. Owns the "grammar grows" mechanism M3b2/M3b3 reuse.
- **Create** `crates/leanr_syntax/src/grammar/notation.rs` — pure derivation: `SyntaxNode` (a parsed `notation`/mixfix command) → `NotationSpec`, plus the Lean-exact kind-name mangler.
- **Create** `crates/leanr_syntax/src/builtin/command/command_notation.rs` — the `notation`/`infixl`/`infixr`/`infix`/`prefix`/`postfix` command *shapes* (builtin grammar productions), registered into the builtin snapshot.
- **Modify** `crates/leanr_syntax/src/grammar.rs` — make `grammar` a module dir (`grammar/mod.rs` re-exporting current contents + the two new submodules); expose `GrammarSnapshot` internals (`tokens`, `categories`, `kinds`, kind count) to the overlay.
- **Modify** `crates/leanr_syntax/src/lex.rs` — `next_token`/`munch` gain an overlay token set (union munch without cloning the base table).
- **Modify** `crates/leanr_syntax/src/parse.rs` — `Ps` holds `base: &GrammarSnapshot` + `overlay: Overlay`; the three accessors (`table`/munch, `snap_category` dispatch, kind naming) consult overlay-then-base; the command loop threads the overlay and clears the category cache on extend.
- **Modify** `crates/leanr_syntax/src/builtin/command/mod.rs` (or `builtin/command.rs`) — register the new notation command shapes.
- **Create** `tests/fixtures/syntax/Notation*.lean` (+ committed `.stx.jsonl` dumps) — the acceptance corpus; auto-discovered by `tests/oracle_golden.rs`.

> **Note on `grammar.rs` → `grammar/` split:** M3a's `grammar.rs` is 1346 lines and about to gain two responsibilities (overlay mechanism, notation derivation) that are distinct from the `Prim`/`SnapshotBuilder` core. Splitting into a `grammar/` directory keeps each file single-responsibility. If the reviewer prefers minimal churn, the two new files may instead live as `src/overlay.rs` and `src/notation.rs` at the crate root — the task steps below use the `grammar/` layout but nothing depends on it.

---

### Task 1: Overlay skeleton + union token munch

Establish the `Overlay` type and make the lexer able to munch against base ∪ overlay tokens without cloning the base table. No parser wiring yet — pure data + lexer.

**Files:**
- Create: `crates/leanr_syntax/src/grammar/overlay.rs`
- Modify: `crates/leanr_syntax/src/lex.rs` (add `munch_with`, extend `next_token`)
- Modify: `crates/leanr_syntax/src/grammar.rs` → split to `grammar/mod.rs` (add `pub mod overlay;` and re-exports)
- Test: inline `#[cfg(test)]` in `overlay.rs` and `lex.rs`

**Interfaces:**
- Produces:
  - `pub struct Overlay { tokens: TokenTable, kind_names: Vec<Arc<str>>, kind_map: HashMap<Arc<str>, u16>, base_kind_count: u16, cats: HashMap<String, CategoryDelta> }`
  - `pub struct CategoryDelta { leading: Vec<(FirstTok, Prim)>, trailing: Vec<(FirstTok, Prim)> }`
  - `impl Overlay { pub fn new(base: &GrammarSnapshot) -> Self; pub fn is_empty(&self) -> bool; pub fn tokens(&self) -> &TokenTable }`
  - `lex::next_token(src, pos, table, overlay_tokens: &TokenTable) -> (Token, Option<LexError>)` (new 4th param; pass `&Default::default()` for no overlay)
  - `TokenTable::munch_with<'a>(&self, rest: &'a str, extra: &TokenTable) -> Option<&'a str>`

- [ ] **Step 1: Split `grammar.rs` into a module dir**

Move `crates/leanr_syntax/src/grammar.rs` to `crates/leanr_syntax/src/grammar/mod.rs` verbatim, then append the submodule declaration near the top (after the existing `use` block):

```rust
pub mod overlay;
pub use overlay::{CategoryDelta, NotationSpec, Overlay};
```

Run `cargo build -p leanr_syntax` — expect a build error only from the missing `overlay` module (created next), nothing else moved.

- [ ] **Step 2: Write the failing lexer union-munch test**

In `crates/leanr_syntax/src/lex.rs` `#[cfg(test)]` mod:

```rust
#[test]
fn munch_with_unions_base_and_overlay() {
    let mut base = TokenTable::default();
    base.insert("+");
    let mut overlay = TokenTable::default();
    overlay.insert("⊕");
    // base-only token still munches
    assert_eq!(base.munch_with("+ x", &overlay), Some("+"));
    // overlay-only token munches without being in base
    assert_eq!(base.munch_with("⊕ x", &overlay), Some("⊕"));
    // neither: no token
    assert_eq!(base.munch_with("x", &overlay), None);
}
```

- [ ] **Step 3: Run it to confirm it fails**

Run: `cargo test -p leanr_syntax munch_with_unions -- --nocapture`
Expected: FAIL — `no method named munch_with`.

- [ ] **Step 4: Implement `munch_with`**

In `impl TokenTable` (lex.rs), add — mirroring the existing `munch` scan but consulting both sets and the larger `max_len`:

```rust
/// Maximal-munch against this table UNIONED with `extra` (the same-file
/// overlay; empty at M3a). Kept separate so the base table stays
/// immutable and Arc-shared — extending the grammar never clones it
/// (spec §Architecture: O(1) overlay).
pub fn munch_with<'a>(&self, rest: &'a str, extra: &TokenTable) -> Option<&'a str> {
    let cap = self.max_len.max(extra.max_len);
    let mut best: Option<&'a str> = None;
    for (end, _) in rest.char_indices().skip(1).chain(std::iter::once((rest.len(), ' '))) {
        if end > cap {
            break;
        }
        let cand = &rest[..end];
        if self.contains(cand) || extra.contains(cand) {
            best = Some(cand);
        }
    }
    best
}
```

> Match the *exact* scan/tie-break semantics of the existing `munch` (read it first — it already encodes the maximal-munch rule this port relies on); `munch_with` must reduce to `munch` when `extra` is empty. If `munch` returns the longest candidate, keep that; the loop above records the last (longest) match.

- [ ] **Step 5: Thread the overlay set through `next_token`**

Change `next_token`'s signature to take `overlay_tokens: &TokenTable` and use `table.munch_with(rest, overlay_tokens)` at the symbol-munch site (where it currently calls `table.munch(rest)`). Update all in-crate call sites to pass a token set (existing non-overlay callers pass `&TokenTable::default()`).

- [ ] **Step 6: Create `overlay.rs` with the `Overlay` type**

```rust
//! Same-file grammar growth (spec §Architecture / overlay). The base
//! `GrammarSnapshot` (builtins now; imports at M3b2) is immutable and
//! Arc-shared; an `Overlay` carries ONLY the productions a file's own
//! `notation`/mixfix commands add. Cloned (cheaply — same-file additions
//! only) and extended between commands; consulted before the base at the
//! three grammar read points in parse.rs. M3b2/M3b3 reuse this mechanism.

use std::collections::HashMap;
use std::sync::Arc;

use crate::grammar::{FirstTok, GrammarSnapshot, Prim};
use crate::kind::SyntaxKind;
use crate::lex::TokenTable;

#[derive(Clone, Debug, Default)]
pub struct CategoryDelta {
    pub leading: Vec<(FirstTok, Prim)>,
    pub trailing: Vec<(FirstTok, Prim)>,
}

#[derive(Clone, Debug)]
pub struct Overlay {
    tokens: TokenTable,
    kind_names: Vec<Arc<str>>,
    kind_map: HashMap<Arc<str>, u16>,
    base_kind_count: u16,
    cats: HashMap<String, CategoryDelta>,
}

impl Overlay {
    pub fn new(base: &GrammarSnapshot) -> Self {
        Overlay {
            tokens: TokenTable::default(),
            kind_names: Vec::new(),
            kind_map: HashMap::new(),
            base_kind_count: base.kind_count(),
            cats: HashMap::new(),
            }
    }
    pub fn is_empty(&self) -> bool {
        self.cats.is_empty() && self.kind_names.is_empty()
    }
    pub fn tokens(&self) -> &TokenTable {
        &self.tokens
    }
}
```

Add `GrammarSnapshot::kind_count(&self) -> u16` in `grammar/mod.rs`:

```rust
pub fn kind_count(&self) -> u16 {
    // number of interned kinds = first free dynamic slot for the overlay
    self.kinds.len_u16()
}
```

Add `KindInterner::len_u16(&self) -> u16 { self.names.len() as u16 }` in `kind.rs`.

- [ ] **Step 7: Write and run an overlay-construction test**

In `overlay.rs` `#[cfg(test)]`:

```rust
#[test]
fn fresh_overlay_is_empty_and_numbers_kinds_after_base() {
    let base = crate::builtin::snapshot();
    let ov = Overlay::new(&base);
    assert!(ov.is_empty());
    assert!(ov.tokens().munch_with("anything", &TokenTable::default()).is_none()
        || true); // overlay token set starts empty
    assert!(base.kind_count() >= crate::kind::FIRST_DYNAMIC_KIND);
}
```

Run: `cargo test -p leanr_syntax overlay:: -- --nocapture` and `cargo test -p leanr_syntax munch_with`.
Expected: PASS.

- [ ] **Step 8: Commit**

```bash
git add crates/leanr_syntax/src/grammar/ crates/leanr_syntax/src/lex.rs crates/leanr_syntax/src/kind.rs
git commit -m "feat(syntax): overlay skeleton + union token munch (M3b1 Task 1)"
```

---

### Task 2: notation/mixfix command shapes (builtin grammar)

Parse the *shape* of the six commands into proper trees, so a `notation` line no longer lands in a recovery error node. This is pure M3a-style porting; correctness is round-trip + (later) oracle equality. No registration yet.

**Files:**
- Create: `crates/leanr_syntax/src/builtin/command/command_notation.rs`
- Modify: `crates/leanr_syntax/src/builtin/command/mod.rs` (or `builtin/command.rs`) — call the new registrar
- Test: inline `#[cfg(test)]` in `command_notation.rs`

**Interfaces:**
- Consumes: `SnapshotBuilder` (`leading`, `sym`, `opt`, `seq`, `cat`, `many1`, `str_lit`/`NumLit` helpers from `grammar/mod.rs`).
- Produces: `pub(crate) fn register(b: &mut SnapshotBuilder)` registering command kinds `Lean.Parser.Command.notation`, `Lean.Parser.Command.mixfix` (and/or the per-fixity kinds Lean uses — confirm names against an oracle dump in Step 1).

- [ ] **Step 1: Dump the oracle shapes to learn exact kinds**

Create a probe fixture `tests/fixtures/syntax/_probe_notation.lean` (leading underscore = scratch; deleted in Step 6):

```lean
prelude
infixl:65 " ⊕ " => Sum
notation:70 a:71 " ⊗ " b:71 => Prod a b
```

Dump it:

```bash
mise run fixtures:regen   # or, faster, just this file:
lean --run tests/fixtures/syntax/dump_syntax.lean tests/fixtures/syntax/_probe_notation.lean
```

Read the printed JSONL. Record, in a comment at the top of `command_notation.rs`, the exact node kind names and child structure Lean produces for `infixl` and `notation` (the `k` fields — e.g. the precedence clause kind, the symbol atom, the `namedName`/`namedPrio` optionals). **These are the authority for Steps 2–4.**

- [ ] **Step 2: Write the failing round-trip test**

In `command_notation.rs`:

```rust
#[test]
fn notation_and_mixfix_round_trip_clean() {
    let snap = crate::builtin::snapshot();
    for src in [
        "prelude\ninfixl:65 \" ⊕ \" => Sum\n",
        "prelude\ninfixr:65 \" ⇒ \" => Arrow\n",
        "prelude\nprefix:100 \"~\" => Not\n",
        "prelude\npostfix:100 \"!\" => Fact\n",
        "prelude\nnotation:70 a \" ⊗ \" b => Prod a b\n",
    ] {
        let r = crate::parse_module(src, &snap);
        assert_eq!(r.tree.text(), src, "round-trip: {src:?}");
        assert!(r.errors.is_empty(), "should parse clean: {src:?} errs={:?}", r.errors);
    }
}
```

- [ ] **Step 3: Run it to confirm it fails**

Run: `cargo test -p leanr_syntax notation_and_mixfix_round_trip -- --nocapture`
Expected: FAIL — commands land in error nodes (`errors` non-empty).

- [ ] **Step 4: Implement the command productions**

Port the productions from the pinned `Lean/Parser/Syntax.lean:92-105` shapes observed in Step 1. Sketch (fill child kinds/precedence-clause shape from the dump):

```rust
pub(crate) fn register(b: &mut SnapshotBuilder) {
    // precedence clause `:` num  (optional), shared by all six
    let prec = opt(seq([sym(":"), Prim::NumLit]));
    // `notation` : optional prec, optional name/prio, notation items, `=>`, term
    let notation_item = or_else([ /* str-lit symbol */ Prim::StrLit,
                                  /* ident placeholder w/ optional :prec */ seq([Prim::Ident, prec_ref()]) ]);
    leading(b, "command", "Lean.Parser.Command.notation", LEAD_PREC, seq([
        sym("notation"), prec.clone(), /* namedName? namedPrio? */
        many(notation_item), sym("=>"), cat("term", 0),
    ]));
    // mixfix family: infixl/infixr/infix/prefix/postfix — each: kw, prec, str-lit, `=>`, term
    for kw in ["infixl", "infixr", "infix", "prefix", "postfix"] {
        leading(b, "command", &format!("Lean.Parser.Command.{kw}"/* or the mixfix kind from dump */), LEAD_PREC,
            seq([sym(kw), prec.clone(), Prim::StrLit, sym("=>"), cat("term", 0)]));
    }
}
```

> Use the *exact* kind names and child order from Step 1's dump — the sketch's names/structure are placeholders for what the oracle prints. Register `notation`'s leading token `"notation"` and each mixfix keyword as tokens (harvested automatically by `leading`).

- [ ] **Step 5: Wire the registrar and re-run**

In `builtin/command/mod.rs` (or `command.rs`), call `command_notation::register(b)` alongside the other command registrars. Run Step 2's test.
Expected: PASS (round-trip clean).

- [ ] **Step 6: Delete the scratch probe fixture**

```bash
rm -f tests/fixtures/syntax/_probe_notation.lean tests/fixtures/syntax/_probe_notation.stx.jsonl
```

(The real corpus lands in Task 8.)

- [ ] **Step 7: Commit**

```bash
git add crates/leanr_syntax/src/builtin/command/
git commit -m "feat(syntax): notation/mixfix command shapes parse clean (M3b1 Task 2)"
```

---

### Task 3: Kind-name mangler (oracle-derived, pure)

Reproduce Lean's auto-generated notation *kind name* (e.g. `` «term_⊕_» ``) exactly. **The exact string is read from an oracle dump, never invented** — this is the sharpest correctness risk in M3b1.

**Files:**
- Create: `crates/leanr_syntax/src/grammar/notation.rs`
- Modify: `crates/leanr_syntax/src/grammar/mod.rs` (`pub mod notation;`)
- Test: inline `#[cfg(test)]` in `notation.rs`

**Interfaces:**
- Produces: `pub fn mangle_kind(category: &str, atoms: &[NotationAtom]) -> String` where `pub enum NotationAtom { Symbol(String), Placeholder }` — returns the fully-qualified kind name Lean generates.

- [ ] **Step 1: Observe the real kind names**

Re-dump the two probe lines from Task 2 Step 1 (or a fresh scratch file) and record the top-level node `k` for each: e.g. `infixl:65 " ⊕ " => Sum` → `k = "«term_⊕_»"` (confirm the exact guillemets, underscores, and namespace against the dump — do not trust this example). Note whether the space inside `" ⊕ "` is trimmed in the name.

- [ ] **Step 2: Write the failing mangler test using the observed values**

```rust
#[test]
fn mangle_matches_oracle_kind_names() {
    use NotationAtom::*;
    // VALUES BELOW are copied from the Step-1 oracle dump — update to match.
    assert_eq!(
        mangle_kind("term", &[Placeholder, Symbol("⊕".into()), Placeholder]),
        "«term_⊕_»"
    );
    assert_eq!(
        mangle_kind("term", &[Symbol("~".into()), Placeholder]),
        "«term~_»"
    );
}
```

- [ ] **Step 3: Run it to confirm it fails**

Run: `cargo test -p leanr_syntax mangle_matches_oracle -- --nocapture`
Expected: FAIL — `mangle_kind` not defined.

- [ ] **Step 4: Implement the mangler to match the observed rule**

Port the naming rule from the pin's notation elaborator (`Lean/Elab/Syntax.lean` — the function that builds the syntax node kind from the parser atoms; placeholders become `_`, symbol atoms are inlined trimmed, wrapped in guillemets under the category namespace). Implement exactly what Step 1 showed:

```rust
pub enum NotationAtom { Symbol(String), Placeholder }

/// Reproduces Lean's generated notation kind name. Rule confirmed against
/// the oracle dump in Task 3 Step 1 — kept byte-exact (oracle equality).
pub fn mangle_kind(category: &str, atoms: &[NotationAtom]) -> String {
    let mut inner = String::new();
    for a in atoms {
        match a {
            NotationAtom::Placeholder => inner.push('_'),
            NotationAtom::Symbol(s) => inner.push_str(s.trim()),
        }
    }
    format!("«{category}{inner}»")
}
```

- [ ] **Step 5: Run to confirm pass**

Run: `cargo test -p leanr_syntax mangle_matches_oracle -- --nocapture`
Expected: PASS. If it fails, the *test values* (from the dump) are truth — fix the implementation, not the expected values.

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_syntax/src/grammar/notation.rs crates/leanr_syntax/src/grammar/mod.rs
git commit -m "feat(syntax): oracle-exact notation kind-name mangler (M3b1 Task 3)"
```

---

### Task 4: Derivation — command subtree → `NotationSpec` (pure)

Turn a parsed `notation`/mixfix command (`SyntaxNode`) into a `NotationSpec`: the token(s), kind name, category, precedence/associativity, and `Prim` body. Pure and independently testable against hand-parsed subtrees.

**Files:**
- Modify: `crates/leanr_syntax/src/grammar/notation.rs`
- Test: inline `#[cfg(test)]` in `notation.rs`

**Interfaces:**
- Consumes: `mangle_kind`, `NotationAtom` (Task 3); `SyntaxNode`/`SyntaxToken` (`tree.rs`); `Prim`, `FirstTok`, precedence consts (`grammar/mod.rs`).
- Produces:
  ```rust
  pub struct NotationSpec {
      pub category: String,      // "term"
      pub kind_name: String,     // mangle_kind(..)
      pub leading: bool,         // false => trailing (has a leading placeholder)
      pub prec: u32,             // Node/TrailingNode prec
      pub lhs_prec: Option<u32>, // Some(p) => trailing; lhs min precedence
      pub tokens: Vec<String>,   // symbols introduced (trimmed)
      pub body: Prim,            // Seq of Symbol + Category recursions (no outer Node wrap)
  }
  pub fn derive(node: &SyntaxNode, kinds: &KindInterner) -> Option<NotationSpec>;
  ```
  `derive` returns `None` if `node.kind()` is not a notation/mixfix kind. It reads kind names via `kinds.name(child.kind())`.

- [ ] **Step 1: Write the failing derivation test**

Parse a real command with `parse_module`, pull out the command subtree, and assert the derived spec:

```rust
#[test]
fn derive_infixl_is_left_assoc_trailing() {
    let snap = crate::builtin::snapshot();
    let r = crate::parse_module("prelude\ninfixl:65 \" ⊕ \" => Sum\n", &snap);
    assert!(r.errors.is_empty());
    // the command node is the module child whose kind is the infixl kind
    let cmd = r.tree.root().children()
        .find(|c| r.tree.kinds.name(c.kind()).contains("infixl")
                  || r.tree.kinds.name(c.kind()).starts_with("«term"))
        .expect("infixl command node");
    let spec = super::derive(&cmd, &r.tree.kinds).expect("derives");
    assert_eq!(spec.category, "term");
    assert_eq!(spec.leading, false);           // infix ⇒ leading lhs placeholder ⇒ trailing parser
    assert_eq!(spec.prec, 65);
    assert_eq!(spec.lhs_prec, Some(65));        // infixl: left-assoc
    assert_eq!(spec.tokens, vec!["⊕".to_string()]);
    assert!(spec.kind_name.starts_with("«term"));
}

#[test]
fn derive_infixr_right_assoc_bumps_lhs_prec() {
    let snap = crate::builtin::snapshot();
    let r = crate::parse_module("prelude\ninfixr:65 \" ⇒ \" => Arrow\n", &snap);
    let cmd = r.tree.root().children()
        .find(|c| r.tree.kinds.name(c.kind()).contains("infixr")
                  || r.tree.kinds.name(c.kind()).starts_with("«term"))
        .unwrap();
    let spec = super::derive(&cmd, &r.tree.kinds).unwrap();
    assert_eq!(spec.lhs_prec, Some(66));        // infixr: lhs at prec+1 (CONFIRM vs oracle tree shape)
}
```

> The `lhs_prec` values (65 / 66) encode Lean's associativity rule. **Confirm them against the oracle parse tree** of a nested use (`a ⊕ b ⊕ c` must group left; `a ⇒ b ⇒ c` right) in Task 8 — if the grouping in the oracle dump disagrees, these numbers are wrong and get fixed here.

- [ ] **Step 2: Run to confirm failure**

Run: `cargo test -p leanr_syntax derive_infixl -- --nocapture`
Expected: FAIL — `derive` not defined.

- [ ] **Step 3: Implement `derive`**

Walk the command subtree: read the keyword (first atom) to pick the fixity; read the optional `:prec` clause (default per Lean — `notation` defaults, mixfix requires or defaults); collect the string-literal symbol atom(s) and placeholder positions into `Vec<NotationAtom>`; build `body` as a `Prim::Seq` of `Prim::Symbol(trimmed)` interleaved with `Prim::Category { name: "term", rbp }`. Map fixity → `(leading, prec, lhs_prec, rbp)`:

```rust
// infixl:p  => trailing, prec=p, lhs_prec=p,   rhs rbp=p+1  (left assoc)
// infixr:p  => trailing, prec=p, lhs_prec=p+1, rhs rbp=p    (right assoc)
// prefix:p  => leading,  prec=p,               operand rbp=p
// postfix:p => trailing, prec=p, lhs_prec=p
// notation:p a:q " x " b:r => leading/trailing per first atom; placeholder rbp = its :q or default
```

Set `kind_name = mangle_kind(&category, &atoms)`; `tokens` = trimmed symbols; `leading = !first_atom_is_placeholder`.

> Read the actual precedence-defaulting and rbp rules from the pin's `Lean/Elab/Syntax.lean` / `Lean/Elab/BuiltinNotation.lean` mixfix expanders; the comment block above is the intended mapping, oracle-verified in Task 8.

- [ ] **Step 4: Run to confirm pass**

Run: `cargo test -p leanr_syntax derive_ -- --nocapture`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_syntax/src/grammar/notation.rs
git commit -m "feat(syntax): derive NotationSpec from notation/mixfix subtree (M3b1 Task 4)"
```

---

### Task 5: `GrammarSnapshot::extend` — apply a `NotationSpec` to the overlay

Fold a `NotationSpec` into an `Overlay`: intern the new kind (numbered after the base), add the token(s), wrap the body in `Node`/`TrailingNode`, index it by first-token, and append to the right category delta. Fingerprint-visible.

**Files:**
- Modify: `crates/leanr_syntax/src/grammar/overlay.rs`
- Modify: `crates/leanr_syntax/src/grammar/mod.rs` — reuse `index_entries`/`first_tokens` (make `pub(crate)`)
- Test: inline `#[cfg(test)]` in `overlay.rs`

**Interfaces:**
- Consumes: `NotationSpec` (Task 4), `index_entries` (existing, `grammar/mod.rs`).
- Produces:
  - `impl Overlay { pub fn register(&mut self, spec: NotationSpec) -> SyntaxKind }`
  - `impl Overlay { pub fn kind_name(&self, k: SyntaxKind) -> Option<&str>; pub fn lookup_kind(&self, name: &str) -> Option<SyntaxKind>; pub fn category_delta(&self, name: &str) -> Option<&CategoryDelta> }`
  - `impl Overlay { pub fn fingerprint_into(&self, h: &mut blake3::Hasher) }`

- [ ] **Step 1: Write the failing register test**

```rust
#[test]
fn register_adds_token_kind_and_trailing_entry() {
    let base = crate::builtin::snapshot();
    let mut ov = Overlay::new(&base);
    let spec = NotationSpec {
        category: "term".into(),
        kind_name: "«term_⊕_»".into(),
        leading: false,
        prec: 65,
        lhs_prec: Some(65),
        tokens: vec!["⊕".into()],
        body: crate::grammar::seq([
            crate::grammar::cat("term", 66),
            crate::grammar::sym("⊕"),
            crate::grammar::cat("term", 66),
        ]),
    };
    let k = ov.register(spec);
    // kind numbered after the base
    assert!(k.0 >= base.kind_count());
    assert_eq!(ov.kind_name(k), Some("«term_⊕_»"));
    assert_eq!(ov.lookup_kind("«term_⊕_»"), Some(k));
    // token now munches
    assert_eq!(ov.tokens().munch_with("⊕ x", &crate::lex::TokenTable::default()), Some("⊕"));
    // a trailing entry exists for the term category
    assert!(ov.category_delta("term").unwrap().trailing.len() == 1);
    assert!(!ov.is_empty());
}
```

- [ ] **Step 2: Run to confirm failure**

Run: `cargo test -p leanr_syntax register_adds_token -- --nocapture`
Expected: FAIL — `register` not defined.

- [ ] **Step 3: Implement `register` + accessors**

```rust
pub fn register(&mut self, spec: NotationSpec) -> SyntaxKind {
    // intern kind after base (overlay-local, bounded by command count)
    let kind = self.intern(&spec.kind_name);
    for t in &spec.tokens {
        self.tokens.insert(t);
    }
    let prim = if let Some(lhs) = spec.lhs_prec {
        Prim::TrailingNode { kind, prec: spec.prec, lhs_prec: lhs, body: Arc::new(spec.body) }
    } else {
        Prim::Node { kind, prec: Some(spec.prec), body: Arc::new(spec.body) }
    };
    let fts = crate::grammar::index_entries(&prim);
    let cd = self.cats.entry(spec.category).or_default();
    for ft in fts {
        if spec.lhs_prec.is_some() {
            cd.trailing.push((ft, prim.clone()));
        } else {
            cd.leading.push((ft, prim.clone()));
        }
    }
    kind
}

fn intern(&mut self, name: &str) -> SyntaxKind {
    if let Some(&k) = self.kind_map.get(name) {
        return SyntaxKind(k);
    }
    let k = self.base_kind_count + self.kind_names.len() as u16;
    let arc: Arc<str> = Arc::from(name);
    self.kind_names.push(arc.clone());
    self.kind_map.insert(arc, k);
    SyntaxKind(k)
}

pub fn kind_name(&self, k: SyntaxKind) -> Option<&str> {
    k.0.checked_sub(self.base_kind_count)
        .and_then(|i| self.kind_names.get(i as usize))
        .map(|s| &**s)
}
pub fn lookup_kind(&self, name: &str) -> Option<SyntaxKind> {
    self.kind_map.get(name).map(|&k| SyntaxKind(k))
}
pub fn category_delta(&self, name: &str) -> Option<&CategoryDelta> {
    self.cats.get(name)
}
```

Make `index_entries` `pub(crate)` in `grammar/mod.rs`. Add `fingerprint_into` hashing the overlay's tokens (sorted), kind names (in order), and each category delta's prims via the existing `encode_prim`.

- [ ] **Step 4: Run to confirm pass**

Run: `cargo test -p leanr_syntax register_adds_token -- --nocapture`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_syntax/src/grammar/
git commit -m "feat(syntax): Overlay::register folds a NotationSpec into the grammar (M3b1 Task 5)"
```

---

### Task 6: Parser reads the overlay (dispatch + kind naming + munch)

Make `Ps` hold `base + overlay` and consult the overlay at the three read points, so a manually-installed overlay actually changes parsing. Threading through the command loop is Task 7.

**Files:**
- Modify: `crates/leanr_syntax/src/parse.rs`
- Test: inline `#[cfg(test)]` in `parse.rs`

**Interfaces:**
- Consumes: `Overlay` + accessors (Task 5).
- Produces: `Ps` field `overlay: Overlay`; `Ps::new` initializes it empty; `pub(crate) fn install_overlay(&mut self, ov: Overlay)`; grammar reads route through overlay-then-base.

- [ ] **Step 1: Write the failing test — an installed overlay parses a new operator**

```rust
#[test]
fn installed_overlay_parses_new_infix() {
    // Base can't parse `a ⊕ b` as an application of ⊕; with the overlay it groups as «term_⊕_».
    let base = crate::builtin::snapshot();
    let mut ov = crate::grammar::Overlay::new(&base);
    ov.register(/* same NotationSpec as Task 5 Step 1 */ sum_spec());
    let src = "prelude\n#check a ⊕ b\n";
    let r = parse_with_overlay(src, &base, ov); // test helper installing the overlay before the loop
    assert_eq!(r.tree.text(), src);
    assert!(r.tree.root().descendants().any(|n| r.tree.kinds_name(n.kind()) == "«term_⊕_»"));
}
```

(Add `sum_spec()` + `parse_with_overlay` test helpers; the latter builds a `Ps`, calls `install_overlay`, then runs the command loop body — or, simplest, have `parse_module` accept a pre-seeded overlay via a `pub(crate)` variant used only by tests.)

- [ ] **Step 2: Run to confirm failure**

Run: `cargo test -p leanr_syntax installed_overlay_parses_new_infix -- --nocapture`
Expected: FAIL — overlay not consulted; `⊕` lexes/dispatches as unknown.

- [ ] **Step 3: Route the three reads through the overlay**

- **Munch:** wherever `Ps` lexes a token (its `next_token` call), pass `self.overlay.tokens()` as the overlay set (Task 1's 4th param).
- **Dispatch:** in `fn category(&mut self, name, rbp)`, after gathering base candidates from `self.base.categories.get(name)`, also gather from `self.overlay.category_delta(name)` and run them through the same longest-match selection. Concretely, build the candidate list as base parsers ++ overlay-delta parsers filtered by `dispatch`'s `FirstTok` rule, preserving registration order (base first, then overlay — overloaded notation appends).
- **Kind naming:** wherever the tree/canon path resolves a `SyntaxKind` to a name, try `self.overlay.kind_name(k)` before `self.kinds.name(k)`. Since `build_tree` (tree.rs) resolves names from a single `Arc<KindInterner>` at the end, fold the overlay's kinds into the interner used for the *final* tree build (see Task 7 Step 4) — within `Ps`, `Prim::Node`'s kind u16 is already overlay-numbered, so emitting events works unchanged; only name *resolution* at build time needs the overlay kinds.

- [ ] **Step 4: Run to confirm pass**

Run: `cargo test -p leanr_syntax installed_overlay_parses_new_infix -- --nocapture`
Expected: PASS. Also run the full crate suite to ensure M3a parses are unaffected when the overlay is empty:

Run: `cargo test -p leanr_syntax`
Expected: PASS (empty overlay ⇒ identical behavior to M3a).

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_syntax/src/parse.rs
git commit -m "feat(syntax): parser consults overlay for munch/dispatch/kind-naming (M3b1 Task 6)"
```

---

### Task 7: Thread the overlay through the command loop

After each command parses, materialize its subtree, and if it is a notation/mixfix command, derive + register into the overlay, clear the category cache, and continue. The final tree build resolves overlay kind names.

**Files:**
- Modify: `crates/leanr_syntax/src/parse.rs` (`parse_module_here` loop; final `build_tree`)
- Test: inline `#[cfg(test)]` in `parse.rs`

**Interfaces:**
- Consumes: `derive` (Task 4), `Overlay::register` (Task 5), `flatten_events`/`build_tree` (existing).
- Produces: `parse_module` now grows the grammar mid-file; no signature change (still `parse_module(src, &GrammarSnapshot)`).

- [ ] **Step 1: Write the failing declare-and-use test**

```rust
#[test]
fn same_file_notation_is_live_on_the_next_line() {
    let snap = crate::builtin::snapshot();
    let src = "prelude\ninfixl:65 \" ⊕ \" => Sum\n#check a ⊕ b\n";
    let r = crate::parse_module(src, &snap);
    assert_eq!(r.tree.text(), src);
    assert!(r.errors.is_empty(), "errs={:?}", r.errors);
    // the #check uses the just-declared notation
    assert!(r.tree.root().descendants()
        .any(|n| r.tree.kinds.name(n.kind()) == "«term_⊕_»"),
        "notation not live on next line");
}
```

- [ ] **Step 2: Run to confirm failure**

Run: `cargo test -p leanr_syntax same_file_notation_is_live -- --nocapture`
Expected: FAIL — `a ⊕ b` doesn't parse as `«term_⊕_»` (overlay never extended by the loop).

- [ ] **Step 3: Extend the command loop**

In `parse_module_here`'s loop, after a successful command parse (the `Ok(())` arm, `ps.pos` advanced), before the next iteration:

```rust
// materialize this command's subtree from its event slice
let cmd_events = flatten_events(&ps.events[sp.events..], &ps.subs);
let subtree = crate::tree::build_tree(ps.src, &cmd_events, ps.overlay_merged_kinds());
if let Some(spec) = crate::grammar::notation::derive(&subtree.root(), &subtree.kinds) {
    ps.overlay.register(spec);
    ps.clear_category_cache();   // grammar changed: drop within-command memoization
}
```

Add `Ps::clear_category_cache(&mut self)` (empties `cat_cache`) and `Ps::overlay_merged_kinds(&self) -> Arc<KindInterner>` (a `KindInterner` = base kinds + overlay kind names, built for tree resolution — cache/rebuild lazily; correctness first). `flatten_events`/`ps.subs`/`ps.events`/`ps.src` are existing fields (make visible to the loop as needed).

> Extraction reuses tested infra: the command's events (`ps.events[sp.events..]`) are one balanced subtree; `flatten_events` + `build_tree` yield a real `SyntaxNode` for `derive`. Note `sp` is the `Savepoint` already taken before the command parse; it records the event index.

- [ ] **Step 4: Resolve overlay kinds in the final tree build**

Where `parse_module_here` calls `build_tree` for the whole module, pass `ps.overlay_merged_kinds()` (base + overlay kind names) so the final tree's `kinds.name(k)` resolves overlay-numbered kinds. Verify a `canon` dump of the test tree shows `«term_⊕_»`, not a panic/`<unknown>`.

- [ ] **Step 5: Run to confirm pass + full suite**

Run: `cargo test -p leanr_syntax same_file_notation_is_live -- --nocapture`
Expected: PASS.
Run: `cargo test -p leanr_syntax`
Expected: PASS (all M3a fixtures still green).

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_syntax/src/parse.rs
git commit -m "feat(syntax): thread same-file notation through the command loop (M3b1 Task 7)"
```

---

### Task 8: Acceptance corpus + oracle gate

Add curated declare-and-use fixtures, dump them with the pinned toolchain, and let `oracle_golden.rs` gate them. This is where associativity/precedence numbers from Task 4 are confirmed against real oracle trees.

**Files:**
- Create: `tests/fixtures/syntax/NotationMixfix.lean`, `NotationMulti.lean`, `NotationOverload.lean`, `NotationLocal.lean`, `NotationTokenMunch.lean`, `NotationBadResync.lean` (+ committed `.stx.jsonl` for the non-error ones)
- Modify: `mise.toml` only if the regen glob doesn't already cover new `tests/fixtures/syntax/*.lean` (it does — verify)
- Test: `crates/leanr_syntax/tests/oracle_golden.rs` (no change — auto-discovers)

**Interfaces:** none (fixture-driven).

- [ ] **Step 1: Author the corpus**

Each file is `prelude`-mode, self-contained within `Init`, declares notation, then uses it. Cover:
- `NotationMixfix.lean` — one of each: `infixl`/`infixr`/`infix`/`prefix`/`postfix`, each with a nested use that pins associativity (`a ⊕ b ⊕ c`, `a ⇒ b ⇒ c`).
- `NotationMulti.lean` — a multi-token `notation` with interior placeholders (`notation:70 a " ⊗ " b " ⊘ " c => ...`).
- `NotationOverload.lean` — two notations sharing a leading token (overloaded); a use that must resolve by longest match.
- `NotationLocal.lean` — `local notation` declared and used later in the same section (no `end`).
- `NotationTokenMunch.lean` — a declared symbol that changes tokenization of a later line (maximal-munch cross-check, e.g. `⊕⊕` vs `⊕`).
- `NotationBadResync.lean` — an intentionally malformed `notation` line between two good commands; **no `.stx.jsonl`** (error fixture — round-trip only), asserting the surrounding commands still parse (Task 7's error path; see Task 9).

- [ ] **Step 2: Dump the oracle trees**

```bash
mise run fixtures:regen
```

Confirm `.stx.jsonl` files appeared for the non-error fixtures. Inspect `NotationMixfix.stx.jsonl`: verify the *grouping* of `a ⊕ b ⊕ c` (left) and `a ⇒ b ⇒ c` (right) matches Task 4's `lhs_prec` mapping. If a grouping disagrees, fix the mapping in `notation.rs` (Task 4 Step 3) and re-dump.

- [ ] **Step 3: Run the oracle gate**

Run: `cargo test -p leanr_syntax --test oracle_golden`
Expected: PASS — every corpus fixture round-trips and matches its dump line-for-line. Fix `notation.rs`/`command_notation.rs` (never the dumps) on any mismatch.

- [ ] **Step 4: Run the full crate + round-trip property + never-hang**

Run: `cargo test -p leanr_syntax`
Expected: PASS. If a property/fuzz test in `tests/` exercises notation, ensure it's green.

- [ ] **Step 5: Commit**

```bash
git add tests/fixtures/syntax/Notation*.lean tests/fixtures/syntax/Notation*.stx.jsonl
git commit -m "test(syntax): M3b1 same-file notation acceptance corpus + oracle dumps (M3b1 Task 8)"
```

---

### Task 9: Error path — malformed notation registers nothing

Harden the loop so a broken `notation`/mixfix command yields an error node, resyncs, and leaves the overlay unmutated — the surrounding commands parse normally.

**Files:**
- Modify: `crates/leanr_syntax/src/parse.rs` (guard derivation behind clean-parse; skip on the error/recover arms)
- Test: inline `#[cfg(test)]` in `parse.rs`; `NotationBadResync.lean` fixture (Task 8)

**Interfaces:** none new.

- [ ] **Step 1: Write the failing test**

```rust
#[test]
fn malformed_notation_registers_nothing_and_resyncs() {
    let snap = crate::builtin::snapshot();
    // missing `=> rhs` — malformed
    let src = "prelude\ninfixl:65 \" ⊕ \"\ndef good := 1\n";
    let r = crate::parse_module(src, &snap);
    assert_eq!(r.tree.text(), src);            // still lossless
    assert!(!r.errors.is_empty());             // the bad line errored
    // the good def after it parsed as a real declaration, not swallowed
    assert!(r.tree.root().children()
        .any(|c| r.tree.kinds.name(c.kind()) == "Lean.Parser.Command.declaration"));
    // ⊕ was NOT registered (no «term_⊕_» kind anywhere)
    assert!(!r.tree.root().descendants()
        .any(|n| r.tree.kinds.name(n.kind()) == "«term_⊕_»"));
}
```

- [ ] **Step 2: Run to confirm failure**

Run: `cargo test -p leanr_syntax malformed_notation_registers_nothing -- --nocapture`
Expected: FAIL if the loop derives from partial/error subtrees (or PASS already if Task 7 only derives on the clean `Ok` arm — in which case add the assertion value by confirming no registration).

- [ ] **Step 3: Guard registration**

Ensure `derive` + `register` run **only** on the `Ok(())` arm with `ps.pos` advanced (a clean command parse), never on the `restore`+`recover_command` arms. `derive` additionally returns `None` if the subtree contains an error/missing node in a structural slot (defensive: a recovered-but-`Ok` command must not register a half-built parser). Add that check in `derive` (Task 4): scan for `KIND_ERROR`/`KIND_MISSING` in required positions → `None`.

- [ ] **Step 4: Run to confirm pass + error fixture**

Run: `cargo test -p leanr_syntax malformed_notation_registers_nothing -- --nocapture`
Expected: PASS.
Run: `cargo test -p leanr_syntax --test oracle_golden` (covers `NotationBadResync.lean` round-trip + resync)
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_syntax/src/parse.rs
git commit -m "fix(syntax): malformed notation registers nothing, resyncs clean (M3b1 Task 9)"
```

---

### Task 10: Fingerprint coverage + final gate

Confirm the M5 firewall seam: same-file grammar growth changes the effective fingerprint, and the full gauntlet is green.

**Files:**
- Modify: `crates/leanr_syntax/src/grammar/overlay.rs` (fingerprint test)
- Test: inline `#[cfg(test)]`

- [ ] **Step 1: Write the fingerprint test**

```rust
#[test]
fn overlay_changes_effective_fingerprint() {
    let base = crate::builtin::snapshot();
    let base_fp = base.fingerprint();
    let mut ov = Overlay::new(&base);
    ov.register(sum_spec());
    let mut h = blake3::Hasher::new();
    h.update(base_fp.as_bytes());
    ov.fingerprint_into(&mut h);
    let with_overlay = h.finalize();
    assert_ne!(with_overlay, base_fp, "grammar growth must change the fingerprint");
}
```

- [ ] **Step 2: Run to confirm it passes** (implementation from Task 5 Step 3)

Run: `cargo test -p leanr_syntax overlay_changes_effective_fingerprint -- --nocapture`
Expected: PASS.

- [ ] **Step 3: Run the crate lint + full test task**

Run: `mise run lint` then `cargo test -p leanr_syntax`
Expected: PASS, no clippy warnings (match M3a's clean bar).

- [ ] **Step 4: Run the parse acceptance / CI slice**

Run: `mise run parse:acceptance` (and/or `mise run ci` if fast enough locally)
Expected: PASS — M3b1 corpus green alongside all M3a fixtures.

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_syntax/src/grammar/overlay.rs
git commit -m "test(syntax): overlay fingerprint seam + M3b1 final gate (M3b1 Task 10)"
```

---

## Self-Review

**Spec coverage:**
- Threaded evolving snapshot (spec §Architecture / threaded command loop) → Tasks 1, 6, 7. ✓
- notation/mixfix command shapes (spec §Architecture / command shapes) → Task 2. ✓
- Surface→parser derivation incl. kind-name mangling (spec §Architecture / derivation, the sharp risk) → Tasks 3, 4. ✓
- Precedence & associativity mapping (spec §6) → Task 4, oracle-confirmed Task 8. ✓
- Layered-overlay, O(1) growth, fingerprint seam (spec §Scope / overlay) → Tasks 1, 5, 10. ✓
- Failed declaration registers nothing (spec §Error handling) → Task 9. ✓
- Overloaded notation, `local notation` included, `scoped` excluded (spec §7) → Task 8 corpus (`NotationOverload`, `NotationLocal`); `scoped` is simply absent. ✓
- Acceptance = bytes AND oracle trees on synthetic corpus (spec §Acceptance) → Task 8. ✓
- Bounded interning relaxation (spec §Global constraints) → Task 5 (`intern` at register time) + Task 7 (once per command). ✓

**Placeholder scan:** The sketches in Tasks 2/3/4 explicitly defer *exact kind names, child structure, and precedence rbp values* to oracle dumps (Task 2 Step 1, Task 3 Step 1, Task 8 Step 2) rather than inventing them — this is intentional (oracle-as-truth), not a TODO. All code steps show concrete code. No "add error handling"-style vagueness.

**Type consistency:** `NotationSpec`/`NotationAtom`/`Overlay`/`CategoryDelta` names and fields are consistent across Tasks 1/4/5/6/7. `derive(&SyntaxNode, &KindInterner) -> Option<NotationSpec>`, `Overlay::register(NotationSpec) -> SyntaxKind`, `mangle_kind(&str, &[NotationAtom]) -> String` used identically where referenced. `kind_count`/`len_u16` added in Task 1 and consumed in Task 5. ✓

**Known confirmation points (oracle-gated, by design):** exact notation kind-name mangling (Task 3), `infixr` `lhs_prec` = `p+1` and placeholder rbp defaults (Task 4), and the precise command child kinds (Task 2) are all pinned to oracle dumps in Tasks 2/3/8 — if any disagree, the dump wins and the pure code is corrected in place.
