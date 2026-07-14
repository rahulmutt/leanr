# M3a — Parser Foundations Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build `crates/leanr_syntax` — lossless green/red syntax trees, Lean's table-driven tokenizer, the category/Pratt parsing machinery, the Rust-ported builtin grammar — plus the oracle dump harness, so a curated fixture corpus round-trips byte-exact AND matches official Lean's parse trees node-for-node.

**Architecture:** One new crate. The parser is an *interpreter* over a combinator data structure (`Prim`) — deliberately ParserDescr-shaped so M3b can map `.olean`-decoded ParserDescr values into the same representation. Parsing emits a flat event list; events build a rowan green tree at the end (speculation = event truncation, Pratt wrap = event insertion). All parser state flows through one explicit `GrammarSnapshot` value (token table + categories), never globals — the query-ready seam. Correctness authority is the oracle: a Lean script under the pinned toolchain dumps official parse trees as canonical JSON; golden fixtures diff ours against it.

**Tech Stack:** Rust (workspace-pinned 1.97.0 via mise), `rowan` (green/red trees), `blake3` (snapshot fingerprint). Oracle side: the pinned `leanprover/lean4:v4.32.0-rc1` toolchain (`lean --run` dump script). Test infra: proptest (already a workspace pattern), cargo-fuzz (mirrors `leanr_olean/fuzz`).

Spec: `docs/superpowers/specs/2026-07-13-m3a-parser-foundations-design.md`. Read it before starting.

## Global Constraints

- **Never bump the `lean-toolchain` pin** (`leanprover/lean4:v4.32.0-rc1`) — AGENTS.md. All oracle references below are to `$(lean --print-prefix)/src/lean/...` of that pin.
- **`leanr_syntax` depends on NO workspace crate** (spec §Architecture: "no `leanr_kernel` dependency for parsing itself"). Kind names are plain interned strings, not kernel `Name`s.
- **`leanr_cli` holds no parsing logic** — argument parsing + printing over `leanr_syntax` APIs only.
- **Untrusted-input rule** (`docs/THREAT_MODEL.md`): source text is arbitrary user bytes. The lexer and parser must never panic and never fail to terminate on any input; malformed input becomes error tokens/nodes + diagnostics.
- **Losslessness is total and by construction**: `text(parse(src)) == src` for every input, including files with parse errors.
- **Node-kind names must match official Lean's kind names byte-for-byte** (e.g. `Lean.Parser.Command.declaration`, `null`, `group`) — oracle-tree equality depends on it.
- **Canonical JSON schema is locked** (Task 7): object keys in *alphabetical order* (matches Lean `Json.compress` RBMap ordering): nodes `{"c":[...],"k":"<kind>"}`, atoms `{"a":"<text>","s":[start,stop]}`, idents `{"i":"<raw>","s":[start,stop]}`, missing `{"k":"<missing>"}`. Spans are byte offsets. Trivia never appears.
- **New external deps limited to:** `rowan`, `blake3` (runtime); `proptest`, `libfuzzer-sys` (dev/fuzz). Nothing else without a spec change. `mise run lint:deps` must pass after the dependency task.
- **Parse errors carry stable codes** (spec §Error handling): `E0301` unexpected token/expected-one-of, `E0302` unterminated string, `E0303` unterminated block comment, `E0304` invalid escape sequence, `E0305` invalid UTF-8 (CLI boundary), `E0306` unterminated `«` identifier escape, `E0307` tab character in source (Lean rejects tabs; minted in Task 2 per ORACLE-PORT), `E0308` isolated carriage return in source (minted in Task 2 per ORACLE-PORT). Codes never change meaning once shipped.
- **Where this plan cites an oracle source location for a port, the port must be checked against that source at execution time** — the pinned toolchain source is on disk and is the authority whenever this plan's inline code and the source disagree. Every such spot is marked `ORACLE-PORT`.
- Run `mise run fmt` before each commit; `mise run lint` and `mise run test` green at every commit.

## File Structure

| File | Action | Responsibility |
|---|---|---|
| `Cargo.toml` (workspace) | Modify | add `crates/leanr_syntax` member; exclude `crates/leanr_syntax/fuzz` |
| `crates/leanr_syntax/Cargo.toml` | Create | crate manifest: `rowan`, `blake3`; dev: `proptest` |
| `crates/leanr_syntax/src/lib.rs` | Create | crate doc + module list + public re-exports |
| `crates/leanr_syntax/src/kind.rs` | Create | `SyntaxKind` (u16), fixed leaf/utility kinds, `KindInterner` |
| `crates/leanr_syntax/src/tree.rs` | Create | rowan `Language` impl, `SyntaxTree`, `Event`, `build_tree` |
| `crates/leanr_syntax/src/canon.rs` | Create | oracle-canonical form: JSON-lines writer over the red tree |
| `crates/leanr_syntax/src/lex.rs` | Create | `TokenTable` (maximal munch), `TokenKind`, `next_token` |
| `crates/leanr_syntax/src/grammar.rs` | Create | `Prim` combinators, `Category`, `GrammarSnapshot`, `SnapshotBuilder`, fingerprint |
| `crates/leanr_syntax/src/parse.rs` | Create | `Ps` interpreter state, combinator semantics, Pratt loop, `parse_module`, recovery |
| `crates/leanr_syntax/src/builtin/mod.rs` | Create | `builtin::snapshot()` assembling the whole builtin grammar |
| `crates/leanr_syntax/src/builtin/level.rs` | Create | `level` category (oracle: `Lean/Parser/Level.lean`) |
| `crates/leanr_syntax/src/builtin/term.rs` | Create | `term` category (oracle: `Lean/Parser/Term.lean`) |
| `crates/leanr_syntax/src/builtin/do_notation.rs` | Create | do-notation (oracle: `Lean/Parser/Do.lean`) |
| `crates/leanr_syntax/src/builtin/tactic.rs` | Create | `tactic` category builtins (oracle: `Lean/Parser/Tactic.lean`) |
| `crates/leanr_syntax/src/builtin/command.rs` | Create | `command` category + module header (oracle: `Lean/Parser/Command.lean`, `Module.lean`) |
| `crates/leanr_syntax/tests/oracle_golden.rs` | Create | golden gate: fixture corpus vs committed oracle dumps + byte round-trip |
| `crates/leanr_syntax/tests/lossless.rs` | Create | proptest: totality of round-trip; reparse stability |
| `crates/leanr_syntax/fuzz/` | Create | cargo-fuzz target `parse_module` (mirrors `leanr_olean/fuzz`) |
| `tests/fixtures/syntax/*.lean` | Create | fixture corpus (builtin-only grammar; see Task 7) |
| `tests/fixtures/syntax/*.stx.jsonl` | Create | committed oracle dumps (regen via `mise run fixtures:regen`) |
| `tests/fixtures/syntax/dump_syntax.lean` | Create | oracle dump script (parse-only frontend loop) |
| `docs/superpowers/specs/2026-07-13-m3a-builtin-surface.md` | Create | enumerated builtin-parser table: in/out of M3a |
| `scripts/builtin-surface.sh` | Create | greps the pinned toolchain source for `@[builtin_*_parser]` |
| `scripts/parse-acceptance.sh` | Create | recorded acceptance run: fresh oracle dumps + diff + round-trip |
| `crates/leanr_cli/src/main.rs` | Modify | `leanr parse [--dump] <file>` |
| `mise.toml` | Modify | `fixtures:regen` additions; `fuzz` → `fuzz:olean`+`fuzz:syntax`; `parse:acceptance` |
| `ARCHITECTURE.md` | Modify | `leanr_syntax` crate entry |
| `docs/THREAT_MODEL.md` | Modify | source-text input row |
| `deny.toml` | Possibly modify | licenses for rowan's transitive deps |

**Module size discipline:** `builtin/term.rs` and `builtin/command.rs` are the growth risk. Keep each production a small `fn` returning `Prim`; if a file passes ~800 lines, split by grammar area (e.g. `term_binder.rs`) — boundaries are per-production functions, so splits are mechanical.

---

### Task 1: Crate scaffold, kinds, rowan trees, events, canonical JSON

**Files:**
- Modify: `Cargo.toml` (workspace `members` += `"crates/leanr_syntax"`)
- Create: `crates/leanr_syntax/Cargo.toml`
- Create: `crates/leanr_syntax/src/lib.rs`
- Create: `crates/leanr_syntax/src/kind.rs`
- Create: `crates/leanr_syntax/src/tree.rs`
- Create: `crates/leanr_syntax/src/canon.rs`
- Possibly modify: `deny.toml`

**Interfaces:**
- Produces: `kind::{SyntaxKind, KindInterner, KIND_WHITESPACE, KIND_LINE_COMMENT, KIND_BLOCK_COMMENT, KIND_ATOM, KIND_IDENT, KIND_ERROR_TOKEN, KIND_ERROR, KIND_MISSING, KIND_NULL, KIND_GROUP, KIND_CHOICE, FIRST_DYNAMIC_KIND}`; `tree::{Lang, SyntaxNode, SyntaxToken, SyntaxTree, Event, build_tree}`; `canon::{canon_jsonl, node_json}`. Consumed by every later task.
- Consumes: nothing.

- [ ] **Step 1: Scaffold the crate**

```bash
cd /workspace
mkdir -p crates/leanr_syntax/src
```

Workspace `Cargo.toml`: add `"crates/leanr_syntax"` to `members` (alphabetical: after `leanr_query`); add `"crates/leanr_syntax/fuzz"` to `exclude` (created in Task 12, excluded now so the entry never gets forgotten).

`crates/leanr_syntax/Cargo.toml`:

```toml
[package]
name = "leanr_syntax"
version.workspace = true
edition.workspace = true
license.workspace = true
repository.workspace = true

[dependencies]
rowan = "0.16"
blake3 = "1"

[dev-dependencies]
proptest = "1"
```

(If `cargo add rowan` resolves a different current major — 0.15 vs 0.16 — accept it; the API surface used below (`GreenNode`, `GreenNodeBuilder`, `SyntaxNode::new_root`, `Language`) is stable across both.)

`crates/leanr_syntax/src/lib.rs`:

```rust
//! Lossless Lean 4 syntax trees + the extensible parser (M3a: foundations).
//! Spec: docs/superpowers/specs/2026-07-13-m3a-parser-foundations-design.md
//!
//! The parser interprets a combinator data structure (`grammar::Prim`) —
//! deliberately ParserDescr-shaped so M3b can feed `.olean`-decoded
//! grammar into the same machinery. All parser state is one explicit
//! `GrammarSnapshot` value (the query-ready firewall seam); nothing is
//! global. Source text is untrusted input: no panic, no non-termination,
//! on any byte sequence (docs/THREAT_MODEL.md).

pub mod builtin;
pub mod canon;
pub mod grammar;
pub mod kind;
pub mod lex;
pub mod parse;
pub mod tree;

pub use grammar::GrammarSnapshot;
pub use parse::{parse_module, ParseError, ParseResult};
pub use tree::SyntaxTree;
```

(`builtin`, `grammar`, `lex`, `parse` don't exist yet — create empty placeholder modules `pub mod x {}`? No: create the files as empty `//! stub` files now so the crate compiles at every commit; each later task fills its file. Concretely: `touch` each `src/*.rs` listed in File Structure with just a `//!` doc line, and `src/builtin/mod.rs` with `//! stub`.)

- [ ] **Step 2: Write the failing tests for kinds + trees** — `crates/leanr_syntax/src/kind.rs`:

```rust
//! Interned syntax-node kinds. Lean kinds are an open set of hierarchical
//! NAMES (`Lean.Parser.Command.declaration`, Mathlib's own kinds, …);
//! rowan raw kinds are u16. `KindInterner` bridges (spec §Architecture:
//! a few thousand kinds in practice, far under 65k). Kind names must
//! match official Lean's byte-for-byte — oracle equality depends on it.

use std::collections::HashMap;
use std::sync::Arc;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct SyntaxKind(pub u16);

// Fixed leaf/utility kinds. Leaves first (tests use `is_trivia`/`is_leaf`).
pub const KIND_WHITESPACE: SyntaxKind = SyntaxKind(0);
pub const KIND_LINE_COMMENT: SyntaxKind = SyntaxKind(1);
pub const KIND_BLOCK_COMMENT: SyntaxKind = SyntaxKind(2);
/// Keyword/symbol leaf ("def", ":=", "=>", …) — Lean `Syntax.atom`.
pub const KIND_ATOM: SyntaxKind = SyntaxKind(3);
/// Identifier leaf — Lean `Syntax.ident` (raw source text, incl. escapes).
pub const KIND_IDENT: SyntaxKind = SyntaxKind(4);
/// Unlexable byte run (untrusted-input totality; never panic).
pub const KIND_ERROR_TOKEN: SyntaxKind = SyntaxKind(5);
/// Error NODE produced by recovery (contains skipped tokens).
pub const KIND_ERROR: SyntaxKind = SyntaxKind(6);
/// Lean `Syntax.missing`.
pub const KIND_MISSING: SyntaxKind = SyntaxKind(7);
/// Lean nullKind ("null"): optional/many/sepBy grouping.
pub const KIND_NULL: SyntaxKind = SyntaxKind(8);
pub const KIND_GROUP: SyntaxKind = SyntaxKind(9);
pub const KIND_CHOICE: SyntaxKind = SyntaxKind(10);
pub const FIRST_DYNAMIC_KIND: u16 = 11;

pub fn is_trivia(k: SyntaxKind) -> bool {
    k == KIND_WHITESPACE || k == KIND_LINE_COMMENT || k == KIND_BLOCK_COMMENT
}

pub fn is_leaf(k: SyntaxKind) -> bool {
    k.0 <= KIND_ERROR_TOKEN.0
}

/// Append-only name↔u16 interner. Built once per `GrammarSnapshot`
/// (snapshot construction pre-interns every kind its grammar can emit),
/// shared `Arc` with every tree parsed under it — parsing itself never
/// mutates the interner.
#[derive(Debug)]
pub struct KindInterner {
    names: Vec<Arc<str>>,
    map: HashMap<Arc<str>, u16>,
}

impl KindInterner {
    pub fn new() -> Self {
        let mut it = KindInterner { names: Vec::new(), map: HashMap::new() };
        // Fixed slots — order MUST match the constants above. The oracle-
        // visible names among them: "null", "group", "choice", "<missing>".
        for name in [
            "<whitespace>", "<line-comment>", "<block-comment>", "<atom>",
            "<ident>", "<error-token>", "<error>", "<missing>", "null",
            "group", "choice",
        ] {
            it.intern(name);
        }
        it
    }

    pub fn intern(&mut self, name: &str) -> SyntaxKind {
        if let Some(&k) = self.map.get(name) {
            return SyntaxKind(k);
        }
        let k = u16::try_from(self.names.len())
            .expect("more than 65535 distinct syntax kinds in one snapshot");
        let arc: Arc<str> = Arc::from(name);
        self.names.push(arc.clone());
        self.map.insert(arc, k);
        SyntaxKind(k)
    }

    pub fn lookup(&self, name: &str) -> Option<SyntaxKind> {
        self.map.get(name).map(|&k| SyntaxKind(k))
    }

    pub fn name(&self, k: SyntaxKind) -> &str {
        &self.names[k.0 as usize]
    }
}

impl Default for KindInterner {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn fixed_kinds_occupy_their_slots() {
        let it = KindInterner::new();
        assert_eq!(it.name(KIND_NULL), "null");
        assert_eq!(it.name(KIND_MISSING), "<missing>");
        assert_eq!(it.lookup("group"), Some(KIND_GROUP));
    }

    #[test]
    fn intern_is_idempotent_and_dynamic_kinds_start_after_fixed() {
        let mut it = KindInterner::new();
        let k1 = it.intern("Lean.Parser.Command.declaration");
        let k2 = it.intern("Lean.Parser.Command.declaration");
        assert_eq!(k1, k2);
        assert_eq!(k1.0, FIRST_DYNAMIC_KIND);
        assert_eq!(it.name(k1), "Lean.Parser.Command.declaration");
    }
}
```

- [ ] **Step 3: `tree.rs` — rowan bridge, events, builder**

```rust
//! Lossless green/red trees over rowan (spec §Architecture / tree).
//! Every source byte — trivia included — is a token in the tree, so
//! `text(parse(src)) == src` holds by construction. The parser emits a
//! flat `Event` list; `build_tree` folds it into a rowan green tree.
//! Events (not a live builder) because the Pratt machinery needs
//! speculation (truncate events) and trailing wraps (insert a Start),
//! neither of which rowan's `GreenNodeBuilder` supports directly.
//! This event layer is our trait-shaped boundary around rowan: if
//! rowan's model ever fights us, only `build_tree` changes (spec's
//! recorded escape hatch).

use std::sync::Arc;

use rowan::{GreenNode, GreenNodeBuilder};

use crate::kind::{KindInterner, SyntaxKind};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Lang {}

impl rowan::Language for Lang {
    type Kind = SyntaxKind;
    fn kind_from_raw(raw: rowan::SyntaxKind) -> SyntaxKind {
        SyntaxKind(raw.0)
    }
    fn kind_to_raw(kind: SyntaxKind) -> rowan::SyntaxKind {
        rowan::SyntaxKind(kind.0)
    }
}

pub type SyntaxNode = rowan::SyntaxNode<Lang>;
pub type SyntaxToken = rowan::SyntaxToken<Lang>;

/// Flat parse event. Token text is carried by (offset, len) into the
/// source — the builder slices the original `src`, which is what makes
/// losslessness structural rather than best-effort.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Event {
    Start(SyntaxKind),
    Token { kind: SyntaxKind, offset: u32, len: u32 },
    Finish,
    /// Lean `Syntax.missing` leaf (zero-width).
    Missing,
}

/// A parsed module: the green tree + the interner that names its kinds.
#[derive(Clone, Debug)]
pub struct SyntaxTree {
    pub green: GreenNode,
    pub kinds: Arc<KindInterner>,
}

impl SyntaxTree {
    pub fn root(&self) -> SyntaxNode {
        SyntaxNode::new_root(self.green.clone())
    }

    /// The exact source text — byte-identical to the parser input.
    pub fn text(&self) -> String {
        self.root().text().to_string()
    }
}

/// Fold events into a green tree. `events` must be balanced
/// (Start/Finish match) and wrapped in exactly one root node — the
/// parser guarantees both; debug_asserts document the contract.
pub fn build_tree(src: &str, events: &[Event], kinds: Arc<KindInterner>) -> SyntaxTree {
    let mut builder = GreenNodeBuilder::new();
    let mut depth: i64 = 0;
    for ev in events {
        match ev {
            Event::Start(kind) => {
                builder.start_node(rowan::SyntaxKind(kind.0));
                depth += 1;
            }
            Event::Token { kind, offset, len } => {
                let s = *offset as usize;
                let e = s + *len as usize;
                builder.token(rowan::SyntaxKind(kind.0), &src[s..e]);
            }
            Event::Finish => {
                builder.finish_node();
                depth -= 1;
            }
            Event::Missing => {
                // Zero-width leaf; canonicalizes to {"k":"<missing>"}.
                builder.token(
                    rowan::SyntaxKind(crate::kind::KIND_MISSING.0),
                    "",
                );
            }
        }
        debug_assert!(depth >= 0, "unbalanced Finish");
    }
    debug_assert_eq!(depth, 0, "unbalanced Start");
    SyntaxTree { green: builder.finish(), kinds }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kind::{KindInterner, KIND_ATOM, KIND_IDENT, KIND_WHITESPACE};

    /// Hand-build `def x` as (root (decl "def" WS ident)) and check
    /// byte-exact text() and tree shape.
    #[test]
    fn events_build_a_lossless_tree() {
        let src = "def x";
        let mut it = KindInterner::new();
        let root = it.intern("module");
        let decl = it.intern("Lean.Parser.Command.declaration");
        let events = vec![
            Event::Start(root),
            Event::Start(decl),
            Event::Token { kind: KIND_ATOM, offset: 0, len: 3 },
            Event::Token { kind: KIND_WHITESPACE, offset: 3, len: 1 },
            Event::Token { kind: KIND_IDENT, offset: 4, len: 1 },
            Event::Finish,
            Event::Finish,
        ];
        let tree = build_tree(src, &events, Arc::new(it));
        assert_eq!(tree.text(), src);
        let root_node = tree.root();
        assert_eq!(tree.kinds.name(root_node.kind()), "module");
        let decl_node = root_node.first_child().unwrap();
        assert_eq!(
            tree.kinds.name(decl_node.kind()),
            "Lean.Parser.Command.declaration"
        );
        assert_eq!(decl_node.children_with_tokens().count(), 3);
    }
}
```

- [ ] **Step 4: `canon.rs` — the locked canonical JSON**

```rust
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

use crate::kind::{
    is_trivia, KindInterner, KIND_ATOM, KIND_ERROR_TOKEN, KIND_IDENT,
    KIND_MISSING,
};
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
                if !first { out.push(','); }
                first = false;
                node_json(&n, kinds, out);
            }
            rowan::NodeOrToken::Token(t) => {
                let k = t.kind();
                if is_trivia(k) {
                    continue;
                }
                if !first { out.push(','); }
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
            Event::Token { kind: KIND_ATOM, offset: 0, len: 3 },
            Event::Token { kind: KIND_WHITESPACE, offset: 3, len: 1 },
            Event::Token { kind: KIND_IDENT, offset: 4, len: 1 },
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
```

- [ ] **Step 5: Build + dependency gates**

Run: `cargo build -p leanr_syntax && cargo test -p leanr_syntax && mise run lint:deps`
Expected: 5 tests pass. If `cargo deny` flags rowan's transitive deps (`text-size`, `countme`, `hashbrown` — all MIT/Apache-2.0), no waiver should be needed; if one fires anyway, extend `deny.toml` `[licenses] allow` with exactly the flagged identifier + a `# rowan (M3a syntax trees)` comment. Advisory/source failures: stop and reassess.

- [ ] **Step 6: Commit**

```bash
mise run fmt
git add -A
git commit -m "feat(syntax): leanr_syntax scaffold — kind interner, rowan event trees, canonical JSON (M3a Task 1)"
```

---

### Task 2: Token table + trivia lexing (whitespace, comments)

**Files:**
- Create (fill): `crates/leanr_syntax/src/lex.rs`

**Interfaces:**
- Produces: `lex::{TokenTable, TokenKind, Token, LexError, next_token}`. `TokenKind::{Whitespace, LineComment, BlockComment, Atom, Ident, Num, Scientific, Str, Char, NameLit, ErrorTok, Eof}`. `next_token(src: &str, pos: usize, table: &TokenTable) -> (Token, Option<LexError>)` where `Token { kind: TokenKind, len: u32 }`. Consumed by Tasks 3, 5, 6.
- Consumes: nothing from other tasks.

**Oracle:** the tokenizer in `$(lean --print-prefix)/src/lean/Lean/Parser/Basic.lean` — `whitespace`, `finishCommentBlock` (nested block comments), and the token-table munch in `tokenFnAux`/`peekToken`. ORACLE-PORT throughout this task.

- [ ] **Step 1: Write the failing tests** — bottom of `lex.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    fn lex_all(src: &str, table: &TokenTable) -> Vec<(TokenKind, &str)> {
        let mut out = Vec::new();
        let mut pos = 0;
        loop {
            let (tok, _err) = next_token(src, pos, table);
            if tok.kind == TokenKind::Eof {
                break;
            }
            out.push((tok.kind, &src[pos..pos + tok.len as usize]));
            pos += tok.len as usize;
            assert!(tok.len > 0, "lexer must always make progress");
        }
        out
    }

    #[test]
    fn maximal_munch_prefers_the_longest_table_entry() {
        let mut t = TokenTable::default();
        t.insert(":");
        t.insert(":=");
        t.insert("=");
        t.insert("=>");
        assert_eq!(
            lex_all(":= = => :", &t),
            vec![
                (TokenKind::Atom, ":="),
                (TokenKind::Whitespace, " "),
                (TokenKind::Atom, "="),
                (TokenKind::Whitespace, " "),
                (TokenKind::Atom, "=>"),
                (TokenKind::Whitespace, " "),
                (TokenKind::Atom, ":"),
            ]
        );
    }

    #[test]
    fn line_comments_run_to_newline_exclusive_of_nothing() {
        let t = TokenTable::default();
        let toks = lex_all("-- hi\n", &t);
        assert_eq!(toks[0], (TokenKind::LineComment, "-- hi\n"));
    }

    #[test]
    fn block_comments_nest() {
        let t = TokenTable::default();
        let toks = lex_all("/- a /- b -/ c -/x", &t);
        assert_eq!(toks[0], (TokenKind::BlockComment, "/- a /- b -/ c -/"));
    }

    #[test]
    fn doc_comments_are_not_trivia() {
        // `/--` and `/-!` open DOC comments — tokens, not trivia
        // (Lean: whitespace's block-comment case explicitly excludes
        // a following '-' or '!'). With "/--" in the table they lex as
        // atoms; the docComment parser (Task 10) consumes the body.
        let mut t = TokenTable::default();
        t.insert("/--");
        let toks = lex_all("/-- doc -/", &t);
        assert_eq!(toks[0], (TokenKind::Atom, "/--"));
    }

    #[test]
    fn unterminated_block_comment_is_an_error_not_a_hang() {
        let t = TokenTable::default();
        let (tok, err) = next_token("/- never closed", 0, &t);
        assert_eq!(tok.kind, TokenKind::BlockComment);
        assert_eq!(tok.len as usize, "/- never closed".len());
        assert_eq!(err.unwrap().code, "E0303");
    }

    #[test]
    fn unlexable_bytes_become_error_tokens_and_progress() {
        // No table entries: a stray symbol byte can't match anything.
        let t = TokenTable::default();
        let toks = lex_all("⊕", &t);
        assert_eq!(toks[0].0, TokenKind::ErrorTok);
    }
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_syntax lex::`
Expected: compile error — `TokenTable` etc. undefined.

- [ ] **Step 3: Implement `lex.rs` (trivia + munch skeleton)**

```rust
//! Table-driven tokenizer (spec §Architecture / lex). Lean has NO static
//! token set: `notation` commands add tokens, and tokenization is
//! maximal-munch against the CURRENT token table — so `next_token` is a
//! pure function of (source, position, table), called per-token as the
//! parser advances. ORACLE-PORT: Lean/Parser/Basic.lean (`whitespace`,
//! `finishCommentBlock`, token munch). Totality: on ANY byte sequence
//! the lexer returns a token with len ≥ 1 (except Eof) and never panics.

use std::collections::BTreeSet;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TokenKind {
    Whitespace,
    LineComment,
    BlockComment,
    /// Keyword or symbol from the token table.
    Atom,
    Ident,
    /// Natural-number literal (incl. 0x/0b/0o).
    Num,
    /// Decimal/scientific literal (`2.5`, `1e-3`).
    Scientific,
    /// String literal, incl. raw `r"…"`/`r#"…"#` forms.
    Str,
    Char,
    /// Name literal: `` `foo `` / ``` ``foo ```.
    NameLit,
    /// Unlexable byte run — untrusted-input totality.
    ErrorTok,
    Eof,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub len: u32,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LexError {
    pub code: &'static str,
    pub msg: String,
}

/// The dynamic token set. `max_len` bounds the munch scan.
#[derive(Clone, Debug, Default)]
pub struct TokenTable {
    toks: BTreeSet<String>,
    max_len: usize,
}

impl TokenTable {
    pub fn insert(&mut self, tok: &str) {
        self.max_len = self.max_len.max(tok.len());
        self.toks.insert(tok.to_string());
    }

    pub fn contains(&self, tok: &str) -> bool {
        self.toks.contains(tok)
    }

    pub fn iter(&self) -> impl Iterator<Item = &str> {
        self.toks.iter().map(|s| s.as_str())
    }

    /// Longest table entry that prefixes `rest` (maximal munch).
    pub fn munch<'a>(&self, rest: &'a str) -> Option<&'a str> {
        let mut best = None;
        for (i, c) in rest.char_indices() {
            let end = i + c.len_utf8();
            if end > self.max_len {
                break;
            }
            if self.toks.contains(&rest[..end]) {
                best = Some(&rest[..end]);
            }
        }
        best
    }
}

fn tok(kind: TokenKind, len: usize) -> (Token, Option<LexError>) {
    (Token { kind, len: len as u32 }, None)
}

/// Lex one token at `pos`. Trivia (whitespace/comments) are returned as
/// ordinary tokens; the parser loops. Returns Eof (len 0) at end.
pub fn next_token(src: &str, pos: usize, table: &TokenTable) -> (Token, Option<LexError>) {
    let rest = &src[pos..];
    let mut chars = rest.chars();
    let Some(c) = chars.next() else {
        return tok(TokenKind::Eof, 0);
    };

    // --- trivia ---------------------------------------------------
    if c.is_whitespace() {
        let end = rest
            .char_indices()
            .find(|&(_, c)| !c.is_whitespace())
            .map(|(i, _)| i)
            .unwrap_or(rest.len());
        return tok(TokenKind::Whitespace, end);
    }
    if rest.starts_with("--") {
        // ORACLE-PORT Basic.lean whitespace: `--` runs to end of line.
        // The newline is included in the trivia token (leading-trivia
        // attachment is ours; byte-losslessness is what matters).
        let end = rest.find('\n').map(|i| i + 1).unwrap_or(rest.len());
        return tok(TokenKind::LineComment, end);
    }
    if rest.starts_with("/-") && !rest.starts_with("/--") && !rest.starts_with("/-!") {
        // Nested block comment. `/--`/`/-!` open DOC comments — tokens,
        // not trivia (they reach the munch below via the table).
        return match block_comment_end(rest) {
            Some(end) => tok(TokenKind::BlockComment, end),
            None => (
                Token { kind: TokenKind::BlockComment, len: rest.len() as u32 },
                Some(LexError {
                    code: "E0303",
                    msg: "unterminated block comment".to_string(),
                }),
            ),
        };
    }

    // --- table munch (symbols, keywords-as-symbols) ----------------
    // Idents/literals are handled in Task 3; munch result competes with
    // them by length there. For now: munch, else single-char ErrorTok.
    if let Some(m) = table.munch(rest) {
        return tok(TokenKind::Atom, m.len());
    }
    tok(TokenKind::ErrorTok, c.len_utf8())
}

/// Byte offset just past the matching `-/`, honoring nesting.
fn block_comment_end(rest: &str) -> Option<usize> {
    debug_assert!(rest.starts_with("/-"));
    let bytes = rest.as_bytes();
    let mut depth = 1usize;
    let mut i = 2;
    while i < bytes.len() {
        if bytes[i..].starts_with(b"/-") {
            depth += 1;
            i += 2;
        } else if bytes[i..].starts_with(b"-/") {
            depth -= 1;
            i += 2;
            if depth == 0 {
                return Some(i);
            }
        } else {
            // Advance one UTF-8 char (never split a code point).
            i += 1;
            while i < bytes.len() && (bytes[i] & 0xC0) == 0x80 {
                i += 1;
            }
        }
    }
    None
}
```

- [ ] **Step 4: Run the tests**

Run: `cargo test -p leanr_syntax lex::`
Expected: all 6 pass.

- [ ] **Step 5: Verify the trivia port against the oracle source**

Read `$(lean --print-prefix)/src/lean/Lean/Parser/Basic.lean` — the `whitespace` function. Confirm: (a) `--` line comments; (b) `/-` blocks nest and exclude `/--`/`/-!`; (c) which whitespace chars Lean accepts (if Lean rejects e.g. tabs or `\r` outside `\r\n`, mirror it — adjust the whitespace arm and add a unit test for the rejected char producing the same behavior). Record any adjustment in the commit message.

- [ ] **Step 6: Commit**

```bash
mise run fmt
git add -A
git commit -m "feat(syntax): table-driven trivia lexer — maximal munch, nested block comments (M3a Task 2)"
```

---

### Task 3: Identifier + literal lexing

**Files:**
- Modify: `crates/leanr_syntax/src/lex.rs`

**Interfaces:**
- Produces: `next_token` now yields `Ident`, `Num`, `Scientific`, `Str`, `Char`, `NameLit`; plus `lex::{is_id_first, is_id_rest}` (used by Task 5's ident primitives and Task 10's `docComment`).
- Consumes: Task 2's `TokenTable`/`next_token` skeleton.

**Oracle:** character classes in `$(lean --print-prefix)/src/lean/Init/Meta/Defs.lean` (lines ~101–142: `isLetterLike`, `isSubScriptAlnum`, `isIdFirst`, `isIdRest`, `idBeginEscape '«'`, `idEndEscape '»'`); token functions in `Lean/Parser/Basic.lean` (`identFn`, hierarchical `.` continuation, `numberFn` for 0x/0b/0o/decimal/scientific, `strLitFn` incl. string gaps, `charLitFn`, raw strings, name literals). ORACLE-PORT throughout.

- [ ] **Step 1: Write the failing tests** — append to `lex.rs` tests:

```rust
    fn kw_table() -> TokenTable {
        let mut t = TokenTable::default();
        for k in ["def", ":=", ".", "=>", "fun"] {
            t.insert(k);
        }
        t
    }

    #[test]
    fn ident_shaped_keywords_lex_as_atoms_longer_idents_win() {
        let t = kw_table();
        assert_eq!(lex_all("def", &t)[0], (TokenKind::Atom, "def"));
        // "define" is LONGER than table entry "def": ident wins.
        assert_eq!(lex_all("define", &t)[0], (TokenKind::Ident, "define"));
    }

    #[test]
    fn hierarchical_idents_are_one_token() {
        let t = kw_table();
        assert_eq!(lex_all("Foo.bar.baz", &t)[0], (TokenKind::Ident, "Foo.bar.baz"));
        // Trailing '.' NOT followed by an ident part stays a separate token.
        assert_eq!(
            lex_all("foo.", &t),
            vec![(TokenKind::Ident, "foo"), (TokenKind::Atom, ".")]
        );
    }

    #[test]
    fn french_quote_escapes_and_letterlike() {
        let t = kw_table();
        assert_eq!(lex_all("«weird id».x", &t)[0], (TokenKind::Ident, "«weird id».x"));
        assert_eq!(lex_all("α₁'", &t)[0], (TokenKind::Ident, "α₁'"));
        let (tok, err) = next_token("«never closed", 0, &t);
        assert_eq!(tok.kind, TokenKind::ErrorTok);
        assert_eq!(err.unwrap().code, "E0306");
    }

    #[test]
    fn number_literals() {
        let t = kw_table();
        assert_eq!(lex_all("0x1F", &t)[0], (TokenKind::Num, "0x1F"));
        assert_eq!(lex_all("0b101", &t)[0], (TokenKind::Num, "0b101"));
        assert_eq!(lex_all("0o77", &t)[0], (TokenKind::Num, "0o77"));
        assert_eq!(lex_all("42", &t)[0], (TokenKind::Num, "42"));
        assert_eq!(lex_all("2.5", &t)[0], (TokenKind::Scientific, "2.5"));
        assert_eq!(lex_all("1e-3", &t)[0], (TokenKind::Scientific, "1e-3"));
        // '.' not followed by a digit is NOT consumed by the number:
        // `1.foo` = Num, ".", Ident (field access on a literal).
        assert_eq!(
            lex_all("1.foo", &t),
            vec![(TokenKind::Num, "1"), (TokenKind::Atom, "."), (TokenKind::Ident, "foo")]
        );
    }

    #[test]
    fn string_char_and_name_literals() {
        let t = kw_table();
        assert_eq!(
            lex_all("\"a\\n\\\"b\"", &t)[0],
            (TokenKind::Str, "\"a\\n\\\"b\"")
        );
        assert_eq!(lex_all("'\\n'", &t)[0], (TokenKind::Char, "'\\n'"));
        assert_eq!(lex_all("'a'", &t)[0], (TokenKind::Char, "'a'"));
        assert_eq!(lex_all("`foo.bar", &t)[0], (TokenKind::NameLit, "`foo.bar"));
        let (tok, err) = next_token("\"never closed", 0, &t);
        assert_eq!(tok.kind, TokenKind::Str);
        assert_eq!(err.unwrap().code, "E0302");
    }

    #[test]
    fn raw_strings() {
        let t = kw_table();
        assert_eq!(
            lex_all("r\"no \\escapes\"", &t)[0],
            (TokenKind::Str, "r\"no \\escapes\"")
        );
        assert_eq!(
            lex_all("r#\"has \" quote\"#", &t)[0],
            (TokenKind::Str, "r#\"has \" quote\"#")
        );
    }

    #[test]
    fn char_lit_does_not_eat_apostrophe_idents() {
        let t = kw_table();
        // `f'` is an ident (apostrophe in isIdRest) — the ' after an
        // ident char is ident continuation, not a char literal opener.
        assert_eq!(lex_all("f' x", &t)[0], (TokenKind::Ident, "f'"));
    }
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_syntax lex::`
Expected: new tests fail (idents currently lex as ErrorTok).

- [ ] **Step 3: Implement — character classes first** (top of `lex.rs`, below the imports):

```rust
/// ORACLE-PORT Init/Meta/Defs.lean:101 (v4.32.0-rc1) — verbatim ranges.
pub fn is_letter_like(c: char) -> bool {
    let v = c as u32;
    (0x3b1..=0x3c9).contains(&v) && v != 0x3bb                    // lower Greek, not λ
        || (0x391..=0x3A9).contains(&v) && v != 0x3A0 && v != 0x3A3 // upper Greek, not Π Σ
        || (0x3ca..=0x3fb).contains(&v)                            // Coptic
        || (0x1f00..=0x1ffe).contains(&v)                          // polytonic Greek
        || (0x2100..=0x214f).contains(&v)                          // letterlike block
        || (0x1d49c..=0x1d59f).contains(&v)                        // script/fraktur/double-struck
        || (0x00c0..=0x00ff).contains(&v) && v != 0x00d7 && v != 0x00f7 // Latin-1, not × ÷
        || (0x0100..=0x017f).contains(&v) // Latin Extended-A
}

/// ORACLE-PORT Init/Meta/Defs.lean:114.
fn is_subscript_alnum(c: char) -> bool {
    let v = c as u32;
    (0x2080..=0x2089).contains(&v)      // isNumericSubscript ₀-₉
        || (0x2090..=0x209c).contains(&v)
        || (0x1d62..=0x1d6a).contains(&v)
        || v == 0x2c7c
}

/// ORACLE-PORT Init/Meta/Defs.lean:120.
pub fn is_id_first(c: char) -> bool {
    c.is_ascii_alphabetic() || c.is_alphabetic() || c == '_' || is_letter_like(c)
}

/// ORACLE-PORT Init/Meta/Defs.lean:133 — note `!` and `?` ARE idRest in
/// this pin. If `identFn` in Basic.lean uses a different predicate than
/// `Lean.isIdRest`, port THAT one (check at execution; the
/// `ident_shaped_keywords` fixture in Task 7 settles it empirically).
pub fn is_id_rest(c: char) -> bool {
    c.is_alphanumeric()
        || c == '_'
        || c == '\''
        || c == '!'
        || c == '?'
        || is_letter_like(c)
        || is_subscript_alnum(c)
}
```

(Note: Lean's `Char.isAlpha` is ASCII-only; `c.is_alphabetic()` above is broader. Check `identFn`'s actual first-char predicate — if it is ASCII-`isAlpha` + `isLetterLike` only, drop the `c.is_alphabetic()` clause. ORACLE-PORT.)

- [ ] **Step 4: Implement — extend `next_token`**. Replace the "table munch" tail of `next_token` with the full dispatch. The competition rule (ORACLE-PORT `tokenFnAux`): idents/literals are lexed by shape; a completed *atomic* ident whose text is exactly a table entry lexes as `Atom`; when both a symbol munch and an ident/literal match, the LONGER match wins (equal length → the ident/keyword path).

```rust
    // --- idents & literals ------------------------------------------
    let munched = table.munch(rest).map(str::len).unwrap_or(0);

    if is_id_first(c) || c == '«' {
        // Raw string `r"…"` / `r#"…"#` — 'r' is idFirst, so probe first.
        if c == 'r' {
            if let Some(len) = raw_string_len(rest) {
                return finish_or_err(rest, len, TokenKind::Str);
            }
        }
        match ident_len(rest) {
            Ok(len) => {
                // Munch competition (ORACLE-PORT tokenFnAux): the longer
                // of (symbol munch, ident) wins; on a tie the ident text
                // being a table entry makes it a keyword Atom.
                if munched > len {
                    return tok(TokenKind::Atom, munched);
                }
                if table.contains(&rest[..len]) {
                    return tok(TokenKind::Atom, len); // ident-shaped keyword
                }
                return tok(TokenKind::Ident, len);
            }
            Err(e) => return (Token { kind: TokenKind::ErrorTok, len: e.0 as u32 }, Some(e.1)),
        }
    }
    if c.is_ascii_digit() && munched == 0 {
        let (len, kind) = number_len(rest);
        return tok(kind, len);
    }
    if c == '"' {
        return match string_lit_len(rest) {
            Ok(len) => tok(TokenKind::Str, len),
            Err(e) => (Token { kind: TokenKind::Str, len: e.0 as u32 }, Some(e.1)),
        };
    }
    if c == '\'' {
        if let Some(len) = char_lit_len(rest) {
            return tok(TokenKind::Char, len);
        }
        // fall through: bare ' may be a table symbol
    }
    if c == '`' {
        if let Some(len) = name_lit_len(rest) {
            return tok(TokenKind::NameLit, len);
        }
    }
    if munched > 0 {
        return tok(TokenKind::Atom, munched);
    }
    tok(TokenKind::ErrorTok, c.len_utf8())
```

Then the helper functions (complete implementations):

```rust
type LexFail = (usize, LexError);

/// Length of a hierarchical identifier at the start of `rest`:
/// part ('.' part)* where part = idFirst idRest* | «…» . The dot
/// continues ONLY if followed by another part start. ORACLE-PORT
/// Basic.lean identFn/identFnAux.
fn ident_len(rest: &str) -> Result<usize, LexFail> {
    let mut i = 0;
    loop {
        i += ident_part_len(&rest[i..], i)?;
        let after = &rest[i..];
        let mut it = after.chars();
        if it.next() == Some('.') {
            if let Some(c2) = it.next() {
                if is_id_first(c2) || c2 == '«' {
                    i += 1; // consume '.' and loop for the next part
                    continue;
                }
            }
        }
        return Ok(i);
    }
}

fn ident_part_len(rest: &str, base: usize) -> Result<usize, LexFail> {
    let mut chars = rest.char_indices();
    let (_, c) = chars.next().expect("caller checked non-empty");
    if c == '«' {
        // Escaped part: everything to the matching '»' (no nesting).
        for (i, c2) in chars {
            if c2 == '»' {
                return Ok(i + '»'.len_utf8());
            }
        }
        return Err((
            base + rest.len(),
            LexError { code: "E0306", msg: "unterminated «identifier escape".into() },
        ));
    }
    debug_assert!(is_id_first(c));
    let end = rest
        .char_indices()
        .skip(1)
        .find(|&(_, c)| !is_id_rest(c))
        .map(|(i, _)| i)
        .unwrap_or(rest.len());
    Ok(end)
}

/// ORACLE-PORT Basic.lean numberFn: 0x/0X hex, 0b/0B bin, 0o/0O octal,
/// else decimal; decimal may continue `.digits` and/or `[eE][+-]?digits`
/// → Scientific. A '.' NOT followed by a digit is not consumed.
fn number_len(rest: &str) -> (usize, TokenKind) {
    let b = rest.as_bytes();
    let radix_digits: fn(&u8) -> bool = if b.len() > 1 && b[0] == b'0' {
        match b[1] {
            b'x' | b'X' => |c: &u8| c.is_ascii_hexdigit(),
            b'b' | b'B' => |c: &u8| *c == b'0' || *c == b'1',
            b'o' | b'O' => |c: &u8| (b'0'..=b'7').contains(c),
            _ => |c: &u8| c.is_ascii_digit(),
        }
    } else {
        |c: &u8| c.is_ascii_digit()
    };
    if b.len() > 1 && b[0] == b'0' && matches!(b[1], b'x' | b'X' | b'b' | b'B' | b'o' | b'O') {
        let mut i = 2;
        while i < b.len() && radix_digits(&b[i]) {
            i += 1;
        }
        return (i, TokenKind::Num);
    }
    let mut i = 0;
    while i < b.len() && b[i].is_ascii_digit() {
        i += 1;
    }
    let mut scientific = false;
    if i + 1 < b.len() && b[i] == b'.' && b[i + 1].is_ascii_digit() {
        scientific = true;
        i += 1;
        while i < b.len() && b[i].is_ascii_digit() {
            i += 1;
        }
    }
    if i < b.len() && (b[i] == b'e' || b[i] == b'E') {
        let mut j = i + 1;
        if j < b.len() && (b[j] == b'+' || b[j] == b'-') {
            j += 1;
        }
        if j < b.len() && b[j].is_ascii_digit() {
            scientific = true;
            i = j;
            while i < b.len() && b[i].is_ascii_digit() {
                i += 1;
            }
        }
    }
    (i, if scientific { TokenKind::Scientific } else { TokenKind::Num })
}

/// ORACLE-PORT Basic.lean quotedCharCoreFn/strLitFn: escapes
/// \\ \" \' \n \t \xHH \uHHHH, plus STRING GAPS (backslash-newline
/// consumes the newline and following leading whitespace).
fn string_lit_len(rest: &str) -> Result<usize, LexFail> {
    debug_assert!(rest.starts_with('"'));
    let mut it = rest.char_indices().skip(1).peekable();
    while let Some((i, c)) = it.next() {
        match c {
            '"' => return Ok(i + 1),
            '\\' => match it.next() {
                Some((_, '\n')) => {
                    // string gap: skip following spaces (not newlines)
                    while matches!(it.peek(), Some((_, ' ')) | Some((_, '\t'))) {
                        it.next();
                    }
                }
                Some((j, e)) if !valid_escape_head(e) => {
                    return Err((
                        j + e.len_utf8(),
                        LexError { code: "E0304", msg: format!("invalid escape '\\{e}'") },
                    ));
                }
                Some(_) => {}
                None => break,
            },
            _ => {}
        }
    }
    Err((
        rest.len(),
        LexError { code: "E0302", msg: "unterminated string literal".into() },
    ))
}

fn valid_escape_head(c: char) -> bool {
    matches!(c, '\\' | '"' | '\'' | 'n' | 't' | 'r' | 'x' | 'u')
    // \xHH / \uHHHH hex-digit VALIDATION is deferred to elaboration in
    // Lean too — the token ends at the closing quote either way.
}

/// `r"…"` / `r#…#"…"#…#` — no escapes; N hashes close with `"` + N `#`s.
fn raw_string_len(rest: &str) -> Option<usize> {
    debug_assert!(rest.starts_with('r'));
    let b = rest.as_bytes();
    let mut hashes = 0;
    let mut i = 1;
    while i < b.len() && b[i] == b'#' {
        hashes += 1;
        i += 1;
    }
    if i >= b.len() || b[i] != b'"' {
        return None; // plain ident starting with r
    }
    i += 1;
    while i < b.len() {
        if b[i] == b'"' && b[i + 1..].len() >= hashes
            && b[i + 1..i + 1 + hashes].iter().all(|&c| c == b'#')
        {
            return Some(i + 1 + hashes);
        }
        i += 1;
        while i < b.len() && (b[i] & 0xC0) == 0x80 {
            i += 1;
        }
    }
    None // unterminated: caller falls through to ident path? No — treat
         // as unterminated string: return None and the ident path lexes
         // `r` alone; the oracle fixture decides if this needs E0302.
}

/// `'c'` with the same escapes as strings. Returns None when this is
/// not a char literal (e.g. `'` after nothing sensible) so idents like
/// `f'` and a bare `'` table symbol still work.
fn char_lit_len(rest: &str) -> Option<usize> {
    let mut it = rest.char_indices().skip(1);
    let (_, c) = it.next()?;
    let close = if c == '\\' {
        let _ = it.next()?;
        it.next()
    } else {
        it.next()
    };
    match close {
        Some((i, '\'')) => Some(i + 1),
        _ => None,
    }
}

/// `` `foo.bar `` (single backtick + ident) and ``` ``ident ``` (double
/// backtick, macro-scope-free). ORACLE-PORT Basic.lean nameLitFn.
fn name_lit_len(rest: &str) -> Option<usize> {
    let after = rest.strip_prefix("``").or_else(|| rest.strip_prefix('`'))?;
    let prefix = rest.len() - after.len();
    let c = after.chars().next()?;
    if !(is_id_first(c) || c == '«') {
        return None;
    }
    ident_len(after).ok().map(|l| prefix + l)
}
```

**Note on `char_lit_does_not_eat_apostrophe_idents`:** the `'` handling above is only reached when `'` is the FIRST char of the token — after `f` the ident path has already consumed `f'`. The test pins this.

- [ ] **Step 5: Run the tests**

Run: `cargo test -p leanr_syntax lex::`
Expected: all pass (Task 2's included).

- [ ] **Step 6: Add a totality property test now (cheap insurance for Tasks 5–11)** — `crates/leanr_syntax/tests/lossless.rs`:

```rust
//! Untrusted-input totality (docs/THREAT_MODEL.md): the lexer terminates
//! with progress on every input, and token texts concatenate back to
//! the source byte-for-byte.

use leanr_syntax::lex::{next_token, TokenKind, TokenTable};
use proptest::prelude::*;

proptest! {
    #[test]
    fn lexer_is_total_and_lossless(src in ".*", extra_tok in "[:=+*<>-]{1,3}") {
        let mut table = TokenTable::default();
        for k in ["def", ":=", ".", "fun", "=>"] { table.insert(k); }
        table.insert(&extra_tok);
        let mut pos = 0;
        let mut rebuilt = String::new();
        loop {
            let (tok, _err) = next_token(&src, pos, &table);
            if tok.kind == TokenKind::Eof { break; }
            prop_assert!(tok.len > 0, "no progress at {pos}");
            rebuilt.push_str(&src[pos..pos + tok.len as usize]);
            pos += tok.len as usize;
        }
        prop_assert_eq!(rebuilt, src);
    }
}
```

Run: `cargo test -p leanr_syntax --test lossless`
Expected: pass. If proptest finds a panic/stall (e.g. a `char_indices` boundary bug), fix before proceeding — this property is the crate's totality contract.

- [ ] **Step 7: Commit**

```bash
mise run fmt
git add -A
git commit -m "feat(syntax): ident + literal lexing with oracle character classes; totality property (M3a Task 3)"
```

---

### Task 4: Enumerate the builtin-parser surface

**Files:**
- Create: `scripts/builtin-surface.sh`
- Create: `docs/superpowers/specs/2026-07-13-m3a-builtin-surface.md`

**Interfaces:**
- Produces: the authoritative table Tasks 7–10 port from, and the fixture-authoring constraint list (what may appear in M3a fixtures).
- Consumes: nothing (pure toolchain archaeology).

**Why this task exists:** Lean's grammar is extensible all the way down; only the *compiled* builtin parsers (`@[builtin_*_parser]` in the toolchain's `src/lean/Lean/Parser/`) exist without ParserDescr interpretation (M3b). Everything declared via `syntax`/`notation` in `src/lean/Init/` — including `+`, `=`, and almost every tactic — is OUT of M3a. Fixtures and ports must respect that line exactly; this task writes it down.

- [ ] **Step 1: Write the enumeration script** — `scripts/builtin-surface.sh`:

```bash
#!/usr/bin/env bash
# Enumerate the pinned toolchain's compiled builtin parsers — the M3a
# porting surface (spec §Architecture / builtin). Output: one line per
# attribute hit, "<category>\t<file>:<line>\t<decl>".
set -euo pipefail
P="$(lean --print-prefix)/src/lean/Lean/Parser"
grep -rnoE '@\[builtin_[a-z_]+_parser[^]]*\] *def [A-Za-z0-9_«»?!']+' "$P" \
  | sed -E 's/^([^:]+):([0-9]+):@\[(builtin_[a-z_]+_parser)[^]]*\] *def (.+)$/\3\t\1:\2\t\4/' \
  | sort
```

Run: `chmod +x scripts/builtin-surface.sh && scripts/builtin-surface.sh | head -30` — expect rows like `builtin_command_parser  …/Command.lean:NNN  declaration`. If the regex misses multi-line attribute forms, widen it (`grep -rn -B0 -A1`) until the counts match a manual spot-check of `Command.lean`.

- [ ] **Step 2: Write the surface document** — `docs/superpowers/specs/2026-07-13-m3a-builtin-surface.md`, structured as:

```markdown
# M3a builtin-parser surface (pinned v4.32.0-rc1)

Generated from `scripts/builtin-surface.sh` on <date>; hand-annotated.
The M3a rule: a construct may appear in fixtures iff every parser it
touches is on this list with status `port` (or is machinery like
`ident`/literals). `Init/`-declared syntax (ParserDescr) is M3b.

## command category (Lean/Parser/Command.lean, Module.lean)
| parser | kind name | source | M3a status |
|---|---|---|---|
| declaration | Lean.Parser.Command.declaration | Command.lean:NN | port |
| … every script row … | | | port / defer-M3b (reason) |

## term category (Term.lean) …
## level category (Level.lean) …
## tactic category (Tactic.lean) — expected tiny: unknown, nestedTactic, match, introMatch, seq forms
## do-element category (Do.lean) …
## deliberately deferred inside M3a
Parsers marked defer get a one-line reason (e.g. `quot` term quotations
— meaningless without antiquotation machinery, lands with M3b).

## fixture-authoring constraints (derived)
- No Init notation: no `+ - * = < >` operators, no `∘`, no `<|>` …
- No Init tactics: no `exact`, `intro`, `rfl`-as-tactic, `simp` …
- Numerals, strings, fun/∀/let/match/do/by, `def`…`instance` — OK.
```

Fill every row from the script output. For each parser decide: **port** (Tasks 7–10 must implement it) or **defer** with a reason and where it lands (typical defers: `quot`/antiquotation machinery → M3b; `deriving` handlers beyond the syntactic clause → parse-only is enough; obscure commands like `#exit` still port — they're trivial). The default is **port**: M3a's builtin snapshot should BE the builtin grammar, not a curated subset; defer only what is meaningless without M3b machinery.

- [ ] **Step 3: Commit**

```bash
git add scripts/builtin-surface.sh docs/superpowers/specs/2026-07-13-m3a-builtin-surface.md
git commit -m "docs(specs): enumerate the pinned toolchain's builtin-parser surface (M3a Task 4)"
```

---

### Task 5: `Prim` combinators + interpreter core

**Files:**
- Create (fill): `crates/leanr_syntax/src/grammar.rs` (the `Prim` enum + helpers; categories/snapshot arrive in Task 6)
- Create (fill): `crates/leanr_syntax/src/parse.rs` (interpreter state + combinator semantics)

**Interfaces:**
- Produces: `grammar::Prim` (all variants below), helper constructors `grammar::{node, seq, sym, opt, many, many1, sep_by1, or_else, atomic}`; `parse::{Ps, PResult, ParseError}` with `Ps::{new, run, peek_significant, finish_into_tree}` (crate-visible; the public API stays `parse_module`, Task 7).
- Consumes: Task 1 events/kinds, Tasks 2–3 lexer.

**Semantics contract (ORACLE-PORT `Lean/Parser/Basic.lean` combinator functions — each rule below names its oracle):**
- `Seq` (`andthenFn`): all in order; failure propagates.
- `OrElse` (`orelseFn`): try next alternative ONLY if the failed one consumed nothing; a consuming failure propagates.
- `Atomic` (`atomicFn`): on failure, reset position/events so an enclosing `OrElse` can try the next alternative.
- `Optional`/`Many`/`SepBy` (`optionalFn`/`manyFn`/`sepByFn`): wrap results in a `null` node; an inner failure that consumed nothing ends the loop cleanly; a consuming inner failure propagates.
- `Lookahead`/`NotFollowedBy`: run and always reset; never emit events.
- Failure records the FURTHEST failure position + expected-token set (`errorMsg` merging) — that's what diagnostics print.

- [ ] **Step 1: `grammar.rs` — the combinator data structure**

```rust
//! The parser as data (spec §Architecture / grammar): `Prim` is a
//! combinator tree the interpreter in `parse.rs` walks. Deliberately
//! ParserDescr-shaped: M3b maps `.olean`-decoded ParserDescr values
//! into this same enum, so builtin and user grammar run identically.
//! Builtin productions (builtin/*.rs) are Rust fns returning `Prim`.

use std::sync::Arc;

use crate::kind::SyntaxKind;

#[derive(Clone, Debug)]
pub enum Prim {
    /// Sequence; children parse in order into the current node.
    Seq(Vec<Prim>),
    /// `leading_parser`: open node `kind`; `prec` gates against the
    /// category's right-binding power (None = always).
    Node { kind: SyntaxKind, prec: Option<u32>, body: Arc<Prim> },
    /// `trailing_parser`: only legal as a category trailing entry.
    /// The already-parsed lhs becomes the node's first child (Pratt
    /// wrap); `lhs_prec` is the minimum lhs precedence.
    TrailingNode { kind: SyntaxKind, prec: u32, lhs_prec: u32, body: Arc<Prim> },
    /// Expect this exact atom token (must be in the snapshot's table).
    Symbol(String),
    /// Ident that is RESERVED in the table but allowed here (Lean
    /// `nonReservedSymbol`, e.g. contextual keywords).
    NonReservedSymbol(String),
    Ident,
    /// Literal leaves — each wraps its token in the Lean node kind:
    /// "num", "scientific", "str", "char", "name".
    NumLit,
    ScientificLit,
    StrLit,
    CharLit,
    NameLit,
    /// Raw digit run after `.` (projections `x.1`) — Lean `fieldIdx`.
    FieldIdx,
    /// Recurse into a category at the given right-binding power.
    Category { name: String, rbp: u32 },
    Optional(Arc<Prim>),
    Many(Arc<Prim>),
    Many1(Arc<Prim>),
    /// Items + separator atoms interleaved flat in one `null` node.
    SepBy { item: Arc<Prim>, sep: String, allow_trailing: bool },
    SepBy1 { item: Arc<Prim>, sep: String, allow_trailing: bool },
    OrElse(Vec<Prim>),
    Atomic(Arc<Prim>),
    Lookahead(Arc<Prim>),
    NotFollowedBy(Arc<Prim>),
    /// Group results into a "group" node (Lean `group`).
    Group(Arc<Prim>),
    // --- position/precedence checks (Task 6 implements semantics) ---
    WithPosition(Arc<Prim>),
    CheckColGt,
    CheckColGe,
    CheckColEq,
    CheckLineEq,
    CheckPrec(u32),
    CheckLhsPrec(u32),
    CheckWsBefore,
    CheckNoWsBefore,
    /// `many1Indent` / `sepByIndent` (do-blocks, tactic seqs) —
    /// Task 6 gives these their withPosition+colGe expansion.
    Many1Indent(Arc<Prim>),
    SepByIndentSemicolon(Arc<Prim>),
    /// Zero-width success producing a `Syntax.missing` leaf (used by
    /// error recovery and a few builtin productions).
    EmitMissing,
}

// Terse constructors — builtin/*.rs is written in these.
pub fn seq(ps: impl IntoIterator<Item = Prim>) -> Prim {
    Prim::Seq(ps.into_iter().collect())
}
pub fn sym(s: &str) -> Prim {
    Prim::Symbol(s.to_string())
}
pub fn opt(p: Prim) -> Prim {
    Prim::Optional(Arc::new(p))
}
pub fn many(p: Prim) -> Prim {
    Prim::Many(Arc::new(p))
}
pub fn many1(p: Prim) -> Prim {
    Prim::Many1(Arc::new(p))
}
pub fn sep_by1(item: Prim, sep: &str) -> Prim {
    Prim::SepBy1 { item: Arc::new(item), sep: sep.to_string(), allow_trailing: false }
}
pub fn or_else(ps: impl IntoIterator<Item = Prim>) -> Prim {
    Prim::OrElse(ps.into_iter().collect())
}
pub fn atomic(p: Prim) -> Prim {
    Prim::Atomic(Arc::new(p))
}
pub fn cat(name: &str, rbp: u32) -> Prim {
    Prim::Category { name: name.to_string(), rbp }
}
```

- [ ] **Step 2: Write the failing interpreter tests** — bottom of `parse.rs` (a toy grammar, no Lean semantics yet):

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use crate::grammar::*;
    use crate::kind::KindInterner;
    use crate::lex::TokenTable;
    use std::sync::Arc;

    /// Run `p` against `src` with tokens from `toks`; return
    /// (canon-ish sexpr of the tree, errors) for terse assertions.
    fn run_toy(src: &str, toks: &[&str], p: &Prim, kinds: &mut KindInterner) -> (String, usize) {
        let mut table = TokenTable::default();
        for t in toks {
            table.insert(t);
        }
        let root = kinds.intern("root");
        let mut ps = Ps::new_for_test(src, table, kinds);
        ps.start(root);
        let _ = ps.run(p);
        ps.finish();
        let (tree, errors) = ps.finish_into_tree_for_test();
        (sexpr(&tree), errors.len())
    }

    fn sexpr(tree: &crate::tree::SyntaxTree) -> String {
        fn go(n: &crate::tree::SyntaxNode, k: &KindInterner, out: &mut String) {
            out.push('(');
            out.push_str(k.name(n.kind()));
            for el in n.children_with_tokens() {
                match el {
                    rowan::NodeOrToken::Node(c) => {
                        out.push(' ');
                        go(&c, k, out);
                    }
                    rowan::NodeOrToken::Token(t) => {
                        use crate::kind::*;
                        if is_trivia(t.kind()) {
                            continue;
                        }
                        out.push(' ');
                        if t.kind() == KIND_IDENT {
                            out.push_str(t.text());
                        } else {
                            out.push('\'');
                            out.push_str(t.text());
                            out.push('\'');
                        }
                    }
                }
            }
            out.push(')');
        }
        let mut out = String::new();
        go(&tree.root(), &tree.kinds, &mut out);
        out
    }

    #[test]
    fn seq_and_symbols() {
        let mut k = KindInterner::new();
        let decl = k.intern("decl");
        let p = Prim::Node {
            kind: decl,
            prec: None,
            body: Arc::new(seq([sym("def"), Prim::Ident, sym(":="), Prim::NumLit])),
        };
        let (s, errs) = run_toy("def x := 42", &["def", ":="], &p, &mut k);
        assert_eq!(s, "(root (decl 'def' x ':=' (num '42')))");
        assert_eq!(errs, 0);
    }

    #[test]
    fn optional_and_many_wrap_in_null_nodes() {
        let mut k = KindInterner::new();
        let p = seq([opt(sym("@")), many(Prim::Ident)]);
        let (s, _) = run_toy("a b c", &["@"], &wrap_root(&mut k, p), &mut k);
        assert_eq!(s, "(root (r (null) (null a b c)))");
    }

    #[test]
    fn orelse_backtracks_only_without_consumption() {
        let mut k = KindInterner::new();
        // alt1 consumes "def" then fails on missing ":=" → consuming
        // failure → alt2 must NOT be tried.
        let p = or_else([seq([sym("def"), sym(":=")]), sym("def")]);
        let (_, errs) = run_toy("def x", &["def", ":="], &wrap_root(&mut k, p), &mut k);
        assert_eq!(errs, 1);
        // With atomic(alt1) the same input succeeds via alt2.
        let p = or_else([atomic(seq([sym("def"), sym(":=")])), sym("def")]);
        let (_, errs) = run_toy("def x", &["def", ":="], &wrap_root(&mut k, p), &mut k);
        assert_eq!(errs, 0);
    }

    #[test]
    fn sepby1_interleaves_flat() {
        let mut k = KindInterner::new();
        let p = sep_by1(Prim::Ident, ",");
        let (s, _) = run_toy("a, b, c", &[","], &wrap_root(&mut k, p), &mut k);
        assert_eq!(s, "(root (r (null a ',' b ',' c)))");
    }

    #[test]
    fn failure_reports_furthest_position_with_expected_set() {
        let mut k = KindInterner::new();
        let p = seq([sym("def"), Prim::Ident, sym(":=")]);
        let mut table = TokenTable::default();
        table.insert("def");
        table.insert(":=");
        let mut ps = Ps::new_for_test("def x +", table, &mut k);
        let root = k.intern("root"); // interned before Ps borrow in real code
        ps.start(root);
        let r = ps.run(&p);
        assert!(r.is_err());
        let (pos, expected) = ps.furthest_for_test();
        assert_eq!(pos, 6); // at the '+'
        assert!(expected.iter().any(|e| e == "':='"));
    }

    fn wrap_root(k: &mut KindInterner, body: Prim) -> Prim {
        let r = k.intern("r");
        Prim::Node { kind: r, prec: None, body: Arc::new(body) }
    }
}
```

(Adjust borrow order if `KindInterner` + `Ps` borrows fight — intern all kinds before constructing `Ps`. The test asserts BEHAVIOR; mechanical signature tweaks during implementation are fine as long as assertions survive.)

- [ ] **Step 3: Run to verify failure**

Run: `cargo test -p leanr_syntax parse::`
Expected: compile errors (`Ps` undefined).

- [ ] **Step 4: Implement `parse.rs` core**

```rust
//! The Prim interpreter (spec §Architecture / parse). One mutable state
//! (`Ps`) over the event list; speculation = truncate-to-savepoint;
//! Pratt trailing wrap = insert Start at the lhs event index (Task 6).
//! Failure carries no data — the state records the furthest failure
//! position + expected set for diagnostics (Lean errorMsg merging).

use std::sync::Arc;

use crate::grammar::{GrammarSnapshot, Prim};
use crate::kind::{
    is_trivia, KindInterner, SyntaxKind, KIND_ATOM, KIND_ERROR, KIND_IDENT,
    KIND_MISSING, KIND_NULL,
};
use crate::lex::{next_token, Token, TokenKind, TokenTable};
use crate::tree::{build_tree, Event, SyntaxTree};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ParseError {
    pub code: &'static str,
    /// Byte span the error points at.
    pub span: (u32, u32),
    pub msg: String,
}

/// Parse failure marker; all context lives in `Ps` (furthest/expected).
#[derive(Debug)]
pub struct Fail;
pub type PResult = Result<(), Fail>;

pub(crate) struct Ps<'a> {
    src: &'a str,
    pub(crate) pos: usize,
    table: &'a TokenTable,
    kinds: &'a KindInterner,
    events: Vec<Event>,
    pub(crate) errors: Vec<ParseError>,
    furthest_pos: usize,
    furthest_expected: Vec<String>,
    /// Current right-binding power (CheckPrec reads it; category sets it).
    prec: u32,
    /// Precedence of the last completed leading/trailing node.
    lhs_prec: u32,
    /// withPosition stack: saved (line, col) of a position marker.
    pos_stack: Vec<(u32, u32)>,
    /// Byte offset of each line start (for col computation).
    line_starts: Vec<usize>,
    /// Pending lex errors to surface as diagnostics once per token.
    // (attached when the offending token is consumed)
    _reserved: (),
}

pub(crate) struct Savepoint {
    pos: usize,
    events: usize,
    errors: usize,
    lhs_prec: u32,
}

impl<'a> Ps<'a> {
    pub(crate) fn new(
        src: &'a str,
        table: &'a TokenTable,
        kinds: &'a KindInterner,
    ) -> Self {
        let mut line_starts = vec![0];
        for (i, b) in src.bytes().enumerate() {
            if b == b'\n' {
                line_starts.push(i + 1);
            }
        }
        Ps {
            src,
            pos: 0,
            table,
            kinds,
            events: Vec::new(),
            errors: Vec::new(),
            furthest_pos: 0,
            furthest_expected: Vec::new(),
            prec: 0,
            lhs_prec: 0,
            pos_stack: Vec::new(),
            line_starts,
            _reserved: (),
        }
    }

    // ---- events ----------------------------------------------------
    pub(crate) fn start(&mut self, kind: SyntaxKind) {
        self.events.push(Event::Start(kind));
    }
    pub(crate) fn finish(&mut self) {
        self.events.push(Event::Finish);
    }
    pub(crate) fn save(&self) -> Savepoint {
        Savepoint {
            pos: self.pos,
            events: self.events.len(),
            errors: self.errors.len(),
            lhs_prec: self.lhs_prec,
        }
    }
    pub(crate) fn restore(&mut self, sp: &Savepoint) {
        self.pos = sp.pos;
        self.events.truncate(sp.events);
        self.errors.truncate(sp.errors);
        self.lhs_prec = sp.lhs_prec;
    }
    fn consumed_since(&self, sp: &Savepoint) -> bool {
        self.pos > sp.pos
    }

    // ---- tokens ----------------------------------------------------
    /// Emit trivia events up to the next significant token; return it
    /// (without consuming) plus its start offset.
    pub(crate) fn peek_significant(&mut self) -> (Token, usize) {
        loop {
            let (t, err) = next_token(self.src, self.pos, self.table);
            let trivia = matches!(
                t.kind,
                TokenKind::Whitespace | TokenKind::LineComment | TokenKind::BlockComment
            );
            if !trivia {
                return (t, self.pos);
            }
            if let Some(e) = err {
                self.errors.push(ParseError {
                    code: e.code,
                    span: (self.pos as u32, (self.pos + t.len as usize) as u32),
                    msg: e.msg,
                });
            }
            self.emit_token(trivia_kind(t.kind), t.len);
        }
    }

    fn emit_token(&mut self, kind: SyntaxKind, len: u32) {
        self.events.push(Event::Token { kind, offset: self.pos as u32, len });
        self.pos += len as usize;
    }

    /// Consume the peeked significant token as leaf `kind`.
    fn bump(&mut self, t: Token, kind: SyntaxKind) {
        if let (_, Some(e)) = next_token(self.src, self.pos, self.table) {
            self.errors.push(ParseError {
                code: e.code,
                span: (self.pos as u32, (self.pos + t.len as usize) as u32),
                msg: e.msg,
            });
        }
        self.emit_token(kind, t.len);
    }

    fn fail_expecting(&mut self, what: &str, at: usize) -> Fail {
        if at > self.furthest_pos {
            self.furthest_pos = at;
            self.furthest_expected.clear();
        }
        if at == self.furthest_pos {
            let w = what.to_string();
            if !self.furthest_expected.contains(&w) {
                self.furthest_expected.push(w);
            }
        }
        Fail
    }

    // ---- the interpreter --------------------------------------------
    pub(crate) fn run(&mut self, p: &Prim) -> PResult {
        match p {
            Prim::Seq(ps) => {
                for q in ps {
                    self.run(q)?;
                }
                Ok(())
            }
            Prim::Node { kind, prec, body } => {
                if let Some(np) = prec {
                    if *np < self.prec {
                        let at = self.pos;
                        return Err(self.fail_expecting("<prec>", at));
                    }
                }
                self.start(*kind);
                let r = self.run(body);
                self.finish();
                if r.is_ok() {
                    self.lhs_prec = prec.unwrap_or(0);
                }
                r
                // on Err the caller's restore() drops the dangling
                // Start/Finish pair with the rest of the events.
            }
            Prim::Symbol(s) => self.expect_atom(s, false),
            Prim::NonReservedSymbol(s) => self.expect_atom(s, true),
            Prim::Ident => {
                let (t, at) = self.peek_significant();
                if t.kind == TokenKind::Ident {
                    self.bump(t, KIND_IDENT);
                    Ok(())
                } else {
                    Err(self.fail_expecting("identifier", at))
                }
            }
            Prim::NumLit => self.lit(TokenKind::Num, "num"),
            Prim::ScientificLit => self.lit(TokenKind::Scientific, "scientific"),
            Prim::StrLit => self.lit(TokenKind::Str, "str"),
            Prim::CharLit => self.lit(TokenKind::Char, "char"),
            Prim::NameLit => self.lit(TokenKind::NameLit, "name"),
            Prim::FieldIdx => self.field_idx(),
            Prim::Optional(q) => {
                let sp = self.save();
                self.start(KIND_NULL);
                match self.run(q) {
                    Ok(()) => {
                        self.finish();
                        Ok(())
                    }
                    Err(f) if self.consumed_since(&sp) => Err(f),
                    Err(_) => {
                        self.restore(&sp);
                        self.start(KIND_NULL);
                        self.finish();
                        Ok(())
                    }
                }
            }
            Prim::Many(q) => self.many_impl(q, 0),
            Prim::Many1(q) => self.many_impl(q, 1),
            Prim::SepBy { item, sep, allow_trailing } => {
                self.sep_by_impl(item, sep, *allow_trailing, 0)
            }
            Prim::SepBy1 { item, sep, allow_trailing } => {
                self.sep_by_impl(item, sep, *allow_trailing, 1)
            }
            Prim::OrElse(alts) => {
                for alt in alts {
                    let sp = self.save();
                    match self.run(alt) {
                        Ok(()) => return Ok(()),
                        Err(f) if self.consumed_since(&sp) => return Err(f),
                        Err(_) => self.restore(&sp),
                    }
                }
                let at = self.pos;
                Err(self.fail_expecting("<alternative>", at))
            }
            Prim::Atomic(q) => {
                let sp = self.save();
                self.run(q).map_err(|f| {
                    self.restore(&sp);
                    f
                })
            }
            Prim::Lookahead(q) => {
                let sp = self.save();
                let r = self.run(q);
                self.restore(&sp);
                r
            }
            Prim::NotFollowedBy(q) => {
                let sp = self.save();
                let r = self.run(q);
                self.restore(&sp);
                match r {
                    Ok(()) => {
                        let at = self.pos;
                        Err(self.fail_expecting("<not-followed-by>", at))
                    }
                    Err(_) => Ok(()),
                }
            }
            Prim::Group(q) => {
                self.start(crate::kind::KIND_GROUP);
                let r = self.run(q);
                self.finish();
                r
            }
            Prim::EmitMissing => {
                self.events.push(Event::Missing);
                Ok(())
            }
            // Task 6 fills these:
            Prim::Category { .. }
            | Prim::WithPosition(_)
            | Prim::CheckColGt
            | Prim::CheckColGe
            | Prim::CheckColEq
            | Prim::CheckLineEq
            | Prim::CheckPrec(_)
            | Prim::CheckLhsPrec(_)
            | Prim::CheckWsBefore
            | Prim::CheckNoWsBefore
            | Prim::Many1Indent(_)
            | Prim::SepByIndentSemicolon(_)
            | Prim::TrailingNode { .. } => {
                unimplemented!("Task 6: {:?}", std::mem::discriminant(p))
            }
        }
    }

    fn expect_atom(&mut self, s: &str, allow_ident: bool) -> PResult {
        let (t, at) = self.peek_significant();
        let text = &self.src[at..at + t.len as usize];
        let ok = match t.kind {
            TokenKind::Atom => text == s,
            TokenKind::Ident if allow_ident => text == s,
            _ => false,
        };
        if ok {
            self.bump(t, KIND_ATOM);
            Ok(())
        } else {
            Err(self.fail_expecting(&format!("'{s}'"), at))
        }
    }

    fn lit(&mut self, want: TokenKind, kind_name: &str) -> PResult {
        let (t, at) = self.peek_significant();
        if t.kind == want {
            let kind = self
                .kinds
                .lookup(kind_name)
                .expect("literal kinds pre-interned by SnapshotBuilder");
            self.start(kind);
            self.bump(t, KIND_ATOM);
            self.finish();
            Ok(())
        } else {
            Err(self.fail_expecting(kind_name, at))
        }
    }

    fn field_idx(&mut self) -> PResult {
        // Raw digits immediately after '.': the LEXER would produce a
        // Num (or Scientific for `x.1.2`!) — so FieldIdx lexes directly:
        // digits only, then wraps in "fieldIdx". ORACLE-PORT fieldIdxFn.
        let at = self.pos;
        let digits = self.src[at..]
            .bytes()
            .take_while(|b| b.is_ascii_digit())
            .count();
        if digits == 0 {
            return Err(self.fail_expecting("field index", at));
        }
        let kind = self.kinds.lookup("fieldIdx").expect("pre-interned");
        self.start(kind);
        self.emit_token(KIND_ATOM, digits as u32);
        self.finish();
        Ok(())
    }

    fn many_impl(&mut self, q: &Prim, min: usize) -> PResult {
        self.start(KIND_NULL);
        let mut n = 0;
        loop {
            let sp = self.save();
            match self.run(q) {
                Ok(()) => {
                    // zero-width success would loop forever: stop.
                    if !self.consumed_since(&sp) {
                        break;
                    }
                    n += 1;
                }
                Err(f) if self.consumed_since(&sp) => return Err(f),
                Err(_) => {
                    self.restore(&sp);
                    break;
                }
            }
        }
        self.finish();
        if n < min {
            let at = self.pos;
            return Err(self.fail_expecting("<many1 item>", at));
        }
        Ok(())
    }

    fn sep_by_impl(
        &mut self,
        item: &Prim,
        sep: &str,
        allow_trailing: bool,
        min: usize,
    ) -> PResult {
        self.start(KIND_NULL);
        let mut n = 0;
        let mut after_sep = false;
        loop {
            let sp = self.save();
            match self.run(item) {
                Ok(()) => n += 1,
                Err(f) if self.consumed_since(&sp) => return Err(f),
                Err(f) => {
                    self.restore(&sp);
                    if after_sep && !allow_trailing {
                        // `a, ` with no trailing allowed: the consumed
                        // separator makes this a real failure.
                        return Err(f);
                    }
                    break;
                }
            }
            let sp = self.save();
            match self.expect_atom(sep, false) {
                Ok(()) => after_sep = true,
                Err(_) => {
                    self.restore(&sp);
                    break;
                }
            }
        }
        self.finish();
        if n < min {
            let at = self.pos;
            return Err(self.fail_expecting("<sepBy1 item>", at));
        }
        Ok(())
    }

    // ---- output -------------------------------------------------------
    pub(crate) fn into_parts(self) -> (Vec<Event>, Vec<ParseError>) {
        (self.events, self.errors)
    }
}

fn trivia_kind(k: TokenKind) -> SyntaxKind {
    match k {
        TokenKind::Whitespace => crate::kind::KIND_WHITESPACE,
        TokenKind::LineComment => crate::kind::KIND_LINE_COMMENT,
        TokenKind::BlockComment => crate::kind::KIND_BLOCK_COMMENT,
        _ => unreachable!("trivia_kind on non-trivia"),
    }
}
```

Add the small `new_for_test`/`finish_into_tree_for_test`/`furthest_for_test` shims the Step 2 tests use (`#[cfg(test)]` impl block; `finish_into_tree_for_test` interns nothing — it calls `build_tree` with a cloned `Arc<KindInterner>` built by the test).

**Literal-kind pre-interning:** `lit()` and `field_idx()` look kinds up by name. Until Task 6's `SnapshotBuilder` exists, the test shim interns `"num" "scientific" "str" "char" "name" "fieldIdx"` itself — note this in `new_for_test`.

- [ ] **Step 5: Run the tests**

Run: `cargo test -p leanr_syntax parse::`
Expected: all 5 toy-grammar tests pass. Also rerun `cargo test -p leanr_syntax` — Tasks 1–3 suites stay green.

- [ ] **Step 6: Commit**

```bash
mise run fmt
git add -A
git commit -m "feat(syntax): Prim combinators + interpreter core with Lean orelse/atomic semantics (M3a Task 5)"
```

---

### Task 6: Precedence, position combinators, Pratt categories, `GrammarSnapshot`

**Files:**
- Modify: `crates/leanr_syntax/src/grammar.rs` (categories, snapshot, builder, fingerprint, prec constants)
- Modify: `crates/leanr_syntax/src/parse.rs` (the Task-5 `unimplemented!` arms + category machinery)

**Interfaces:**
- Produces: `grammar::{MAX_PREC, ARG_PREC, LEAD_PREC, MIN_PREC, Category, GrammarSnapshot, SnapshotBuilder, FirstTok}`; helpers `grammar::{leading, trailing}`; `GrammarSnapshot::{fingerprint, kinds}` (returns `Arc<KindInterner>`); `parse` gains working `Category`/`TrailingNode`/position/prec arms. Consumed by Tasks 7–10 (all builtin grammar) and Task 13 (CLI).
- Consumes: Tasks 1–5.

**Oracle:** `Lean/Parser/Basic.lean` (`prattParser`, `leadingParser`, `trailingLoop`, `longestMatchFn`, `checkColGt`/`checkColGe`/`withPosition`), precedence constants in `src/lean/Init/Prelude.lean` (the `prec` macros: `max` = 1024, `arg` = 1023, `lead` = 1022, `min` = 10 — ORACLE-PORT: verify these four numbers in the pin before writing them down).

- [ ] **Step 1: Write the failing tests** — append to `parse.rs` tests:

```rust
    use crate::grammar::{leading, trailing, SnapshotBuilder, MAX_PREC};

    /// A miniature Pratt category: atoms `a`; prefix `- e` (prec 75);
    /// left-assoc `e + e` (prec 65); right-assoc `e ^ e` (prec 75).
    fn arith_snapshot() -> crate::grammar::GrammarSnapshot {
        let mut b = SnapshotBuilder::new();
        b.category("term");
        b.leading2("term", "lit", MAX_PREC, Prim::Ident);
        b.leading2("term", "neg", 75, seq([sym("-"), cat("term", 75)]));
        b.trailing2("term", "add", 65, 65, seq([sym("+"), cat("term", 66)]));
        b.trailing2("term", "pow", 75, 76, seq([sym("^"), cat("term", 75)]));
        b.finish()
    }

    #[test]
    fn pratt_precedence_and_associativity() {
        let snap = arith_snapshot();
        // Idents parse via the "lit" leading node, so leaves print as
        // (lit x). a + b + c → left assoc (rhs at 66):
        assert_eq!(
            parse_cat(&snap, "a + b + c"),
            "(add (add (lit a) '+' (lit b)) '+' (lit c))"
        );
        // a ^ b ^ c → right assoc (rhs at 75):
        assert_eq!(
            parse_cat(&snap, "a ^ b ^ c"),
            "(pow (lit a) '^' (pow (lit b) '^' (lit c)))"
        );
        // - a + b → prefix binds tighter:
        assert_eq!(
            parse_cat(&snap, "- a + b"),
            "(add (neg '-' (lit a)) '+' (lit b))"
        );
        // a + - b → the rhs of + parses the prefix:
        assert_eq!(
            parse_cat(&snap, "a + - b"),
            "(add (lit a) '+' (neg '-' (lit b)))"
        );
    }

    #[test]
    fn longest_match_picks_the_farthest_leading_parse() {
        let mut b = SnapshotBuilder::new();
        b.category("c");
        b.leading2("c", "short", MAX_PREC, sym("x"));
        b.leading2("c", "long", MAX_PREC, seq([sym("x"), sym("!")]));
        let snap = b.finish();
        assert_eq!(parse_cat(&snap, "x !"), "(long 'x' '!')");
        assert_eq!(parse_cat(&snap, "x"), "(short 'x')");
    }

    #[test]
    fn with_position_col_gt() {
        let mut b = SnapshotBuilder::new();
        b.category("c");
        // "block" = 'do' then many1 idents, each on a column > do's.
        b.leading2(
            "c",
            "block",
            MAX_PREC,
            Prim::WithPosition(Arc::new(seq([
                sym("do"),
                many1(seq([Prim::CheckColGt, Prim::Ident])),
            ]))),
        );
        let snap = b.finish();
        assert_eq!(parse_cat(&snap, "do a\n   b"), "(block 'do' (null a b))");
        // `b` at column 0 is OUTSIDE the block: many1 stops after `a`.
        assert_eq!(parse_cat(&snap, "do a\nb"), "(block 'do' (null a))");
    }

    #[test]
    fn snapshot_fingerprint_is_stable_and_grammar_sensitive() {
        let s1 = arith_snapshot();
        let s2 = arith_snapshot();
        assert_eq!(s1.fingerprint(), s2.fingerprint());
        let mut b = SnapshotBuilder::new();
        b.category("term");
        b.leading2("term", "lit", MAX_PREC, Prim::Ident);
        let s3 = b.finish();
        assert_ne!(s1.fingerprint(), s3.fingerprint());
    }
```

With a `parse_cat(snap, src) -> String` test helper: build `Ps` from the snapshot (table + interner), run `Prim::Category { name: "term"/"c", rbp: 0 }` wrapped in a root, sexpr the single child. (Same sexpr helper as Task 5; hoist it.)

- [ ] **Step 2: Run to verify failure** — `cargo test -p leanr_syntax` → new tests fail to compile (`SnapshotBuilder` missing).

- [ ] **Step 3: Implement `grammar.rs` additions**

```rust
// ORACLE-PORT src/lean/Init/Prelude.lean `prec` macros — verify in pin.
pub const MAX_PREC: u32 = 1024;
pub const ARG_PREC: u32 = 1023;
pub const LEAD_PREC: u32 = 1022;
pub const MIN_PREC: u32 = 10;

/// What token class can begin a Prim — the category dispatch index
/// (Lean's PrattParsingTables leading/trailing token maps).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum FirstTok {
    Sym(String),
    Ident,
    Num,
    Scientific,
    Str,
    Char,
    NameLit,
    /// Cannot be indexed (position checks, category recursion, …):
    /// tried on every dispatch, like Lean's non-indexed parser list.
    Any,
}

#[derive(Clone, Debug, Default)]
pub struct Category {
    /// (first-token → candidate indices) + the always-tried rest.
    pub leading: Vec<(FirstTok, usize)>,
    pub leading_parsers: Vec<Prim>,
    pub trailing: Vec<(FirstTok, usize)>,
    pub trailing_parsers: Vec<Prim>,
}

#[derive(Debug)]
pub struct GrammarSnapshot {
    pub(crate) tokens: crate::lex::TokenTable,
    pub(crate) categories: std::collections::HashMap<String, Category>,
    kinds: std::sync::Arc<crate::kind::KindInterner>,
}

impl GrammarSnapshot {
    pub fn kinds(&self) -> std::sync::Arc<crate::kind::KindInterner> {
        self.kinds.clone()
    }

    /// Stable hash of the whole grammar (spec: the query-ready
    /// parser-state firewall fingerprint). Tokens sorted (BTreeSet
    /// iteration), categories sorted by name, Prims encoded by a
    /// deterministic byte walk.
    pub fn fingerprint(&self) -> blake3::Hash {
        let mut h = blake3::Hasher::new();
        h.update(b"leanr-m3a-grammar-v1\0");
        for t in self.tokens.iter() {
            h.update(t.as_bytes());
            h.update(b"\0");
        }
        let mut names: Vec<_> = self.categories.keys().collect();
        names.sort();
        for name in names {
            h.update(name.as_bytes());
            h.update(b"\x01");
            let c = &self.categories[name];
            for p in c.leading_parsers.iter().chain(&c.trailing_parsers) {
                encode_prim(p, self, &mut h);
            }
        }
        h.finalize()
    }
}

/// Deterministic Prim encoding: tag byte + fields; kinds encoded by
/// NAME (interner ids are session-relative). Every variant handled —
/// adding a variant without extending this is a compile error (match
/// is exhaustive, no wildcard).
fn encode_prim(p: &Prim, snap: &GrammarSnapshot, h: &mut blake3::Hasher) {
    use Prim::*;
    match p {
        Seq(ps) => {
            h.update(&[0]);
            for q in ps {
                encode_prim(q, snap, h);
            }
            h.update(&[0xFF]);
        }
        Node { kind, prec, body } => {
            h.update(&[1]);
            h.update(snap.kinds.name(*kind).as_bytes());
            h.update(&prec.unwrap_or(u32::MAX).to_le_bytes());
            encode_prim(body, snap, h);
        }
        TrailingNode { kind, prec, lhs_prec, body } => {
            h.update(&[2]);
            h.update(snap.kinds.name(*kind).as_bytes());
            h.update(&prec.to_le_bytes());
            h.update(&lhs_prec.to_le_bytes());
            encode_prim(body, snap, h);
        }
        Symbol(s) => { h.update(&[3]); h.update(s.as_bytes()); h.update(b"\0"); }
        NonReservedSymbol(s) => { h.update(&[4]); h.update(s.as_bytes()); h.update(b"\0"); }
        Ident => h.update(&[5]).pipe_void(),
        NumLit => h.update(&[6]).pipe_void(),
        ScientificLit => h.update(&[7]).pipe_void(),
        StrLit => h.update(&[8]).pipe_void(),
        CharLit => h.update(&[9]).pipe_void(),
        NameLit => h.update(&[10]).pipe_void(),
        FieldIdx => h.update(&[11]).pipe_void(),
        Category { name, rbp } => {
            h.update(&[12]);
            h.update(name.as_bytes());
            h.update(&rbp.to_le_bytes());
        }
        Optional(q) => { h.update(&[13]); encode_prim(q, snap, h); }
        Many(q) => { h.update(&[14]); encode_prim(q, snap, h); }
        Many1(q) => { h.update(&[15]); encode_prim(q, snap, h); }
        SepBy { item, sep, allow_trailing } => {
            h.update(&[16, *allow_trailing as u8]);
            h.update(sep.as_bytes());
            h.update(b"\0");
            encode_prim(item, snap, h);
        }
        SepBy1 { item, sep, allow_trailing } => {
            h.update(&[17, *allow_trailing as u8]);
            h.update(sep.as_bytes());
            h.update(b"\0");
            encode_prim(item, snap, h);
        }
        OrElse(ps) => {
            h.update(&[18]);
            for q in ps {
                encode_prim(q, snap, h);
            }
            h.update(&[0xFF]);
        }
        Atomic(q) => { h.update(&[19]); encode_prim(q, snap, h); }
        Lookahead(q) => { h.update(&[20]); encode_prim(q, snap, h); }
        NotFollowedBy(q) => { h.update(&[21]); encode_prim(q, snap, h); }
        Group(q) => { h.update(&[22]); encode_prim(q, snap, h); }
        WithPosition(q) => { h.update(&[23]); encode_prim(q, snap, h); }
        CheckColGt => h.update(&[24]).pipe_void(),
        CheckColGe => h.update(&[25]).pipe_void(),
        CheckColEq => h.update(&[26]).pipe_void(),
        CheckLineEq => h.update(&[27]).pipe_void(),
        CheckPrec(n) => { h.update(&[28]); h.update(&n.to_le_bytes()); }
        CheckLhsPrec(n) => { h.update(&[29]); h.update(&n.to_le_bytes()); }
        CheckWsBefore => h.update(&[30]).pipe_void(),
        CheckNoWsBefore => h.update(&[31]).pipe_void(),
        Many1Indent(q) => { h.update(&[32]); encode_prim(q, snap, h); }
        SepByIndentSemicolon(q) => { h.update(&[33]); encode_prim(q, snap, h); }
        EmitMissing => h.update(&[34]).pipe_void(),
    }
}
// (`pipe_void` doesn't exist — just write `{ h.update(&[N]); }` blocks;
// shown compressed here for readability.)

pub struct SnapshotBuilder {
    kinds: crate::kind::KindInterner,
    tokens: crate::lex::TokenTable,
    categories: std::collections::HashMap<String, Category>,
}

impl SnapshotBuilder {
    pub fn new() -> Self {
        let mut kinds = crate::kind::KindInterner::new();
        // Literal node kinds the interpreter looks up by name.
        for k in ["num", "scientific", "str", "char", "name", "fieldIdx"] {
            kinds.intern(k);
        }
        SnapshotBuilder {
            kinds,
            tokens: Default::default(),
            categories: Default::default(),
        }
    }

    pub fn kind(&mut self, name: &str) -> crate::kind::SyntaxKind {
        self.kinds.intern(name)
    }

    pub fn token(&mut self, tok: &str) {
        self.tokens.insert(tok);
    }

    pub fn category(&mut self, name: &str) {
        self.categories.entry(name.to_string()).or_default();
    }

    /// Register a leading parser: interns `kind_name`, wraps `body` in
    /// `Prim::Node`, harvests its Symbols into the token table, indexes
    /// by FIRST token.
    pub fn leading2(&mut self, cat: &str, kind_name: &str, prec: u32, body: Prim) {
        let kind = self.kinds.intern(kind_name);
        let p = Prim::Node { kind, prec: Some(prec), body: std::sync::Arc::new(body) };
        self.harvest_tokens(&p);
        let c = self.categories.get_mut(cat).expect("category registered");
        let idx = c.leading_parsers.len();
        c.leading_parsers.push(p);
        let f = first_tok(&c.leading_parsers[idx]);
        c.leading.push((f, idx));
    }

    /// Register a trailing parser (Pratt loop continuation).
    pub fn trailing2(&mut self, cat: &str, kind_name: &str, prec: u32, lhs: u32, body: Prim) {
        let kind = self.kinds.intern(kind_name);
        let p = Prim::TrailingNode {
            kind,
            prec,
            lhs_prec: lhs,
            body: std::sync::Arc::new(body),
        };
        self.harvest_tokens(&p);
        let c = self.categories.get_mut(cat).expect("category registered");
        let idx = c.trailing_parsers.len();
        c.trailing_parsers.push(p);
        let f = first_tok(&c.trailing_parsers[idx]);
        c.trailing.push((f, idx));
    }

    fn harvest_tokens(&mut self, p: &Prim) {
        // Walk the Prim; every Symbol/NonReservedSymbol/SepBy separator
        // string goes into the token table (Lean: syntax registers its
        // atoms as tokens). ~25-line recursive match, all variants.
        walk_symbols(p, &mut |s| self.tokens.insert(s));
    }

    pub fn finish(self) -> GrammarSnapshot {
        GrammarSnapshot {
            tokens: self.tokens,
            categories: self.categories,
            kinds: std::sync::Arc::new(self.kinds),
        }
    }
}

/// FIRST-token of a Prim for dispatch indexing; `Any` when unknowable.
/// Skips CheckPrec/positions; looks through Node/Seq/Atomic heads.
fn first_tok(p: &Prim) -> FirstTok {
    use Prim::*;
    match p {
        Node { body, .. } | TrailingNode { body, .. } | Atomic(body)
        | Group(body) | WithPosition(body) => first_tok(body),
        Seq(ps) => ps
            .iter()
            .find(|q| !is_transparent_for_first(q))
            .map(first_tok)
            .unwrap_or(FirstTok::Any),
        Symbol(s) | NonReservedSymbol(s) => FirstTok::Sym(s.clone()),
        Ident => FirstTok::Ident,
        NumLit => FirstTok::Num,
        ScientificLit => FirstTok::Scientific,
        StrLit => FirstTok::Str,
        CharLit => FirstTok::Char,
        NameLit => FirstTok::NameLit,
        _ => FirstTok::Any,
    }
}

fn is_transparent_for_first(p: &Prim) -> bool {
    matches!(
        p,
        Prim::CheckPrec(_)
            | Prim::CheckLhsPrec(_)
            | Prim::CheckColGt
            | Prim::CheckColGe
            | Prim::CheckColEq
            | Prim::CheckLineEq
            | Prim::CheckWsBefore
            | Prim::CheckNoWsBefore
            | Prim::Lookahead(_)
            | Prim::NotFollowedBy(_)
    )
}

/// `leading`/`trailing` free-fn helpers used by builtin/*.rs (they just
/// delegate to the builder; kept so grammar files read like the oracle).
```

(Also write `walk_symbols` — the straightforward recursive visitor. And delete the stray `leading(&mut b_kinds…)` line from the Step-1 test sketch; the `leading2/trailing2` API is the real one. Rename `leading2/trailing2` → `leading/trailing` if no name clash bites — the plan uses `leading2/trailing2` below for unambiguity.)

- [ ] **Step 4: Implement the remaining `parse.rs` arms**

```rust
            Prim::CheckPrec(n) => {
                if self.prec <= *n {
                    Ok(())
                } else {
                    let at = self.pos;
                    Err(self.fail_expecting("<prec>", at))
                }
            }
            Prim::CheckLhsPrec(n) => {
                if self.lhs_prec >= *n {
                    Ok(())
                } else {
                    let at = self.pos;
                    Err(self.fail_expecting("<lhs-prec>", at))
                }
            }
            Prim::WithPosition(q) => {
                let (_, at) = self.peek_significant();
                let lc = self.line_col(at);
                self.pos_stack.push(lc);
                let r = self.run(q);
                self.pos_stack.pop();
                r
            }
            Prim::CheckColGt => self.check_col(|cur, saved| cur.1 > saved.1),
            Prim::CheckColGe => self.check_col(|cur, saved| cur.1 >= saved.1),
            Prim::CheckColEq => self.check_col(|cur, saved| cur.1 == saved.1),
            Prim::CheckLineEq => self.check_col(|cur, saved| cur.0 == saved.0),
            Prim::CheckWsBefore => {
                if self.had_ws_before_current() {
                    Ok(())
                } else {
                    let at = self.pos;
                    Err(self.fail_expecting("<whitespace>", at))
                }
            }
            Prim::CheckNoWsBefore => {
                if self.had_ws_before_current() {
                    let at = self.pos;
                    Err(self.fail_expecting("<no whitespace>", at))
                } else {
                    Ok(())
                }
            }
            Prim::Many1Indent(q) => {
                // ORACLE-PORT Basic.lean many1Indent: withPosition over
                // many1(checkColGe + p).
                let expanded = Prim::WithPosition(Arc::new(Prim::Many1(Arc::new(
                    Prim::Seq(vec![Prim::CheckColGe, (**q).clone()]),
                ))));
                self.run(&expanded)
            }
            Prim::SepByIndentSemicolon(q) => {
                // ORACLE-PORT Basic.lean sepByIndent: items at colEq of
                // the position marker, with optional ';' separators
                // (null node, separators interleaved when present).
                self.sep_by_indent(q)
            }
            Prim::Category { name, rbp } => self.category(name, *rbp),
            Prim::TrailingNode { .. } => {
                // Only the category trailing loop may run these (it owns
                // the lhs wrap). A TrailingNode anywhere else is a
                // grammar-construction bug.
                unreachable!("TrailingNode outside a category trailing loop")
            }
```

with the supporting methods on `Ps`:

```rust
    fn line_col(&self, at: usize) -> (u32, u32) {
        let line = self
            .line_starts
            .partition_point(|&s| s <= at)
            .saturating_sub(1);
        // Column = CHARACTER offset from line start (Lean uses codepoint
        // positions for columns — ORACLE-PORT FileMap; verify).
        let col = self.src[self.line_starts[line]..at].chars().count();
        (line as u32, col as u32)
    }

    fn check_col(&mut self, ok: impl Fn((u32, u32), (u32, u32)) -> bool) -> PResult {
        let (_, at) = self.peek_significant();
        let cur = self.line_col(at);
        let Some(&saved) = self.pos_stack.last() else {
            return Ok(()); // no marker: Lean treats as unconstrained
        };
        if ok(cur, saved) {
            Ok(())
        } else {
            Err(self.fail_expecting("<indentation>", at))
        }
    }

    fn had_ws_before_current(&mut self) -> bool {
        // True iff the last emitted event before the upcoming token is
        // trivia (or we're at pos 0 boundary of a node — matches Lean's
        // checkWsBefore "there is whitespace before" on the next token).
        let before = self.pos;
        let (_, at) = self.peek_significant();
        at > before || matches!(
            self.events.last(),
            Some(Event::Token { kind, .. }) if crate::kind::is_trivia(*kind)
        )
    }

    /// The Pratt driver. ORACLE-PORT prattParser/trailingLoop.
    fn category(&mut self, name: &str, rbp: u32) -> PResult {
        let Some(cat) = self.snap_category(name) else {
            let at = self.pos;
            return Err(self.fail_expecting(&format!("<category {name}>"), at));
        };
        let saved_prec = self.prec;
        self.prec = rbp;
        let r = (|| {
            // ---- leading: longest match over dispatched candidates --
            let lhs_events = self.events.len();
            let (t, at) = self.peek_significant();
            let candidates = dispatch(&cat, &self.src[at..at + t.len as usize], t.kind, true);
            let mut best: Option<(Savepoint /*end*/, Vec<Event>, u32)> = None;
            let sp = self.save();
            let mut best_end = 0usize;
            let mut best_events: Option<(Vec<Event>, usize, u32)> = None;
            for idx in candidates {
                let p = cat.leading_parsers[idx].clone();
                self.restore(&sp);
                if self.run(&p).is_ok() && self.pos > best_end {
                    best_end = self.pos;
                    best_events =
                        Some((self.events[sp.events..].to_vec(), self.pos, self.lhs_prec));
                }
            }
            let Some((events, end, lhs_prec)) = best_events else {
                self.restore(&sp);
                let at = self.pos;
                return Err(self.fail_expecting(&format!("<{name}>"), at));
            };
            self.restore(&sp);
            self.events.extend(events);
            self.pos = end;
            self.lhs_prec = lhs_prec;

            // ---- trailing loop --------------------------------------
            loop {
                let (t, at) = self.peek_significant();
                if t.kind == TokenKind::Eof {
                    break;
                }
                let text = &self.src[at..at + t.len as usize];
                let candidates = dispatch(&cat, text, t.kind, false);
                let sp = self.save();
                let mut advanced = false;
                for idx in candidates {
                    let Prim::TrailingNode { kind, prec, lhs_prec, body } =
                        cat.trailing_parsers[idx].clone()
                    else {
                        unreachable!("trailing entries are TrailingNode")
                    };
                    if prec < self.prec || self.lhs_prec < lhs_prec {
                        continue;
                    }
                    match self.run(&body) {
                        Ok(()) => {
                            // Wrap: insert Start at lhs, then Finish.
                            self.events.insert(lhs_events, Event::Start(kind));
                            self.events.push(Event::Finish);
                            self.lhs_prec = prec;
                            advanced = true;
                            break;
                        }
                        Err(_) => self.restore(&sp),
                    }
                }
                if !advanced {
                    break;
                }
            }
            Ok(())
        })();
        self.prec = saved_prec;
        r
    }
```

`snap_category`/`dispatch` are small helpers: `dispatch` collects candidate indices whose `FirstTok` matches (`Sym(text)` for Atom tokens by text, the literal classes by `TokenKind`, `Ident` for idents, plus every `Any` entry), preserving registration order. `Ps` needs a `snap: &'a GrammarSnapshot` field now — update `Ps::new` to take the snapshot and derive `table`/`kinds` from it (`new_for_test` keeps building a snapshot-less shim or constructs a tiny snapshot; pick whichever keeps Tasks 5's tests compiling with minimal churn — behavior must not change).

**Longest-match subtleties pinned by the tests:** candidates are ALL run from the same savepoint; the winner is the farthest `pos` (first registered wins ties — a tie in real Lean yields a `choice` node; M3a records first-wins as a known divergence, spec §risks, revisited in M3b — `grep 'choice'` in dumps will catch any fixture that hits one). Restore-then-replay of the winning event slice keeps the event list consistent without re-running the parse.

**Note on `trailing_parsers` prec gate:** Lean checks `prec ≥ rbp` (not `>`); the test `a + b + c` vs rhs-at-66 pins left-associativity — if it comes out right-associated, the comparison direction is wrong.

- [ ] **Step 5: Run the tests**

Run: `cargo test -p leanr_syntax`
Expected: all pass, including Task 5's (whose `unimplemented!` arms are now live) and the fingerprint stability test.

- [ ] **Step 6: Commit**

```bash
mise run fmt
git add -A
git commit -m "feat(syntax): Pratt categories, longest-match, position/prec combinators, GrammarSnapshot + fingerprint (M3a Task 6)"
```

---

### Task 7: Vertical slice — `parse_module`, module header, oracle dump script, first golden fixture

**Files:**
- Modify: `crates/leanr_syntax/src/parse.rs` (`parse_module`, `ParseResult`)
- Create (fill): `crates/leanr_syntax/src/builtin/mod.rs` (+ stub `command.rs` with the header + a micro command set)
- Create: `tests/fixtures/syntax/dump_syntax.lean`
- Create: `tests/fixtures/syntax/Micro.lean` + committed `Micro.stx.jsonl`
- Create: `crates/leanr_syntax/tests/oracle_golden.rs`
- Modify: `mise.toml` (`fixtures:regen` additions)

**Interfaces:**
- Produces: `parse::parse_module(src: &str, snap: &GrammarSnapshot) -> ParseResult` where `ParseResult { pub tree: SyntaxTree, pub errors: Vec<ParseError> }`; `builtin::snapshot() -> GrammarSnapshot` (grows through Tasks 8–10); the oracle harness every later fixture reuses.
- Consumes: everything before.

**This task is the load-bearing one:** it proves lex → parse → canon → oracle-diff end-to-end on a one-command file before Tasks 8–10 add grammar breadth. Expect iteration here — schema mismatches (JSON escaping, span conventions, eoi handling) all surface on this first diff, on a tiny file, where they're cheap.

- [ ] **Step 1: `parse_module` + recovery-free driver** (recovery hardening is Task 11; the shape lands now) — in `parse.rs`:

```rust
#[derive(Debug)]
pub struct ParseResult {
    pub tree: SyntaxTree,
    pub errors: Vec<ParseError>,
}

/// Parse one module: header, then commands to EOF. Never panics; a
/// command that fails to parse becomes a KIND_ERROR node and parsing
/// resumes at the next plausible command start (Task 11 hardens this).
pub fn parse_module(src: &str, snap: &GrammarSnapshot) -> ParseResult {
    let kinds = snap.kinds();
    let mut ps = Ps::new(src, snap);
    let module = kinds.lookup("module").expect("interned by builtin::snapshot");
    ps.start(module);

    // Header (always present; all-optional parts ⇒ cannot fail).
    let header = snap.header_prim();
    let _ = ps.run(&header);

    // Command loop.
    loop {
        let (t, _at) = ps.peek_significant();
        if t.kind == crate::lex::TokenKind::Eof {
            break;
        }
        let sp = ps.save();
        match ps.run(&Prim::Category { name: "command".into(), rbp: 0 }) {
            Ok(()) => {}
            Err(_) => {
                ps.restore(&sp);
                ps.recover_command();
            }
        }
    }
    // Trailing trivia + eoi node (mirrors Lean's Command.eoi so dumps
    // line up — VERIFY against the first regen: if the oracle dump has
    // no eoi line, drop ours instead).
    let eoi = kinds.lookup("Lean.Parser.Command.eoi").expect("interned");
    ps.start(eoi);
    ps.finish();

    ps.finish(); // module
    let (events, errors) = ps.into_parts();
    ParseResult { tree: build_tree(src, &events, kinds), errors }
}

impl<'a> Ps<'a> {
    /// Minimal recovery: emit an ERROR node, skip tokens until the next
    /// token that could START a command (per the command category's
    /// dispatch index) or EOF; always consume ≥ 1 token. Also surfaces
    /// the furthest-failure diagnostic (E0301).
    pub(crate) fn recover_command(&mut self) {
        let (pos, expected) = (self.furthest_pos, self.furthest_expected.clone());
        self.errors.push(ParseError {
            code: "E0301",
            span: (pos as u32, pos as u32),
            msg: format!("unexpected input; expected one of: {}", expected.join(", ")),
        });
        self.start(KIND_ERROR);
        let mut first = true;
        loop {
            let (t, at) = self.peek_significant();
            if t.kind == TokenKind::Eof {
                break;
            }
            let text = &self.src[at..at + t.len as usize];
            if !first && self.starts_command(text, t.kind) {
                break;
            }
            first = false;
            let kind = match t.kind {
                TokenKind::Ident => KIND_IDENT,
                _ => KIND_ATOM,
            };
            self.bump(t, kind);
        }
        self.finish();
    }
}
```

(`starts_command` = "the command category's leading dispatch has a `Sym(text)` entry, or an `Any`-indexed entry could apply" — conservatively: `Sym(text)` match only; `header_prim()` is a small accessor on `GrammarSnapshot` set by `builtin::snapshot()` — add `pub(crate) header: Option<Prim>` to the snapshot + builder.)

- [ ] **Step 2: the micro builtin grammar** — `builtin/mod.rs`:

```rust
//! The builtin grammar snapshot (spec §Architecture / builtin) —
//! Rust ports of the pinned toolchain's compiled `@[builtin_*_parser]`
//! set, per docs/superpowers/specs/2026-07-13-m3a-builtin-surface.md.
//! Kind names MUST match Lean's byte-for-byte (oracle equality).

pub mod command;
// Tasks 8–10 add: pub mod level; pub mod term; pub mod do_notation;
// pub mod tactic;

use crate::grammar::{GrammarSnapshot, SnapshotBuilder};

pub fn snapshot() -> GrammarSnapshot {
    let mut b = SnapshotBuilder::new();
    b.kind("module");
    b.kind("Lean.Parser.Command.eoi");
    b.category("command");
    b.category("term");
    b.category("level");
    b.category("tactic");
    command::register(&mut b);
    // Tasks 8–10: level::register(&mut b); term::register(&mut b); …
    b.finish()
}
```

`builtin/command.rs` (micro set — replaced/extended in Task 10; ORACLE-PORT `Lean/Parser/Module.lean` for the header shape — READ IT and mirror the optional module/prelude/import structure exactly, including the `Lean.Parser.Module.*` kind names):

```rust
use crate::grammar::*;
use crate::kind::SyntaxKind;
use std::sync::Arc;

/// `Prim::Node` with no prec gate — the sub-node shape every compound
/// production uses.
fn node_named(kind: SyntaxKind, body: Prim) -> Prim {
    Prim::Node { kind, prec: None, body: Arc::new(body) }
}

pub fn register(b: &mut SnapshotBuilder) {
    // --- module header (ORACLE-PORT Module.lean `header`) -----------
    // Shape in v4.32.0-rc1 (verify): optional "module" marker,
    // optional "prelude", many imports where import =
    //   optional "public" ++ optional "meta" ++ "import" ++ optional "all" ++ ident
    // Kind names: Lean.Parser.Module.header / .prelude / .import.
    let header_kind = b.kind("Lean.Parser.Module.header");
    let prelude_kind = b.kind("Lean.Parser.Module.prelude");
    let import_kind = b.kind("Lean.Parser.Module.import");
    b.set_header(node_named(
        header_kind,
        seq([
            opt(node_named(prelude_kind, sym("prelude"))),
            many(node_named(
                import_kind,
                seq([sym("import"), opt(sym("all")), Prim::Ident]),
            )),
        ]),
    ));
    // ^ If the pin's header includes the module-system markers
    // ("module", "public", "meta"), ADD them here per the source —
    // the Micro fixture regen will show the real shape immediately.

    // --- micro command set -------------------------------------------
    // Just enough for the vertical slice: `def x := <term>` — the real
    // declaration parser replaces this in Task 10 with the same kinds.
    let decl = b.kind("Lean.Parser.Command.declaration");
    let modifiers = b.kind("Lean.Parser.Command.declModifiers");
    let def_k = b.kind("Lean.Parser.Command.definition");
    let decl_id = b.kind("Lean.Parser.Command.declId");
    let decl_sig = b.kind("Lean.Parser.Command.optDeclSig");
    let decl_val = b.kind("Lean.Parser.Command.declValSimple");
    b.leading2(
        "command",
        "Lean.Parser.Command.declaration",
        MAX_PREC,
        seq([
            empty_modifiers(modifiers),
            node_named(
                def_k,
                seq([
                    sym("def"),
                    node_named(decl_id, seq([Prim::Ident, opt_universe_binders()])),
                    empty_opt_sig(decl_sig),
                    node_named(decl_val, seq([sym(":="), cat("term", 0)])),
                ]),
            ),
        ]),
    );
    // term category micro set: just idents + num literals for now.
    b.leading2("term", "<term-ident>", MAX_PREC, Prim::Ident);
    // NOTE: "<term-ident>" is WRONG for the oracle (bare idents are
    // Syntax.ident leaves, not nodes). Fix while diffing Micro.lean:
    // a leading entry whose Prim is bare `Prim::Ident` (no Node wrap)
    // — extend `leading2` with a `leading_raw` variant that skips the
    // Node wrapper. The first golden diff makes this concrete.
    b.leading2("term", "num", MAX_PREC, Prim::NumLit);
}
```

The exact helper names (`node_named`, `empty_modifiers`, `opt_universe_binders`, `empty_opt_sig`, `set_header`, `leading_raw`) don't pre-exist — write them in this task; they're one-to-five-liners. What the oracle REALLY emits for `declModifiers`/`optDeclSig` on a bare `def` (empty null children in specific arities) comes out of the first regen diff; adjust the micro grammar until the Micro fixture matches EXACTLY, and keep those learnings as comments — Task 10 reuses them.

- [ ] **Step 3: the oracle dump script** — `tests/fixtures/syntax/dump_syntax.lean`:

```lean
/-
Oracle parse-tree dump (M3a spec §Oracle harness). Parse-only frontend
loop: header via parseHeader/processHeader (so imported grammar IS
honored — M3b's full-Mathlib sweep reuses this), then parseCommand in a
loop WITHOUT elaboration. M3a fixtures therefore must not rely on
same-file grammar extensions (they can't — that's the M3a/M3b line).

Canonical JSON (locked, see plan Global Constraints):
  node    {"c":[…],"k":"<kind>"}     atom  {"a":"<text>","s":[b,e]}
  ident   {"i":"<raw>","s":[b,e]}    missing {"k":"<missing>"}
Json.compress prints object keys RBMap-sorted = alphabetical, matching
leanr's canon.rs writer.

Usage: lean --run dump_syntax.lean <file.lean>   (pinned toolchain)
-/
import Lean

open Lean Parser Elab

def spanJson : SourceInfo → Json
  | .original _ pos _ tailPos => Json.arr #[Json.num pos.byteIdx, Json.num tailPos.byteIdx]
  | _ => Json.null

partial def toCanon : Syntax → Json
  | .missing => Json.mkObj [("k", "<missing>")]
  | .node _ kind args =>
    Json.mkObj [("k", kind.toString), ("c", Json.arr (args.map toCanon))]
  | .atom info val =>
    Json.mkObj [("a", val), ("s", spanJson info)]
  | .ident info rawVal _ _ =>
    Json.mkObj [("i", rawVal.toString), ("s", spanJson info)]

unsafe def main (args : List String) : IO Unit := do
  let fileName := args.head!
  let input ← IO.FS.readFile fileName
  Lean.initSearchPath (← Lean.findSysroot)
  let inputCtx := Parser.mkInputContext input fileName
  let (header, parserState, messages) ← Parser.parseHeader inputCtx
  let (env, _messages) ← processHeader header {} messages inputCtx
  IO.println (toCanon header.raw).compress
  let pmctx : Parser.ParserModuleContext := { env, options := {} }
  let mut state := parserState
  let mut msgs : MessageLog := {}
  repeat
    let (cmd, state', msgs') := Parser.parseCommand inputCtx pmctx state msgs
    state := state'
    msgs := msgs'
    IO.println (toCanon cmd).compress
    if Parser.isTerminalCommand cmd then
      break
```

ORACLE-PORT: exact API names (`processHeader` module path, `ParserModuleContext` fields, mut-in-`main` syntax) may need adaptation to the pin — compile it with `lean --run` and fix until it runs; that's Step 4. If `header.raw` doesn't typecheck, it's `header` already being `Syntax` in this pin.

- [ ] **Step 4: first fixture + regen** — `tests/fixtures/syntax/Micro.lean`:

```lean
prelude

def x := 42
```

Run (needs toolchain):
```bash
lean --run tests/fixtures/syntax/dump_syntax.lean tests/fixtures/syntax/Micro.lean \
  > tests/fixtures/syntax/Micro.stx.jsonl
cat tests/fixtures/syntax/Micro.stx.jsonl
```
Expected: 2–3 JSON lines (header, the def, possibly eoi). **Read them carefully** — they are the ground truth for: header node shape, `declModifiers` arity, whether eoi is dumped, span conventions, ident vs atom leaves. Fix the micro grammar + canon writer until Step 5 passes.

- [ ] **Step 5: the golden test** — `crates/leanr_syntax/tests/oracle_golden.rs`:

```rust
//! The M3a oracle gate (spec §Testing 4–5): every fixture under
//! tests/fixtures/syntax/ must (a) round-trip byte-exact and (b) —
//! when a committed .stx.jsonl dump exists — match official Lean's
//! parse tree in canonical form, line for line. Hermetic: dumps are
//! committed; regen needs the toolchain (mise run fixtures:regen).

use leanr_syntax::{builtin, canon, parse_module};

fn fixture_dir() -> std::path::PathBuf {
    std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/syntax")
}

#[test]
fn corpus_round_trips_and_matches_oracle_dumps() {
    let snap = builtin::snapshot();
    let mut checked_any = false;
    for entry in std::fs::read_dir(fixture_dir()).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().and_then(|e| e.to_str()) != Some("lean")
            || path.file_name().unwrap() == "dump_syntax.lean"
        {
            continue;
        }
        let src = std::fs::read_to_string(&path).unwrap();
        let result = parse_module(&src, &snap);

        // (a) byte round-trip — EVERY fixture, error files included.
        assert_eq!(result.tree.text(), src, "round-trip failed: {path:?}");

        // (b) oracle equality — fixtures with a committed dump.
        let dump = path.with_extension("stx.jsonl");
        if dump.exists() {
            assert!(
                result.errors.is_empty(),
                "{path:?}: oracle-compared fixtures must parse clean: {:?}",
                result.errors
            );
            let want = std::fs::read_to_string(&dump).unwrap();
            let got = canon::canon_jsonl(&result.tree);
            for (i, (g, w)) in got.lines().zip(want.lines()).enumerate() {
                assert_eq!(g, w, "{path:?} line {}", i + 1);
            }
            assert_eq!(
                got.lines().count(),
                want.lines().count(),
                "{path:?}: line-count mismatch"
            );
            checked_any = true;
        }
    }
    assert!(checked_any, "no oracle dumps found — corpus wiring broken");
}
```

Run: `cargo test -p leanr_syntax --test oracle_golden`
Expected: PASS after grammar/canon iteration. This is the task's exit gate.

- [ ] **Step 6: wire regen** — in `mise.toml`, append to `fixtures:regen`'s `run` list:

```toml
  # M3a parser fixtures: official parse trees in canonical JSON
  # (tests/fixtures/syntax/; dump_syntax.lean is the dumper itself).
  "sh -c 'for f in tests/fixtures/syntax/*.lean; do [ \"$(basename $f)\" = dump_syntax.lean ] && continue; lean --run tests/fixtures/syntax/dump_syntax.lean \"$f\" > \"${f%.lean}.stx.jsonl\"; done'",
```

Run: `mise run fixtures:regen` — confirm `Micro.stx.jsonl` is reproduced byte-identically (`git diff --stat` clean for fixture dumps).

- [ ] **Step 7: Commit**

```bash
mise run fmt
git add -A
git commit -m "feat(syntax): parse_module vertical slice — module header, oracle dump harness, first golden fixture (M3a Task 7)"
```

---

### Task 8: Term + level grammar breadth

**Files:**
- Create: `crates/leanr_syntax/src/builtin/level.rs`
- Create: `crates/leanr_syntax/src/builtin/term.rs` (micro term entries move here from `command.rs`)
- Create: `tests/fixtures/syntax/Terms.lean`, `tests/fixtures/syntax/Unicode.lean` (+ regen dumps)

**Interfaces:**
- Produces: `level::register(&mut SnapshotBuilder)`, `term::register(&mut SnapshotBuilder)` wired into `builtin::snapshot()`.
- Consumes: Tasks 5–7 machinery + Task 4's surface table (the authoritative port list).

**Porting method (applies here and in Tasks 9–10):** for each `port`-status parser in the surface table's term/level sections, read its definition at the cited source line and transcribe: `leading_parser`/`trailing_parser` → `leading2`/`trailing2` with the declared prec/lhs-prec; combinators map 1:1 onto `Prim` (`optional` → `opt`, `many`, `sepBy1`, `<|>` → `or_else`, `atomic`, `checkColGt` etc.); pretty-print hints (`ppSpace`, `ppLine`, `ppGroup`, `ppIndent`) are parsing no-ops — SKIP them; `withAntiquot`/antiquotation wrappers — SKIP (M3b); the node kind is the parser's full declaration name (`Lean.Parser.Term.app`). When a source combinator has no `Prim` counterpart, STOP and add the variant to `Prim` + interpreter + `encode_prim` (exhaustive match keeps this honest) rather than approximating.

- [ ] **Step 1: `level.rs`** — the `level` category is small (ORACLE-PORT `Level.lean`, ~8 parsers). Complete port, representative shape:

```rust
use crate::grammar::*;

pub fn register(b: &mut SnapshotBuilder) {
    // ORACLE-PORT Lean/Parser/Level.lean — full builtin set:
    // paren  "(" level ")"
    b.leading2("level", "Lean.Parser.Level.paren", MAX_PREC,
        seq([sym("("), cat("level", 0), sym(")")]));
    // max/imax: "max" levels+ ; "imax" levels+
    b.leading2("level", "Lean.Parser.Level.max", MAX_PREC,
        seq([Prim::NonReservedSymbol("max".into()), many1(cat("level", MAX_PREC))]));
    b.leading2("level", "Lean.Parser.Level.imax", MAX_PREC,
        seq([Prim::NonReservedSymbol("imax".into()), many1(cat("level", MAX_PREC))]));
    b.leading2("level", "Lean.Parser.Level.hole", MAX_PREC, sym("_"));
    b.leading2("level", "num", MAX_PREC, Prim::NumLit);
    b.leading_raw("level", Prim::Ident); // bare universe variable
    // trailing: "+" num  (Level.addLit, prec/lhs from source)
    b.trailing2("level", "Lean.Parser.Level.addLit", 65, 65,
        seq([sym("+"), Prim::NumLit]));
    // ^ every prec number above: VERIFY against Level.lean; the numbers
    // here are the expected ones, the source is authoritative.
}
```

- [ ] **Step 2: `term.rs`** — port the term category's `port`-status rows. The must-have set for the M3a corpus (each with its oracle kind name; read each definition in `Term.lean` for the exact child structure):

`ident` (raw leading), `num`/`scientific`/`str`/`char`/`name` literals, `Term.hole` (`_`), `Term.syntheticHole` (`?x`/`?_`), `Term.sort`+`Term.prop`+`Term.type` (`Sort`/`Prop`/`Type` with optional level), `Term.paren` (incl. tuple `(a, b)` and `()`), `Term.anonymousCtor` (`⟨…⟩`), `Term.explicit` (`@f`), `Term.forall` (`∀`/binders/`,` body), `Term.fun` (incl. `fun | pat => e` match-alts form; `=>` and `↦`), `Term.let`/`Term.letrec`? (per surface table), `Term.have`? (per surface table — likely Init macro: check), `Term.show`? (check), `Term.match` (discriminants, optional motive, `with`, alts `| p => e`), `Term.structInst` (`{ x := e, … }` incl. `with`/`..`), `Term.typeAscription` (`(e : T)`), binder forms (`explicitBinder`/`implicitBinder`/`strictImplicitBinder`/`instBinder` — shared with commands via a `binders()` helper fn), `Term.app` (trailing: function application — juxtaposition at `ARG_PREC` via a trailing entry whose body is `many1` of arg-position terms; PORT the real structure, it is subtle), `Term.proj` (trailing `.` + fieldIdx/ident with `CheckNoWsBefore`), `Term.arrow` (trailing `→`/`->` at prec 25, rhs 24 — right assoc), `Term.depArrow` (`(x : A) → B`), `Term.byTactic` (`by` + tacticSeq — tacticSeq itself lands in Task 9; register `by` here gated on the tactic category existing), `Term.subst`? / `Term.letMVar`? — per table; defer anything the table defers.

Structure the file as one `fn` per parser + `pub fn register(b)` calling them in source order. Move the Task-7 micro term entries here (idents/num) so `command.rs` keeps only commands.

- [ ] **Step 3: fixtures** — `tests/fixtures/syntax/Terms.lean` exercising every ported term parser (prelude-mode, builtin-only; NO Init notation — no `+`, `=`, etc. Application, arrows, foralls, lambdas, match, structure-instance literals, projections, ascriptions, holes are all builtin and legal):

```lean
prelude

def app (f : A → B) (a : A) : B := f a
def compose (f : B → C) (g : A → B) : C := fun a => f (g a)
def fa : ∀ (x : A) {y : B} [inst : C] ⦃z : D⦄, E := sorryPlaceholder
def lam2 := fun (a : A) {b : B} => a
def lamMatch := fun | y => y
def letTerm := let x := f a; g x
def matchTerm (n : N) : N := match n, m with
  | c, _ => c
  | _, d => d
def structTerm : S := { field := a, other := b }
def structUpdate (s : S) : S := { s with field := a }
def projections (s : S) := s.field.1.2
def ascription := (a : A)
def tuple := (a, b, c)
def unit' := ()
def anon : S := ⟨a, b⟩
def explicitApp := @f A a
def holes : A := _
def synth : A := ?_
def sorts := fun (α : Sort 1) (β : Type 2) (γ : Prop) => γ
def uni.{u, v} (α : Sort u) (β : Sort (max u v)) : Sort _ := α
def arrowChain : (A → B) → A → B := fun f a => f a
```

(`sorryPlaceholder` is a plain ident — `sorry` itself may be a keyword; keep fixtures keyword-clean per the surface table. If any line uses something the table marked defer/Init — the regen dump errors or the golden diff fails — REPLACE the line, don't port extra grammar to save it. Elaboration is irrelevant: the dump script never elaborates.)

`tests/fixtures/syntax/Unicode.lean`:

```lean
prelude

def «weird name» := «another one»
def α₁' (β! : A) := β!
def ℕtest (x : A) := x
def strLits := "line\nnext\ttab \x41 A quote\""
def strGap := "start \
   continued"
def rawStr := r"no \escapes here"
def rawStrHash := r#"quote " inside"#
def chars := ('a', '\n', '\'')
def nums := (0x1F, 0b101, 0o17, 42, 2.5, 1e-3, 6.02e23)
def names := (`foo.bar, ``qualified)
```

- [ ] **Step 4: regen + golden**

```bash
mise run fixtures:regen
cargo test -p leanr_syntax --test oracle_golden
```
Expected: dumps regenerate (Micro's byte-identical), Terms/Unicode gain dumps, golden test passes. Iterate on ports (prec numbers, null-node arities, `Term.app`'s exact shape) until zero diffs. When the oracle dump itself errors on a fixture line ("unexpected token"), the LINE is wrong (uses non-builtin grammar) — fix the fixture per Step 3's rule.

- [ ] **Step 5: Commit**

```bash
mise run fmt
git add -A
git commit -m "feat(syntax): term + level builtin grammar; Terms/Unicode oracle fixtures green (M3a Task 8)"
```

---

### Task 9: match/do/by — Do.lean + Tactic.lean builtins

**Files:**
- Create: `crates/leanr_syntax/src/builtin/do_notation.rs`
- Create: `crates/leanr_syntax/src/builtin/tactic.rs`
- Modify: `crates/leanr_syntax/src/builtin/term.rs` (wire `Term.do`, `Term.byTactic` bodies)
- Create: `tests/fixtures/syntax/MatchDo.lean`, `tests/fixtures/syntax/ByTac.lean` (+ dumps)

**Interfaces:**
- Produces: `do_notation::register`, `tactic::register`; `Term.do`/`Term.byTactic` complete.
- Consumes: Task 6's indentation combinators (`Many1Indent`, `SepByIndentSemicolon`, `CheckColGt`, `CheckColEq`) — this task is where they earn their keep; expect to refine their semantics against the oracle here.

- [ ] **Step 1: `do_notation.rs`** — ORACLE-PORT `Lean/Parser/Do.lean`. Port the `port`-status rows: `Term.do` (`"do" doSeq`), `Term.doSeqIndent`/`doSeqBracketed` (the `SepByIndentSemicolon` client), `doLet` (`let` + optional `mut` + letDecl), `doLetArrow` (`let x ← e`), `doBind`? (per source), `doExpr`, `doIf` (with `then`/`else if`/`else` chains — read the source, the else-if encoding is a specific nested null shape), `doFor` (`for x in xs do …`), `doWhile`?, `doReturn`, `doUnless`?, `doMatch`, `doSeqItem`. Register a `doElem` category in `builtin::snapshot()` first (`b.category("doElem")`).

- [ ] **Step 2: `tactic.rs`** — ORACLE-PORT `Lean/Parser/Tactic.lean` (+ `Tactic/` dir). The builtin tactic set is deliberately tiny (Task 4's table confirms: `unknown`, `nestedTactic`, `«match»`, `introMatch`, plus the tacticSeq machinery `tacticSeq`/`tacticSeq1Indented`/`tacticSeqBracketed` from `Term.lean`/`Tactic.lean` — port whatever the table lists, nothing more). `Term.byTactic`'s body = `"by" tacticSeq` with the col-gt gating from the source.

- [ ] **Step 3: fixtures** — `MatchDo.lean` (match alts incl. multiple patterns per alt `| a | b => e`, guards? (per source — likely none builtin), nested match; do-blocks with let/letArrow/if/for/return over ident-applications only):

```lean
prelude

def m1 (n : N) : N := match n with
  | z => z
def m2 (p : Prod A B) : A := match p with
  | pair a _ => a
def m3 (n m : N) : N :=
  match n, m with
  | a, b => f a b
def doBlock (act : M A) : M A := do
  let x ← act
  let y := f x
  if cond then
    pure y
  else
    act
def doFor (xs : List A) : M Unit := do
  for x in xs do
    consume x
  return
def doNested : M A := do
  let a ← do
    let b ← inner
    pure b
  pure a
```

`ByTac.lean` (builtin tactics only — match/introMatch/nested seq; NO Init tactics like exact/intro):

```lean
prelude

theorem t1 (h : P) : P := by
  match h with
  | hp => nested (hp)
```

**Honest caveat baked into the fixture:** whether `nested (hp)` — or anything — closes a builtin-only tactic block gracefully is settled by the oracle dump: the dump script does NOT elaborate, so any *parse-valid* tactic body works. If `«match»`'s alt bodies require a tactic and no builtin tactic fits, use a nested `match` or the `nestedTactic` bracket form; iterate against the dump. If the surface table shows the tactic set is too thin for ANY sensible `by` fixture, record that in the surface doc ("by-block corpus coverage: syntactic via tacticSeq + match only") and keep whatever minimal `by` fixture the oracle accepts — the spec's acceptance bar (§Acceptance 1: "by blocks") is met by parsing `by` + tacticSeq + a builtin tactic, not by tactic breadth (that's M3b, per the spec's own scope line).

- [ ] **Step 4: regen + golden** — same loop as Task 8 Step 4. The indentation semantics (`SepByIndentSemicolon` col-eq vs col-ge, where the position marker sits) will need refinement here; the oracle diffs are the spec.

- [ ] **Step 5: Commit**

```bash
mise run fmt
git add -A
git commit -m "feat(syntax): do-notation + builtin tactic grammar; MatchDo/ByTac fixtures green (M3a Task 9)"
```

---

### Task 10: Command grammar breadth

**Files:**
- Modify: `crates/leanr_syntax/src/builtin/command.rs` (replace the micro set with the full port)
- Create: `tests/fixtures/syntax/Decls.lean`, `Types.lean`, `Cmds.lean` (+ dumps)

**Interfaces:**
- Produces: the full `command` category per the surface table.
- Consumes: term grammar (declarations embed terms/binders), Task 4 table.

- [ ] **Step 1: port the declaration family** — ORACLE-PORT `Lean/Parser/Command.lean`. The one big parser is `declaration`: `declModifiers` (docComment? / attributes `@[…]` / visibility `private`/`protected` / `noncomputable` / `unsafe` / `partial`/`nonrec` — each an optional null slot with EXACT arity from the source) followed by `or_else` over `definition`/`theorem`/`abbrev`/`example`/`instance`/`axiom`/`opaque`/`inductive`/`classInductive`/`structure` (+ `deriving` clauses). Port each with its `declId`/`declSig`/`optDeclSig`/`declVal` sub-structure (`declValSimple` `:=`, `declValEqns` `| pat => …`, `whereStructInst`). `docComment` is a token-pair parser: `/--` + everything to `-/` — implement as a dedicated `Prim`-free primitive? No: add it as lexer support — when the parser expects `docComment`, the `"/--"` atom (from the table, Task 2's test) is followed by a raw-scan to `-/`; implement as a new `Prim::DocCommentBody` primitive (raw scan, emits one atom token) + `encode_prim` arm. Kind: `Lean.Parser.Command.docComment` (verify name).

- [ ] **Step 2: port the rest of the command set** — per the table: `namespace`/`section`/`end`, `open` (all its scoped/renaming/hiding sub-forms), `universe`, `variable`, `set_option` (option value = ident/num/str/`true`/`false`), `attribute` command, `#check`/`#eval`/`#print` (whatever the table lists as builtin), `mutual`/`end` blocks, `export`, `init_quot`? (port — trivial), `import` mid-file error form if builtin. Same one-fn-per-parser structure.

- [ ] **Step 3: fixtures** —

`Decls.lean`:
```lean
prelude

/-- A doc comment. -/
def documented (a : A) : A := a
@[someAttr] def attributed := x
private def hidden' := x
protected def prot := x
noncomputable def nc : A := x
unsafe def dangerous : A := x
partial def looping (a : A) : A := looping a
theorem thm (h : P) : P := h
abbrev shortcut : A := x
example : A := x
axiom ax : P
opaque opq : A
def withEqns : N → N
  | z => z
def withWhere : A := helper
  where helper : A := x
mutual
  def evenish : N → N
    | z => z
  def oddish : N → N
    | z => z
end
```

`Types.lean`:
```lean
prelude

structure Point (α : Sort 1) where
  x : α
  y : α

structure Extended (α : Sort 1) extends Point α where
  z : α

inductive Tree (α : Sort 1) where
  | leaf : Tree α
  | node (l : Tree α) (v : α) (r : Tree α) : Tree α

class Marker (α : Sort 1) where
  mark : α → α

instance : Marker Unit' where
  mark u := u
```

`Cmds.lean`:
```lean
prelude

namespace Outer
namespace Inner
def deep := x
end Inner
end Outer

section MySection
universe u v
variable (α : Sort u) {β : Sort v}
def usesVars (a : α) := a
end MySection

open Outer
open Outer.Inner in
def opened := deep
open Outer (Inner)
set_option maxHeartbeats 400000
set_option pp.all true in
def optioned := x
attribute [someAttr] opened
export Outer (Inner)
#check opened
```

(Every construct above must be builtin per the table — where it isn't (e.g. if `#eval`'s parser or `attribute` forms differ), fix the fixture, not the scope. The dump errors point straight at offenders.)

- [ ] **Step 4: regen + golden** — the Task 8 loop again. Also rerun ALL fixtures: `cargo test -p leanr_syntax --test oracle_golden`.

- [ ] **Step 5: delete the Task-7 micro-grammar remnants** — `command.rs` should now contain only the real ports; grep for `"<term-ident>"` and other placeholder kind names — none may survive.

- [ ] **Step 6: Commit**

```bash
mise run fmt
git add -A
git commit -m "feat(syntax): full builtin command grammar; Decls/Types/Cmds oracle fixtures green (M3a Task 10)"
```

---

### Task 11: Error recovery hardening + diagnostics

**Files:**
- Modify: `crates/leanr_syntax/src/parse.rs` (recovery polish, diagnostic rendering helper)
- Create: `tests/fixtures/syntax/Errors0.lean`, `tests/fixtures/syntax/Errors1.lean` (NO dumps — round-trip-only, spec §Oracle: error fixtures are excluded from oracle equality)

**Interfaces:**
- Produces: `parse::render_error(src: &str, e: &ParseError) -> String` (`file-agnostic "line:col: error[E0301]: …"` body used by the CLI); recovery behavior pinned by tests.
- Consumes: Task 7's `recover_command`.

- [ ] **Step 1: error fixtures** —

`Errors0.lean` (mid-file garbage between two good commands):
```lean
prelude

def good1 := x

⊄⊄ this is not lean $$ %%

def good2 := y
```

`Errors1.lean` (unterminated constructs + a broken declaration):
```lean
prelude

def broken : A :=

def good3 := "unterminated
```

- [ ] **Step 2: write the failing tests** — append to `oracle_golden.rs`:

```rust
#[test]
fn error_fixtures_round_trip_and_resync() {
    let snap = builtin::snapshot();
    let src = std::fs::read_to_string(fixture_dir().join("Errors0.lean")).unwrap();
    let r = parse_module(&src, &snap);
    assert_eq!(r.tree.text(), src, "losslessness is TOTAL (spec §Acceptance 2)");
    assert!(!r.errors.is_empty());
    // Resync: both good commands still parse as declarations.
    let kinds = r.tree.kinds.clone();
    let decls = r
        .tree
        .root()
        .children()
        .filter(|c| kinds.name(c.kind()) == "Lean.Parser.Command.declaration")
        .count();
    assert_eq!(decls, 2, "commands after the error must parse normally");
    // The garbage is contained in an <error> node.
    let errs = r
        .tree
        .root()
        .children()
        .filter(|c| kinds.name(c.kind()) == "<error>")
        .count();
    assert_eq!(errs, 1);
}

#[test]
fn every_error_has_a_stable_code_and_a_span_inside_the_file() {
    let snap = builtin::snapshot();
    for name in ["Errors0.lean", "Errors1.lean"] {
        let src = std::fs::read_to_string(fixture_dir().join(name)).unwrap();
        let r = parse_module(&src, &snap);
        assert_eq!(r.tree.text(), src, "{name}");
        for e in &r.errors {
            assert!(e.code.starts_with("E03"), "{name}: {:?}", e);
            assert!((e.span.1 as usize) <= src.len());
            assert!(e.span.0 <= e.span.1);
        }
    }
}
```

- [ ] **Step 3: run, fix recovery until green.** Likely fixes: `recover_command` must also stop at tokens that START a command via ident-shaped keywords (`def`, `theorem`, …) even mid-line; `Errors1`'s unterminated string must surface E0302 exactly once (dedupe lex errors when speculation re-lexes the same offset — keep a `BTreeSet<(u32, &'static str)>` of reported (offset, code) pairs in `Ps`; this ALSO fixes duplicate diagnostics from longest-match re-runs — write a targeted unit test: parse `"def x := \"open` and assert `errors.len() == 1` for E0302).

- [ ] **Step 4: `render_error`** (used by CLI in Task 13):

```rust
/// "12:5: error[E0301]: unexpected input; expected one of: ':=', '('"
pub fn render_error(src: &str, e: &ParseError) -> String {
    let mut line = 1;
    let mut col = 1;
    for (i, c) in src.char_indices() {
        if i >= e.span.0 as usize {
            break;
        }
        if c == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    format!("{line}:{col}: error[{}]: {}", e.code, e.msg)
}
```

Unit test: an error at the start of line 3 renders `3:1: …`.

- [ ] **Step 5: Commit**

```bash
mise run fmt
git add -A
git commit -m "feat(syntax): command resync recovery + stable-coded diagnostics; error fixtures (M3a Task 11)"
```

---

### Task 12: Property tests + fuzz target

**Files:**
- Modify: `crates/leanr_syntax/tests/lossless.rs` (parser-level properties join the Task-3 lexer property)
- Create: `crates/leanr_syntax/fuzz/Cargo.toml`, `crates/leanr_syntax/fuzz/fuzz_targets/parse_module.rs`
- Modify: `mise.toml` (fuzz task split)

**Interfaces:**
- Produces: the spec §Testing 2–3 gates.
- Consumes: `parse_module`, `builtin::snapshot`.

- [ ] **Step 1: parser properties** — append to `lossless.rs`:

```rust
use leanr_syntax::{builtin, parse_module, GrammarSnapshot};
use std::sync::OnceLock;

fn snap() -> &'static GrammarSnapshot {
    static S: OnceLock<GrammarSnapshot> = OnceLock::new();
    S.get_or_init(builtin::snapshot)
}

proptest! {
    /// Spec §Acceptance 2 as a property: TOTAL losslessness.
    #[test]
    fn parse_round_trips_arbitrary_input(src in ".*") {
        let r = parse_module(&src, snap());
        prop_assert_eq!(r.tree.text(), src);
    }

    /// Keyword-dense soup stresses the interesting paths harder than
    /// uniform-random strings.
    #[test]
    fn parse_round_trips_lean_shaped_soup(
        parts in proptest::collection::vec(
            prop_oneof![
                Just("def".to_string()), Just("theorem".to_string()),
                Just(":=".to_string()), Just("fun".to_string()),
                Just("=>".to_string()), Just("(".to_string()),
                Just(")".to_string()), Just("{".to_string()),
                Just("match".to_string()), Just("with".to_string()),
                Just("|".to_string()), Just("do".to_string()),
                Just("\n".to_string()), Just(" ".to_string()),
                Just("«x»".to_string()), Just("/- c -/".to_string()),
                Just("\"s\"".to_string()), Just("42".to_string()),
                "[a-z]{1,4}".prop_map(|s| s),
            ],
            0..64,
        )
    ) {
        let src = parts.concat();
        let r = parse_module(&src, snap());
        prop_assert_eq!(r.tree.text(), &src);
    }

    /// Reparse stability: parsing the (identical) text again yields the
    /// same canonical tree — determinism guard for the Pratt machinery.
    #[test]
    fn reparse_is_stable(src in ".*") {
        let r1 = parse_module(&src, snap());
        let r2 = parse_module(&src, snap());
        prop_assert_eq!(
            leanr_syntax::canon::canon_jsonl(&r1.tree),
            leanr_syntax::canon::canon_jsonl(&r2.tree)
        );
    }
}
```

Run: `cargo test -p leanr_syntax --test lossless` — expect pass (fix any counterexample; shrunk cases become permanent regression `#[test]`s at the bottom of the file).

- [ ] **Step 2: fuzz target** — mirror `crates/leanr_olean/fuzz` exactly. `crates/leanr_syntax/fuzz/Cargo.toml`:

```toml
[package]
name = "leanr_syntax-fuzz"
version = "0.0.0"
publish = false
edition = "2021"

[package.metadata]
cargo-fuzz = true

[dependencies]
libfuzzer-sys = "0.4"

[dependencies.leanr_syntax]
path = ".."

[[bin]]
name = "parse_module"
path = "fuzz_targets/parse_module.rs"
test = false
doc = false
bench = false

[workspace]
```

`fuzz_targets/parse_module.rs`:

```rust
//! Never-panic / always-terminate gate over arbitrary bytes
//! (docs/THREAT_MODEL.md: source text). Also asserts total
//! losslessness — the cheapest strong invariant a fuzzer can check.
#![no_main]

use libfuzzer_sys::fuzz_target;
use std::sync::OnceLock;

fuzz_target!(|data: &[u8]| {
    let Ok(src) = std::str::from_utf8(data) else { return };
    static SNAP: OnceLock<leanr_syntax::GrammarSnapshot> = OnceLock::new();
    let snap = SNAP.get_or_init(leanr_syntax::builtin::snapshot);
    let r = leanr_syntax::parse_module(src, snap);
    assert_eq!(r.tree.text(), src);
});
```

Seed corpus: `mkdir -p crates/leanr_syntax/fuzz/corpus/parse_module && cp tests/fixtures/syntax/*.lean crates/leanr_syntax/fuzz/corpus/parse_module/`.

- [ ] **Step 3: mise task split** — replace the `[tasks.fuzz]` entry:

```toml
[tasks."fuzz:olean"]
description = "(same description text as the current fuzz task)"
dir = "crates/leanr_olean"
run = "ASAN_OPTIONS=detect_leaks=0 cargo +nightly-2026-07-01 fuzz run module_data -- -max_total_time=60"

[tasks."fuzz:syntax"]
description = "Fuzz the Lean source parser (never panic, always terminate, total losslessness). Same nightly/leak-detection caveats as fuzz:olean."
dir = "crates/leanr_syntax"
run = "ASAN_OPTIONS=detect_leaks=0 cargo +nightly-2026-07-01 fuzz run parse_module -- -max_total_time=60"

[tasks.fuzz]
depends = ["fuzz:olean", "fuzz:syntax"]
```

(Copy the long nightly-toolchain comment from the existing task onto `fuzz:olean` verbatim — it documents a real sandbox constraint.)

Run: `mise run fuzz:syntax` (needs the nightly per the comment; locally only). Expected: 60s clean soak, no crashes. Any crash input: commit the shrunk reproducer as a unit test before fixing.

- [ ] **Step 4: Commit**

```bash
mise run fmt
git add -A
git commit -m "test(syntax): parser round-trip/determinism properties + parse_module fuzz target (M3a Task 12)"
```

---

### Task 13: CLI `leanr parse` + docs

**Files:**
- Modify: `crates/leanr_cli/src/main.rs`
- Modify: `crates/leanr_cli/Cargo.toml` (dep on `leanr_syntax`)
- Modify: `ARCHITECTURE.md`, `docs/THREAT_MODEL.md`

**Interfaces:**
- Produces: `leanr parse [--dump] <file>` (spec §Acceptance 4).
- Consumes: `parse_module`, `canon::canon_jsonl`, `parse::render_error`, `GrammarSnapshot::fingerprint`.

- [ ] **Step 1: CLI test first** — `crates/leanr_cli/tests/parse_cmd.rs`:

```rust
//! `leanr parse` surface: dump matches the library canon; parse errors
//! exit nonzero with coded diagnostics; invalid UTF-8 is E0305.

use std::process::Command;

fn leanr() -> Command {
    Command::new(env!("CARGO_BIN_EXE_leanr"))
}

#[test]
fn parse_dump_emits_canonical_jsonl() {
    let dir = tempfile::tempdir().unwrap(); // if tempfile isn't already a
    // dev-dep of leanr_cli, use std::env::temp_dir()+pid like the other
    // CLI tests do — follow the existing pattern in tests/leanr_cli/.
    let f = dir.path().join("T.lean");
    std::fs::write(&f, "prelude\n\ndef x := 42\n").unwrap();
    let out = leanr().args(["parse", "--dump"]).arg(&f).output().unwrap();
    assert!(out.status.success(), "{:?}", out);
    let stdout = String::from_utf8(out.stdout).unwrap();
    assert!(stdout.lines().count() >= 2, "header + command lines");
    assert!(stdout.contains("\"k\":\"Lean.Parser.Module.header\""));
}

#[test]
fn parse_errors_exit_nonzero_with_codes() {
    let dir = tempfile::tempdir().unwrap();
    let f = dir.path().join("Bad.lean");
    std::fs::write(&f, "def := :=").unwrap();
    let out = leanr().arg("parse").arg(&f).output().unwrap();
    assert!(!out.status.success());
    let stderr = String::from_utf8(out.stderr).unwrap();
    assert!(stderr.contains("error[E03"), "{stderr}");
}

#[test]
fn invalid_utf8_is_e0305_not_a_panic() {
    let dir = tempfile::tempdir().unwrap();
    let f = dir.path().join("bin.lean");
    std::fs::write(&f, [0xFF, 0xFE, 0x00]).unwrap();
    let out = leanr().arg("parse").arg(&f).output().unwrap();
    assert!(!out.status.success());
    assert!(String::from_utf8(out.stderr).unwrap().contains("E0305"));
}
```

(Check how existing `tests/leanr_cli/` integration tests are laid out — this repo keeps CLI tests under the top-level `tests/leanr_cli/` tree; put the file where the existing pattern puts it and reuse its tempdir idiom instead of adding `tempfile`.)

- [ ] **Step 2: implement the subcommand** — in `main.rs`, add to `enum Command`:

```rust
    /// Parse a Lean source file with the builtin grammar (M3a: no
    /// imported notation yet) and report syntax errors.
    Parse {
        /// The .lean file to parse.
        file: PathBuf,
        /// Print the canonical parse tree as JSON lines (the oracle-
        /// comparable form; see leanr_syntax::canon).
        #[arg(long)]
        dump: bool,
    },
```

and the handler (thin, per Global Constraints):

```rust
fn parse_cmd(file: &Path, dump: bool) -> ExitCode {
    let bytes = match std::fs::read(file) {
        Ok(b) => b,
        Err(e) => {
            eprintln!("error: cannot read {}: {e}", file.display());
            return ExitCode::FAILURE;
        }
    };
    let src = match String::from_utf8(bytes) {
        Ok(s) => s,
        Err(_) => {
            eprintln!(
                "{}: error[E0305]: file is not valid UTF-8",
                file.display()
            );
            return ExitCode::FAILURE;
        }
    };
    let snap = leanr_syntax::builtin::snapshot();
    let result = leanr_syntax::parse_module(&src, &snap);
    if dump {
        print!("{}", leanr_syntax::canon::canon_jsonl(&result.tree));
    }
    for e in &result.errors {
        eprintln!("{}:{}", file.display(), leanr_syntax::parse::render_error(&src, e));
    }
    if result.errors.is_empty() {
        ExitCode::SUCCESS
    } else {
        ExitCode::FAILURE
    }
}
```

`cargo add --package leanr_cli --path crates/leanr_syntax leanr_syntax` (or edit the manifest by hand matching the existing workspace-path dep style).

Run the Step-1 tests: `cargo test -p leanr_cli --test parse_cmd` → pass.

- [ ] **Step 3: docs** —

`ARCHITECTURE.md`: add the `leanr_syntax` crate bullet after `leanr_olean` (match the existing entries' voice/density):

> - `crates/leanr_syntax` — lossless Lean source trees + the extensible
>   parser (M3a). Trust boundary: source text is untrusted input
>   (`docs/THREAT_MODEL.md`) — the lexer/parser never panic and always
>   terminate, fuzzed via `mise run fuzz:syntax`, and `text(parse(src))
>   == src` holds for every input including parse errors (error nodes +
>   command-resync recovery). The parser interprets a ParserDescr-shaped
>   combinator tree (`grammar::Prim`) over an explicit, fingerprintable
>   `GrammarSnapshot` (token table + Pratt categories) — the
>   parser-state firewall seam the architecture's incrementality story
>   needs, kept batch-mode until M5. M3a ships the builtin grammar
>   (ports of the pinned toolchain's compiled `@[builtin_*_parser]`
>   set, enumerated in
>   `docs/superpowers/specs/2026-07-13-m3a-builtin-surface.md`);
>   imported/declared grammar (ParserDescr interpretation from
>   `.olean`s) is M3b. Correctness bar: byte round-trip + node-exact
>   equality against official parse trees
>   (`tests/fixtures/syntax/`, dumped by `dump_syntax.lean`, regen via
>   `mise run fixtures:regen`). No workspace-crate dependencies.
>   `leanr parse [--dump]` in the CLI.

`docs/THREAT_MODEL.md`: add a row/section next to the `.olean` one:

> **Lean source text** (`leanr parse`, later `fmt`/LSP): arbitrary
> user bytes. Lower stakes than `.olean` (no decoded-value invariants
> to corrupt) but the same bar: no panic, no non-termination, on any
> input — enforced by proptest totality gates and the
> `fuzz:syntax` target. Malformed input degrades to error tokens/nodes
> with stable-coded diagnostics (`E03xx`); losslessness is total, so
> hostile input cannot desynchronize spans.

- [ ] **Step 4: full gate + commit**

```bash
mise run fmt && mise run lint && mise run test
git add -A
git commit -m "feat(cli): leanr parse --dump; syntax crate architecture + threat-model docs (M3a Task 13)"
```

---

### Task 14: Acceptance script + recorded results

**Files:**
- Create: `scripts/parse-acceptance.sh`
- Modify: `mise.toml` (`parse:acceptance` task)
- Modify: `docs/superpowers/specs/2026-07-13-m3a-parser-foundations-design.md` (append `## Acceptance results`)

**Interfaces:**
- Produces: the recorded M3a acceptance run (spec §Acceptance 1–4).
- Consumes: everything.

- [ ] **Step 1: the script** — `scripts/parse-acceptance.sh`:

```bash
#!/usr/bin/env bash
# M3a acceptance (spec §Acceptance): regenerate oracle dumps FRESH from
# the pinned toolchain, diff against committed dumps (catches stale
# fixtures), then run the full hermetic gate + fuzz smoke. Local-only
# (needs the toolchain), like build:acceptance.
set -euo pipefail
cd "$(dirname "$0")/.."

echo "== [1/4] fresh oracle dumps vs committed =="
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
for f in tests/fixtures/syntax/*.lean; do
  base=$(basename "$f")
  [ "$base" = dump_syntax.lean ] && continue
  committed="${f%.lean}.stx.jsonl"
  [ -f "$committed" ] || { echo "  (no dump — round-trip-only) $base"; continue; }
  lean --run tests/fixtures/syntax/dump_syntax.lean "$f" > "$tmp/$base.jsonl"
  diff -u "$committed" "$tmp/$base.jsonl" || { echo "STALE DUMP: $f"; exit 1; }
  echo "  ok $base"
done

echo "== [2/4] hermetic golden + property gates =="
cargo test --release -p leanr_syntax

echo "== [3/4] leanr parse --dump == oracle, per fixture =="
cargo build --release -p leanr_cli
for f in tests/fixtures/syntax/*.lean; do
  base=$(basename "$f")
  [ "$base" = dump_syntax.lean ] && continue
  committed="${f%.lean}.stx.jsonl"
  [ -f "$committed" ] || continue
  ./target/release/leanr parse --dump "$f" | diff -u "$committed" - \
    || { echo "CLI DUMP DIVERGES: $f"; exit 1; }
  echo "  ok $base"
done

echo "== [4/4] fuzz smoke (60s) =="
mise run fuzz:syntax

echo "M3a acceptance: ALL GREEN"
```

`chmod +x scripts/parse-acceptance.sh`, and in `mise.toml`:

```toml
[tasks."parse:acceptance"]
description = "M3a acceptance: fresh oracle dumps vs committed, golden+property gates, CLI dump diff, fuzz smoke (local; needs toolchain + nightly)"
depends = ["elan:bootstrap"]
run = "scripts/parse-acceptance.sh"
```

- [ ] **Step 2: run it**

Run: `mise run parse:acceptance`
Expected: ALL GREEN. Any stale-dump failure means a fixture/dump drifted — regen and re-verify.

- [ ] **Step 3: record results in the spec** — append to `docs/superpowers/specs/2026-07-13-m3a-parser-foundations-design.md`:

```markdown
## Acceptance results (recorded YYYY-MM-DD)

`scripts/parse-acceptance.sh` against the pinned toolchain:

- Fixture corpus: N files, M oracle-compared (list); byte round-trip
  AND oracle-tree equality: zero diffs.
- Error fixtures: total losslessness + resync demonstrated
  (Errors0/Errors1; N commands parse normally after recovery).
- Property gates: lexer totality, parser totality, reparse stability
  (K proptest cases each); fuzz soak 60s clean over the seeded corpus.
- `leanr parse --dump` byte-identical to oracle dumps on all compared
  fixtures.
- Grammar snapshot fingerprint: stable across runs; sensitive to
  grammar edits (unit-tested).
- Divergences discovered and fixed along the way: (record the real
  list — e.g. eoi handling, declModifiers arities, longest-match
  first-wins ties if any fixture hit one.)
```

Fill in real numbers from the run. Also run `mise run ci` one final time.

- [ ] **Step 4: Commit**

```bash
mise run fmt
git add -A
git commit -m "test(syntax): M3a recorded acceptance — oracle dumps fresh-diffed, all gates green (M3a Task 14)"
```

---

## Verification (whole-plan exit bar)

- `mise run ci` green (lint, test, deps, secrets, cache gates untouched).
- `mise run parse:acceptance` green with results recorded in the spec.
- Spec §Acceptance 1–4 each traceable to a passing gate: (1) Task 8–10 fixtures + Task 14 script; (2) Task 11 tests; (3) Tasks 3/12 properties + fuzz; (4) Task 13 CLI + docs.
- No `unimplemented!`/`todo!` left in `leanr_syntax` (grep).
- `docs/superpowers/specs/2026-07-13-m3a-builtin-surface.md` rows all resolved to port/defer — no blanks.
