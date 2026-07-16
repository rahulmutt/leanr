# M3b2a — Imported Extensions Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `leanr parse` parses `.lean` files using notation declared in their imports, by decoding `parserExtension` entries from the imported `.olean` closure and folding them into the grammar snapshot; acceptance is a Mathlib sweep with a checked-in pass-list plus a hermetic synthetic-import corpus in CI.

**Architecture:** `leanr_olean` gains typed decode of `Lean.Parser.parserExtension` entries (pure decode, untrusted bytes). A new crate `leanr_grammar` (deps: `leanr_olean`, `leanr_kernel`, `leanr_syntax`) interprets `ParserDescr` constant Exprs into `Prim` and assembles a per-import-set base snapshot by **rebuilding via `SnapshotBuilder`** (builtins + imported entries, cached per import set) — NOT by extending the M3b1 `Overlay`, which cannot introduce categories and whose dispatch is only consulted for base categories. Same-file M3b1 overlay threading runs unchanged on top of the assembled base. Anything uninterpretable is skipped-and-recorded, never guessed.

**Tech Stack:** Rust workspace (edition 2021); `rowan`/`blake3` in `leanr_syntax`; no new external dependencies; pinned Lean toolchain `v4.32.0-rc1` for fixtures/oracle only.

## Global Constraints

- **Oracle discipline:** correctness = byte round-trip + structural oracle-tree equality vs the pinned toolchain (`lean-toolchain` = v4.32.0-rc1). Never bump the pin. Regenerate fixtures only via `mise run fixtures:regen`.
- **Untrusted input:** `.olean` bytes never panic the decoder — every malformed shape is `OleanError::BadShape` via `interp::bad(...)`. New entry decode is automatically covered by the existing `module_data` fuzz target.
- **Skip-and-record:** an imported parser entry that cannot be interpreted is recorded (decl name + reason) and skipped; its tokens still fold. Never guess a parser.
- **Crate boundaries:** `leanr_syntax` keeps zero workspace deps. `leanr_olean` stays decode-only (no `leanr_syntax` dep). `leanr_kernel` untouched. No logic in `leanr_cli` beyond argument plumbing.
- **No new external deps** (deny.toml unchanged). Tools via mise only.
- **CI vs local:** everything under plain `cargo test --workspace` must be hermetic (no network, no toolchain). Mathlib sweep and dump regeneration are local-only (`--ignored` / mise tasks).
- **Commit style:** `type(scope): summary (M3b2a Task N)` matching M3b1 history.

## File Structure

```
crates/leanr_grammar/                    NEW crate (bridge: olean entries → syntax snapshot)
  Cargo.toml
  src/lib.rs                             pub API: assemble(), AssembledGrammar, SkippedEntry, SkipReason
  src/alias.rs                           parser-alias table (name → arity + Prim mapping)
  src/descr.rs                           ParserDescr Expr interpreter (term bank → Prim)
  src/assemble.rs                        entry folding onto builtin SnapshotBuilder
  tests/import_golden.rs                 hermetic CI gate over synthetic import fixtures
  tests/mathlib_sweep.rs                 --ignored local Mathlib sweep + pass-list ratchet
crates/leanr_olean/src/module_data.rs    +ParserEntry/EntryScope types, ModuleData.parser_entries
crates/leanr_olean/src/interp_id.rs      +parser extension entry decode (field f[4])
crates/leanr_olean/src/lib.rs            re-export new types
crates/leanr_syntax/src/builtin/mod.rs   +pub fn builder() (refactor of snapshot())
crates/leanr_syntax/src/grammar/mod.rs   +SnapshotBuilder::{leading_prim, trailing_prim}
crates/leanr_syntax/src/parse.rs         +pub fn parse_header_imports()
crates/leanr_cli/src/main.rs             Parse gains --path/--verbose; import-aware parse_cmd
tests/fixtures/syntax/import/            NEW fixture dir: dep packages + importers + dumps
  Init.lean / Init.olean                 stub prelude module (hermetic closure resolution)
  NotaDep.lean / NotaDep.olean           dep declaring notation/tokens/category (Init-only)
  NotaDepMeta.lean / NotaDepMeta.olean   dep with a raw @[term_parser] Parser (skip coverage)
  ImportMixfix.lean / .stx.jsonl         each mixfix fixity via import
  ImportMunch.lean / .stx.jsonl          imported token changes tokenization
  ImportCat.lean / .stx.jsonl            dep-declared category used via dep notation
  ImportOverload.lean / .stx.jsonl       imported token overloaded by same-file M3b1 notation
tests/fixtures/syntax/mathlib-passlist.txt   checked-in ratchet (created by final gate)
mise.toml                                fixtures:regen additions; parse:mathlib; passlist:update
ARCHITECTURE.md                          leanr_grammar crate entry
docs/superpowers/specs/2026-07-16-m3b2a-imported-extensions-design.md   assembly-mechanism amendment
```

**Interpreter → snapshot data flow:** `ModuleData.parser_entries` (typed, per module) → `assemble()` walks modules in closure order → `Token`/`Kind`/`Category` entries call `SnapshotBuilder` directly → `Parser` entries go through `descr::interpret()` (Expr walk producing a `Prim`, interning kinds via the builder) → `leading_prim`/`trailing_prim` register it → `finish()` yields the flat imported-base `GrammarSnapshot` whose existing `fingerprint()` covers imported grammar.

---

### Task 1: Spec amendment + `leanr_grammar` crate scaffold

The exploration finding that changes the spec: `Overlay` (M3b1) has no category-creation mechanism and `parse.rs::category()` consults the overlay only for categories already in the base snapshot (`parse.rs:2360-2363`, doc at `parse.rs:2741-2742`). Rebuilding a flat snapshot per import set via the existing `SnapshotBuilder` is simpler, keeps the dispatch hot path untouched, supports new categories via the existing `SnapshotBuilder::category`, and its existing `fingerprint()` covers imported grammar wholesale. Cost is one builtin-grammar rebuild per import set (milliseconds, cached by the caller) — nothing like the rejected per-command rebuild.

**Files:**
- Modify: `docs/superpowers/specs/2026-07-16-m3b2a-imported-extensions-design.md` (§"`leanr_grammar`: snapshot assembly")
- Create: `crates/leanr_grammar/Cargo.toml`, `crates/leanr_grammar/src/lib.rs`
- Modify: `Cargo.toml` (workspace members), `ARCHITECTURE.md`

**Interfaces:**
- Produces: workspace crate `leanr_grammar` that later tasks fill in; amended spec.

- [ ] **Step 1: Amend the spec's snapshot-assembly section**

In `docs/superpowers/specs/2026-07-16-m3b2a-imported-extensions-design.md`, replace the paragraph beginning "Folds an import closure's entries, in Lean's import order, onto the M3a builtin snapshot via M3b1's `extend(delta)`:" and its list, with:

```markdown
Folds an import closure's entries, in Lean's import order, into a flat
imported-base snapshot built with the existing `SnapshotBuilder`
(implementation refinement over the drafted `extend(delta)` folding:
the M3b1 overlay cannot introduce categories and dispatch consults it
only for base categories, so extending it would touch the dispatch hot
path; a builder rebuild per import set is one-time per file, cached,
and reuses the already-tested registration path):

- `token` entries into the builder token table (idempotent);
- `kind` entries interned;
- `category` entries create **new categories** via the existing
  `SnapshotBuilder::category` (with their leading-ident behavior);
- `parser` entries become leading/trailing category entries from the
  interpreted `Prim` (leading vs. trailing comes from the constant's
  declared type: `ParserDescr`/`Parser` leading,
  `TrailingParserDescr`/`TrailingParser` trailing, per
  `mkParserOfConstant`, `Lean/Parser/Extension.lean`).

The assembled base snapshot is cached per import set. Its existing
`fingerprint()` covers all imported grammar (tokens, categories,
productions), keeping the M5 firewall seam honest. Same-file M3b1
commands then thread their overlay *on top of* this imported base,
unchanged.
```

- [ ] **Step 2: Create the crate scaffold**

`crates/leanr_grammar/Cargo.toml`:

```toml
[package]
name = "leanr_grammar"
version.workspace = true
edition.workspace = true
license.workspace = true

[dependencies]
leanr_kernel = { version = "0.1.0", path = "../leanr_kernel" }
leanr_olean = { version = "0.1.0", path = "../leanr_olean" }
leanr_syntax = { version = "0.1.0", path = "../leanr_syntax" }
```

`crates/leanr_grammar/src/lib.rs`:

```rust
//! The bridge between decoded `.olean` parser-extension entries and the
//! parser's grammar snapshot: interprets `ParserDescr` constant values
//! from the term bank into `Prim` productions and assembles the
//! per-import-set base snapshot. Sits between `leanr_olean` (which
//! decodes entries but never interprets) and `leanr_syntax` (which has
//! zero workspace deps) — see the M3b2a design spec.

mod alias;
mod assemble;
mod descr;

pub use assemble::{assemble, AssembledGrammar, SkipReason, SkippedEntry};
```

Leave `alias.rs`, `descr.rs`, `assemble.rs` as stubs so the crate compiles; `assemble.rs` stub:

```rust
use std::sync::Arc;

use leanr_kernel::bank::Store;
use leanr_kernel::name::Name;
use leanr_olean::ModuleData;
use leanr_syntax::grammar::GrammarSnapshot;

/// Why an imported entry was not folded into the snapshot.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SkipReason {
    /// Constant has type `Parser`/`TrailingParser` (compiled function;
    /// shims are M3b3).
    RawParser,
    /// `ParserDescr.const/unary/binary` alias not in the table yet.
    UnknownAlias(String),
    /// Value is not a literal constructor tree we can walk.
    UnsupportedShape(&'static str),
    /// Referenced constant not present in the loaded closure.
    MissingConstant,
    /// Recursive `ParserDescr` reference cycle.
    Cycle,
    /// Scoped entry — activation semantics are M3b3.
    ScopedInactive,
}

/// A recorded skip: which declaration, and why.
#[derive(Clone, Debug)]
pub struct SkippedEntry {
    pub decl: String,
    pub reason: SkipReason,
}

/// The imported-base grammar for one import set.
pub struct AssembledGrammar {
    pub snapshot: GrammarSnapshot,
    pub skipped: Vec<SkippedEntry>,
}

/// Fold the closure's parser-extension entries (in closure order) onto
/// the builtin grammar. `modules` is `load_closure` output:
/// dependencies-first, each module once.
pub fn assemble(modules: &[(Arc<Name>, ModuleData)], store: &Store) -> AssembledGrammar {
    let _ = (modules, store);
    todo!("M3b2a Task 7")
}
```

(`alias.rs` and `descr.rs`: empty files with a one-line module doc each.)

Add `"crates/leanr_grammar"` to `members` in the root `Cargo.toml` (after `leanr_olean`).

- [ ] **Step 3: Add the ARCHITECTURE.md crate entry**

After the `crates/leanr_syntax` bullet in `ARCHITECTURE.md`, add:

```markdown
- `crates/leanr_grammar` — the bridge from decoded `.olean`
  parser-extension entries to the parser's grammar (M3b2a). Interprets
  `ParserDescr` constant values from the term bank into `grammar::Prim`
  productions (skip-and-record for anything uninterpretable — raw
  `Parser` functions, unknown aliases) and assembles the per-import-set
  base `GrammarSnapshot` (builtins + imported tokens/kinds/categories/
  parsers, in closure order). Depends on `leanr_olean`, `leanr_kernel`,
  `leanr_syntax`; exists so the untrusted-bytes decoder never
  interprets and the parser keeps zero workspace deps.
```

- [ ] **Step 4: Build and verify the workspace is green**

Run: `cargo test --workspace`
Expected: PASS (new crate compiles; `assemble` is `todo!` but uncalled).

- [ ] **Step 5: Commit**

```bash
git add docs/superpowers/specs/2026-07-16-m3b2a-imported-extensions-design.md \
        crates/leanr_grammar Cargo.toml ARCHITECTURE.md
git commit -m "feat(grammar): leanr_grammar crate scaffold + spec assembly amendment (M3b2a Task 1)"
```

---

### Task 2: Synthetic import fixtures + regen wiring

Author the dependency/importer fixture corpus and wire `fixtures:regen` to build the dep `.olean`s and dump the importers' oracle trees **with imports honored**. Everything produced here is committed (hermetic for CI). Requires the local pinned toolchain (present via `elan:bootstrap`).

**Files:**
- Create: `tests/fixtures/syntax/import/Init.lean`, `NotaDep.lean`, `NotaDepMeta.lean`, `ImportMixfix.lean`, `ImportMunch.lean`, `ImportCat.lean`, `ImportOverload.lean`
- Modify: `mise.toml` (`fixtures:regen` run-list)
- Commit generated: `tests/fixtures/syntax/import/*.olean`, `tests/fixtures/syntax/import/Import*.stx.jsonl`

**Interfaces:**
- Produces: `tests/fixtures/syntax/import/` corpus used by Tasks 3, 6, 7, 8. Dep tokens (exact): `" ⊕⊕ "`, `" ⊗⊗ "`, `"⋄⋄"`, `"‼"`, `"⟪"`, `"⟫"`, `"+++"`, `"wob"`, `"wrap["`, `"]"`; scoped token `" ⊖⊖ "`; category `widget`.

- [ ] **Step 1: Author the stub prelude module**

`tests/fixtures/syntax/import/Init.lean`:

```lean
prelude
-- Stub Init so hermetic tests can resolve NotaDep's auto-import of
-- `Init` without the real toolchain closure. Importer fixtures avoid
-- all real-Init-declared notation for exactly this reason (same
-- self-containment discipline as the M3a/M3b1 corpora).
```

- [ ] **Step 2: Author the dependency modules**

`tests/fixtures/syntax/import/NotaDep.lean` (compiled by real Lean against the real `Init`; only its `.olean` entries matter to leanr):

```lean
-- Declares the imported-notation surface the importer fixtures use.
-- Each mixfix fixity, a multi-token notation, an ASCII munch token,
-- a scoped notation (must be SKIPPED by leanr), and a custom category
-- reachable from term.
infixl:65 " ⊕⊕ " => HAdd.hAdd
infixr:67 " ⊗⊗ " => HMul.hMul
prefix:100 "⋄⋄" => Nat.succ
postfix:200 "‼" => Nat.succ
notation:50 "⟪" x "⟫" => Nat.succ x
infixl:60 " +++ " => HAdd.hAdd
namespace NotaDep
scoped infixl:65 " ⊖⊖ " => HSub.hSub
end NotaDep
declare_syntax_cat widget
syntax "wob" : widget
syntax num : widget
syntax "wrap[" widget "]" : term
```

`tests/fixtures/syntax/import/NotaDepMeta.lean` (raw-`Parser` skip coverage; never imported by importer fixtures — `import Lean` drags Lean's grammar into the oracle, which the corpus discipline forbids):

```lean
import Lean
open Lean Parser in
@[term_parser] def rawWidget : Parser :=
  leading_parser "rawwob"
```

- [ ] **Step 3: Author the importer fixtures**

All importers: `import NotaDep` header only; bodies avoid every real-Init-declared notation (same discipline as M3a — plain `#check`, numerals, idents, and the dep's own tokens only).

`tests/fixtures/syntax/import/ImportMixfix.lean`:

```lean
import NotaDep
#check 1 ⊕⊕ 2 ⊕⊕ 3
#check 1 ⊗⊗ 2 ⊗⊗ 3
#check ⋄⋄1
#check 1‼
#check ⟪4⟫
#check 1 ⊕⊕ 2 ⊗⊗ 3
```

`tests/fixtures/syntax/import/ImportMunch.lean` (the cross-module maximal-munch check — without the imported token `+++`, `1+++2` lexes as `1`, `+`, `+`, `+`, `2`):

```lean
import NotaDep
#check 1+++2
#check 1 +++ 2 +++ 3
```

`tests/fixtures/syntax/import/ImportCat.lean` (dep-declared category `widget` used through the dep's term production; parse-only, so no macro/elaborator needed):

```lean
import NotaDep
#check wrap[wob]
#check wrap[42]
```

`tests/fixtures/syntax/import/ImportOverload.lean` (imported base + same-file M3b1 overlay composing on one token):

```lean
import NotaDep
infixl:65 " ⊕⊕ " => HMul.hMul
#check 1 ⊕⊕ 2
```

- [ ] **Step 4: Wire fixtures:regen**

In `mise.toml`, append to the `fixtures:regen` run-list (after the existing syntax-fixture loop, before `depends_post` fires):

```toml
  "sh -c 'cd tests/fixtures/syntax/import && lean Init.lean -o Init.olean'",
  "sh -c 'cd tests/fixtures/syntax/import && lean NotaDep.lean -o NotaDep.olean && lean NotaDepMeta.lean -o NotaDepMeta.olean'",
  "sh -c 'cd tests/fixtures/syntax/import && for f in ImportMixfix ImportMunch ImportCat; do LEAN_PATH=$PWD lean --run ../dump_syntax.lean $f.lean > $f.stx.jsonl; done'",
  "sh -c 'cd tests/fixtures/syntax/import && LEAN_PATH=$PWD lean --run ../dump_syntax_elab.lean ImportOverload.lean > ImportOverload.stx.jsonl'",
```

Notes for the implementer:
- `NotaDep.olean` must be built against the **real** toolchain `Init` (bare `lean` does that; the stub `Init.olean` exists only for leanr-side closure resolution in hermetic tests and must be built from a `prelude` file so real Lean accepts the name).
- `ImportOverload` needs the **elaborating** dumper (`dump_syntax_elab.lean`) because its same-file `infixl` grows the grammar mid-file; parse-only `dump_syntax.lean` (which already honors imports via `parseHeader`/`processHeader`) suffices for the others. If `dump_syntax_elab.lean` does not resolve `LEAN_PATH` imports as-is, extend it the same way `dump_syntax.lean` does (both must call `processHeader` with the search path in effect).
- The existing flat `tests/fixtures/syntax/*.lean` regen loop must not pick up the `import/` subdir (it globs `tests/fixtures/syntax/*.lean` — already excludes subdirs; verify).

- [ ] **Step 5: Regenerate and eyeball**

Run: `mise run fixtures:regen`
Expected: `tests/fixtures/syntax/import/` contains `Init.olean`, `NotaDep.olean`, `NotaDepMeta.olean`, and four `Import*.stx.jsonl`. Spot-check `ImportMunch.stx.jsonl`: the first `#check` line's tree contains an atom `"+++"` (one token, not three `+`); `ImportMixfix.stx.jsonl` kind names include `«term_⊕⊕_»` (Lean's mangled kind — these dumped names are the byte-exact targets Task 6's interpreter must reproduce).
Also run: `cargo test --workspace` — Expected: PASS (existing `oracle_golden.rs` must be unaffected; it reads `read_dir` non-recursively).

- [ ] **Step 6: Commit**

```bash
git add tests/fixtures/syntax/import mise.toml
git commit -m "test(syntax): synthetic import-notation fixture corpus + regen wiring (M3b2a Task 2)"
```

---

### Task 3: `leanr_olean` — typed `parserExtension` entry decode

Decode `ModuleData` field `f[4]` (`entries : Array (Name × Array EnvExtensionEntry)`, Environment.lean:127) — for the pair whose Name is `Lean.Parser.parserExtension`, decode each element as `ScopedEnvExtension.Entry OLeanEntry`; all other extensions stay opaque. Oracle shapes (pinned toolchain, `Lean/Parser/Extension.lean:57-66`, `Lean/ScopedEnvExtension.lean`):

- `ScopedEnvExtension.Entry α`: tag 0 = `global (v : α)` (1 ptr field), tag 1 = `scoped (ns : Name) (v : α)` (2 ptr fields).
- `OLeanEntry`: tag 0 `token (val : String)` (1 field); tag 1 `kind (val : Name)` (1 field); tag 2 `category (catName declName : Name) (behavior : LeadingIdentBehavior)` (2 ptr fields + behavior — behavior is an enum; **empirically pin whether it is a scalar byte or a boxed `Scalar`** against `NotaDep.olean`, and adjust `ctor` field/scalar expectations to match; both patterns exist in the codebase, cf. `DefinitionSafety` at `interp_id.rs:415-420`); tag 3 `parser (catName declName : Name) (prio : Nat)` (3 ptr fields — `Nat` is boxed).
- `local` declarations never serialize (`addLocalEntry` bypasses `newEntries`); scoped notations serialize as tag-1 `scoped` entries in the same array.

**Files:**
- Modify: `crates/leanr_olean/src/module_data.rs` (types + field), `crates/leanr_olean/src/interp_id.rs` (decode), `crates/leanr_olean/src/lib.rs` (re-exports)
- Test: `crates/leanr_olean/tests/parser_entries.rs` (new)

**Interfaces:**
- Consumes: Task 2's `NotaDep.olean`/`NotaDepMeta.olean` fixtures.
- Produces (used by Task 7):
  ```rust
  pub enum CatBehavior { Default, Symbol, Both }
  pub enum ParserEntry {
      Token(String),
      Kind(NameId),
      Category { cat: NameId, decl: NameId, behavior: CatBehavior },
      Parser { cat: NameId, decl: NameId },
  }
  pub enum EntryScope { Global, Scoped(NameId) }
  pub struct ScopedParserEntry { pub scope: EntryScope, pub entry: ParserEntry }
  // ModuleData gains: pub parser_entries: Vec<ScopedParserEntry>
  ```
  (`prio` is deliberately dropped at decode: leanr dispatch resolves by longest match, and no consumer reads it — YAGNI; the spec's skip-and-record covers any file whose parse depends on priority ordering, and the sweep will surface it.)

- [ ] **Step 1: Write the failing test**

`crates/leanr_olean/tests/parser_entries.rs`:

```rust
use std::path::Path;

use leanr_kernel::bank::Store;
use leanr_olean::{CatBehavior, EntryScope, ModuleData, ParserEntry};

fn fixture(name: &str) -> Vec<u8> {
    let p = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/syntax/import")
        .join(name);
    std::fs::read(&p).unwrap_or_else(|e| panic!("read {}: {e}", p.display()))
}

fn name_string(st: &Store, id: Option<leanr_kernel::bank::NameId>) -> String {
    st.to_name(None, id).to_string()
}

#[test]
fn notadep_entries_decode_typed() {
    let mut st = Store::persistent();
    let md = ModuleData::parse(&fixture("NotaDep.olean"), &mut st).unwrap();

    let tokens: Vec<&str> = md
        .parser_entries
        .iter()
        .filter_map(|e| match &e.entry {
            ParserEntry::Token(t) => Some(t.as_str()),
            _ => None,
        })
        .collect();
    for expected in ["⊕⊕", "⊗⊗", "⋄⋄", "‼", "⟪", "⟫", "+++", "wob", "wrap["] {
        assert!(tokens.contains(&expected), "missing token {expected:?} in {tokens:?}");
    }

    // The custom category arrives as a category entry named `widget`.
    let cat = md
        .parser_entries
        .iter()
        .find_map(|e| match &e.entry {
            ParserEntry::Category { cat, behavior, .. } => Some((cat, behavior)),
            _ => None,
        })
        .expect("widget category entry");
    assert_eq!(name_string(&st, Some(*cat.0)), "widget");
    assert_eq!(*cat.1, CatBehavior::Default);

    // Global parser entries exist for the mixfix decls; the scoped one
    // is tagged Scoped with namespace `NotaDep`.
    let scoped: Vec<_> = md
        .parser_entries
        .iter()
        .filter(|e| matches!(e.scope, EntryScope::Scoped(_)))
        .collect();
    assert!(!scoped.is_empty(), "expected a scoped entry for ⊖⊖");
    let EntryScope::Scoped(ns) = scoped[0].scope else { unreachable!() };
    assert_eq!(name_string(&st, Some(ns)), "NotaDep");

    let global_parsers = md
        .parser_entries
        .iter()
        .filter(|e| {
            matches!(e.scope, EntryScope::Global)
                && matches!(e.entry, ParserEntry::Parser { .. })
        })
        .count();
    // 6 mixfix/notation + 3 widget syntaxes + wrap[] = 10 (adjust ONLY
    // if the committed fixture legitimately differs; count them in the
    // fixture source).
    assert_eq!(global_parsers, 10);
}

#[test]
fn notadepmeta_raw_parser_entry_decodes() {
    let mut st = Store::persistent();
    let md = ModuleData::parse(&fixture("NotaDepMeta.olean"), &mut st).unwrap();
    let raw = md
        .parser_entries
        .iter()
        .find_map(|e| match &e.entry {
            ParserEntry::Parser { decl, .. } => Some(name_string(&st, Some(*decl))),
            _ => None,
        })
        .expect("rawWidget parser entry");
    assert!(raw.ends_with("rawWidget"), "got {raw}");
}

#[test]
fn legacy_fixtures_still_decode() {
    // Modules whose parserExtension entries are absent/empty must keep
    // decoding, with an empty typed vector.
    let mut st = Store::persistent();
    let p = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/Sample.olean");
    let md = ModuleData::parse(&std::fs::read(p).unwrap(), &mut st).unwrap();
    let _ = md.parser_entries.len(); // field exists; content unasserted
}
```

- [ ] **Step 2: Run it to make sure it fails**

Run: `cargo test -p leanr_olean --test parser_entries`
Expected: FAIL — `parser_entries`/`ParserEntry` etc. do not exist.

- [ ] **Step 3: Implement the decode**

In `crates/leanr_olean/src/module_data.rs`, add above `ModuleData`:

```rust
/// `LeadingIdentBehavior` (oracle: Parser/Basic.lean:1643-1659); tag order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CatBehavior {
    Default,
    Symbol,
    Both,
}

/// One typed `Lean.Parser.parserExtension` olean entry
/// (oracle `ParserExtension.OLeanEntry`, Parser/Extension.lean:57-62;
/// tag order). `prio` is dropped: no leanr consumer reads it (dispatch
/// is longest-match) — see the M3b2a design spec.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParserEntry {
    Token(String),
    Kind(NameId),
    Category { cat: NameId, decl: NameId, behavior: CatBehavior },
    Parser { cat: NameId, decl: NameId },
}

/// Scope wrapper (oracle `ScopedEnvExtension.Entry`): `local` never
/// serializes; `scoped` carries its activation namespace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum EntryScope {
    Global,
    Scoped(NameId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScopedParserEntry {
    pub scope: EntryScope,
    pub entry: ParserEntry,
}
```

Add field `pub parser_entries: Vec<ScopedParserEntry>` to `ModuleData` (keep `num_entries`). In the multi-part path (`parse_parts`), take `parser_entries` from the Base part alongside `num_entries` (module_data.rs:204-212).

In `crates/leanr_olean/src/interp_id.rs`, extend `module_data` (interp_id.rs:518-541): keep `num_entries: array(&f[4])?.len()` and add a walk of `array(&f[4])?`:

```rust
// entries : Array (Name × Array EnvExtensionEntry). Only the
// parserExtension pair is decoded (M3b2a); others stay opaque.
let mut parser_entries = Vec::new();
for pair in array(&f[4])? {
    let (pf, _) = ctor(pair, 0, 2, "ModuleData.entries pair")?;
    let ext_name = self.name(&pf[0])?;
    if self.st.to_name(None, ext_name).to_string() != "Lean.Parser.parserExtension" {
        continue;
    }
    for e in array(&pf[1])? {
        parser_entries.push(self.scoped_parser_entry(e)?);
    }
}
```

New private methods on `InterpId`, following the `constant_info` template (interp_id.rs:393-504):

```rust
/// oracle: ScopedEnvExtension.Entry — tag 0 global(v), tag 1 scoped(ns, v).
fn scoped_parser_entry(&mut self, r: &Raw) -> Result<crate::ScopedParserEntry, OleanError> {
    let RawValue::Ctor { tag, fields, .. } = &**r else {
        return Err(bad("ScopedEnvExtension.Entry"));
    };
    let (scope, payload) = match (tag, fields.len()) {
        (0, 1) => (crate::EntryScope::Global, &fields[0]),
        (1, 2) => (crate::EntryScope::Scoped(self.name_req(&fields[0])?), &fields[1]),
        _ => return Err(bad("ScopedEnvExtension.Entry")),
    };
    Ok(crate::ScopedParserEntry { scope, entry: self.parser_entry(payload)? })
}

/// oracle: ParserExtension.OLeanEntry (Extension.lean:57-62), tag order.
fn parser_entry(&mut self, r: &Raw) -> Result<crate::ParserEntry, OleanError> {
    let RawValue::Ctor { tag, fields, scalars } = &**r else {
        return Err(bad("ParserExtension.OLeanEntry"));
    };
    match (tag, fields.len()) {
        (0, 1) => Ok(crate::ParserEntry::Token(string(&fields[0])?)),
        (1, 1) => Ok(crate::ParserEntry::Kind(self.name_req(&fields[0])?)),
        (2, 2) => Ok(crate::ParserEntry::Category {
            cat: self.name_req(&fields[0])?,
            decl: self.name_req(&fields[1])?,
            behavior: match scalars.first().copied() {
                Some(0) => crate::CatBehavior::Default,
                Some(1) => crate::CatBehavior::Symbol,
                Some(2) => crate::CatBehavior::Both,
                _ => return Err(bad("LeadingIdentBehavior")),
            },
        }),
        (3, 3) => {
            let _prio = nat(&fields[2])?; // validated, dropped
            Ok(crate::ParserEntry::Parser {
                cat: self.name_req(&fields[0])?,
                decl: self.name_req(&fields[1])?,
            })
        }
        _ => Err(bad("ParserExtension.OLeanEntry")),
    }
}
```

**Empirical pin:** if `behavior` arrives boxed (a `RawValue::Scalar` third *pointer* field rather than a scalar byte), the `category` arm becomes `(2, 3)` with a `match &*fields[2]` — decide by running the Step 1 test against `NotaDep.olean` and keep whichever shape it exhibits, with a comment citing the observed encoding. Same for the raw `.olean` layout of the pair: if the entries pair is not `Ctor{tag:0, fields:2}`, adjust with an oracle comment. This is the M1a pattern: shapes are pinned by fixture, never guessed.

Re-export in `lib.rs`: `pub use module_data::{CatBehavior, EntryScope, Import, ModuleData, ParserEntry, PartKind, ScopedParserEntry};`

- [ ] **Step 4: Run tests**

Run: `cargo test -p leanr_olean`
Expected: PASS (new test + all existing; existing tests construct `ModuleData` only via `parse`, so the new field needs no other call-site changes).

- [ ] **Step 5: Fuzz smoke (local)**

Run: `mise run fuzz:olean`
Expected: no crashes in 60s (the new decode path runs inside `ModuleData::parse`, so it is fuzzed automatically).

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_olean tests/fixtures/syntax/import
git commit -m "feat(olean): typed Lean.Parser.parserExtension entry decode (M3b2a Task 3)"
```

---

### Task 4: `leanr_syntax` seams — `builtin::builder()`, `leading_prim`/`trailing_prim`, `parse_header_imports`

Three small, independently testable additions inside `leanr_syntax` (still zero workspace deps):

1. Expose the pre-registered builtin `SnapshotBuilder` so `leanr_grammar` can append imported entries before `finish()`.
2. Registration of an **already-shaped** `Prim` (the interpreter output is already `Node`/`TrailingNode`-wrapped by the descr's own `node`/`trailingNode` constructors) — `leading2`/`trailing2` would double-wrap.
3. A header-only parse returning the imports, so the CLI can resolve them before the real parse.

**Files:**
- Modify: `crates/leanr_syntax/src/builtin/mod.rs`, `crates/leanr_syntax/src/grammar/mod.rs`, `crates/leanr_syntax/src/parse.rs`, `crates/leanr_syntax/src/lib.rs`
- Test: unit tests in `grammar/mod.rs` + `parse.rs` test modules (follow each file's existing `#[cfg(test)]` section)

**Interfaces:**
- Produces (used by Tasks 6, 7, 8):
  ```rust
  // builtin/mod.rs
  pub fn builder() -> SnapshotBuilder;              // snapshot() == builder().finish()
  // grammar/mod.rs — SnapshotBuilder methods
  pub fn leading_prim(&mut self, cat: &str, prim: Prim);
  pub fn trailing_prim(&mut self, cat: &str, prim: Prim);
  // parse.rs
  pub fn parse_header_imports(src: &str) -> Vec<String>;   // dotted module names
  ```

- [ ] **Step 1: Write the failing tests**

In `crates/leanr_syntax/src/grammar/mod.rs` tests:

```rust
#[test]
fn leading_prim_registers_and_dispatches() {
    let mut b = crate::builtin::builder();
    let kind = b.kind("Test.imported");
    b.token("@@@");
    b.leading_prim(
        "term",
        Prim::Node {
            kind,
            prec: Some(LEAD_PREC),
            body: std::sync::Arc::new(Prim::Seq(vec![
                Prim::Symbol("@@@".into()),
                Prim::Category { name: "term".into(), rbp: MAX_PREC },
            ])),
        },
    );
    let snap = b.finish();
    let r = crate::parse_module("#check @@@1\n", &snap);
    assert!(r.errors.is_empty(), "{:?}", r.errors);
    assert_eq!(r.tree.text(), "#check @@@1\n");
    assert!(crate::canon::canon_jsonl(&r.tree).contains("Test.imported"));
}

#[test]
fn builder_finish_equals_builtin_snapshot() {
    assert_eq!(
        crate::builtin::builder().finish().fingerprint(),
        crate::builtin::snapshot().fingerprint()
    );
}
```

In `crates/leanr_syntax/src/parse.rs` tests:

```rust
#[test]
fn header_imports_are_extracted() {
    assert_eq!(
        parse_header_imports("import Foo\nimport Foo.Bar.Baz\n#check 1\n"),
        vec!["Foo".to_string(), "Foo.Bar.Baz".to_string()]
    );
    assert_eq!(parse_header_imports("#check 1\n"), Vec::<String>::new());
    assert_eq!(parse_header_imports("prelude\n#check 1\n"), Vec::<String>::new());
    // Malformed header: never panic, best-effort.
    let _ = parse_header_imports("import \u{0}\u{0}");
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_syntax leading_prim_registers builder_finish header_imports`
Expected: FAIL — methods/functions not defined.

- [ ] **Step 3: Implement**

`builtin/mod.rs`: rename the body of `snapshot()` into `pub fn builder() -> SnapshotBuilder` (everything up to but excluding `b.finish()`), then `pub fn snapshot() -> GrammarSnapshot { builder().finish() }`.

`grammar/mod.rs`, on `SnapshotBuilder` (mirror `leading2`/`trailing2` at mod.rs:790/814, minus the Node wrap — the prim arrives shaped):

```rust
/// Register an already-shaped leading production (e.g. an interpreted
/// imported `ParserDescr`, whose own `node` constructor supplied the
/// `Prim::Node` wrap). Harvests tokens and indexes like `leading2`.
pub fn leading_prim(&mut self, cat: &str, prim: Prim) {
    self.harvest_tokens(&prim);
    let c = self
        .categories
        .get_mut(cat)
        .expect("category registered before leading_prim");
    let idx = c.leading_parsers.len();
    for ft in index_entries(&prim) {
        c.leading.push((ft, idx));
    }
    c.leading_parsers.push(prim);
}

/// Trailing counterpart of [`Self::leading_prim`].
pub fn trailing_prim(&mut self, cat: &str, prim: Prim) {
    self.harvest_tokens(&prim);
    let c = self
        .categories
        .get_mut(cat)
        .expect("category registered before trailing_prim");
    let idx = c.trailing_parsers.len();
    for ft in index_entries(&prim) {
        c.trailing.push((ft, idx));
    }
    c.trailing_parsers.push(prim);
}
```

(Match the exact push/index pattern of `leading2` — read it first; if `leading2` pushes index entries differently, e.g. `Any` handling, copy that behavior verbatim.)

`parse.rs`:

```rust
/// Parse ONLY the module header and return the imported module names
/// (dotted). Total: any input yields a (possibly empty) list. The
/// header grammar is fixed (imports cannot depend on imports), so the
/// builtin snapshot is always sufficient — official Lean's
/// `parseHeader` has the same property.
pub fn parse_header_imports(src: &str) -> Vec<String> {
    let snap = crate::builtin::snapshot();
    let mut ps = Ps::new(src, &snap);
    // Mirror run_module's header phase exactly (parse.rs run_module):
    // parse snap.header_prim() if present, build the subtree, then walk
    // it for `Lean.Parser.Module.import` nodes, joining each import's
    // ident atoms with '.'.
    /* implementation mirrors run_module's header section; the walk:
       for each node of kind "Lean.Parser.Module.import", collect its
       identifier token text (the module name may be a dotted ident —
       one token in Lean's lexer) and push it. */
    todo!("mirror run_module header phase")
}
```

The implementer replaces the `todo!` by lifting the header phase from `run_module` (parse.rs:126 onward) — the header parse, event flattening, and tree build are all existing code paths; the only new logic is the tree walk extracting `Module.import` idents. If lifting proves awkward, an equally acceptable implementation is: run the header phase, build the partial tree, walk it. Do NOT parse the whole module.

Export in `lib.rs`: add `parse_header_imports` to the `pub use parse::{...}` list.

- [ ] **Step 4: Run tests**

Run: `cargo test -p leanr_syntax`
Expected: PASS, including the untouched `oracle_golden` corpus (the `builder()` refactor must be behavior-identical — the fingerprint test proves it).

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_syntax
git commit -m "feat(syntax): builtin builder seam, shaped-Prim registration, header-imports parse (M3b2a Task 4)"
```

---

### Task 5: `leanr_grammar` — the parser-alias table

`ParserDescr.const/unary/binary` carry alias names resolved against Lean's runtime alias registry (`Lean/Parser.lean:27-61`, `Extra.lean:337-351`, plus category-specific registrations). The table below is the deliberate **initial** set: core combinators, literal leaves, and position/ws checks. Everything else (category-specific aliases like `declModifiers`, `tacticSeq`; `recover`; `interpolatedStr`; `hexnum`; `rawIdent`; `hygieneInfo`) returns `None` → skip-and-record. The Mathlib ratchet tells us which to add next; adding one is a one-line table edit + a fixture.

**Files:**
- Create: `crates/leanr_grammar/src/alias.rs` (replacing stub)
- Test: unit tests in the same file

**Interfaces:**
- Produces (used by Task 6):
  ```rust
  pub(crate) enum AliasPrim {
      Const(Prim),          // arity 0 → this Prim
      Epsilon,              // arity 0, parses nothing (pp* spacing hints)
      Unary(fn(Prim) -> Prim),
      Transparent,          // arity 1, identity (pp grouping/indent hints)
      Binary(fn(Prim, Prim) -> Prim),
  }
  pub(crate) fn lookup(alias: &str) -> Option<AliasPrim>;
  ```

- [ ] **Step 1: Write the failing test**

In `crates/leanr_grammar/src/alias.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use leanr_syntax::grammar::Prim;

    #[test]
    fn core_aliases_map() {
        assert!(matches!(lookup("andthen"), Some(AliasPrim::Binary(_))));
        assert!(matches!(lookup("orelse"), Some(AliasPrim::Binary(_))));
        assert!(matches!(lookup("optional"), Some(AliasPrim::Unary(_))));
        assert!(matches!(lookup("many"), Some(AliasPrim::Unary(_))));
        assert!(matches!(lookup("ppSpace"), Some(AliasPrim::Epsilon)));
        assert!(matches!(lookup("ppIndent"), Some(AliasPrim::Transparent)));
        assert!(matches!(lookup("num"), Some(AliasPrim::Const(Prim::NumLit))));
        assert!(matches!(lookup("colGt"), Some(AliasPrim::Const(Prim::CheckColGt))));
        assert!(lookup("declModifiers").is_none()); // deliberately absent → skip
        assert!(lookup("nonsense").is_none());
    }

    #[test]
    fn binary_builders_build() {
        let Some(AliasPrim::Binary(f)) = lookup("andthen") else { panic!() };
        let p = f(Prim::Ident, Prim::NumLit);
        assert!(matches!(p, Prim::Seq(ref v) if v.len() == 2));
        let Some(AliasPrim::Binary(g)) = lookup("orelse") else { panic!() };
        assert!(matches!(g(Prim::Ident, Prim::NumLit), Prim::OrElse(_)));
    }
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_grammar`
Expected: FAIL — `lookup` undefined.

- [ ] **Step 3: Implement the table**

```rust
//! Lean parser-alias table (ORACLE-PORT of the `registerAlias` set in
//! Lean/Parser.lean:27-61 + Parser/Extra.lean:337-351). Deliberately
//! partial: aliases outside this table skip-and-record (M3b2a spec);
//! extend as the Mathlib ratchet demands. Arity is fixed by each
//! combinator's Lean type (Parser / Parser→Parser / Parser→Parser→Parser).

use std::sync::Arc;

use leanr_syntax::grammar::Prim;

pub(crate) enum AliasPrim {
    Const(Prim),
    Epsilon,
    Unary(fn(Prim) -> Prim),
    Transparent,
    Binary(fn(Prim, Prim) -> Prim),
}

fn seq2(a: Prim, b: Prim) -> Prim {
    // Flatten nested andthen chains like the builtin ports do.
    match a {
        Prim::Seq(mut v) => { v.push(b); Prim::Seq(v) }
        a => Prim::Seq(vec![a, b]),
    }
}
fn or2(a: Prim, b: Prim) -> Prim {
    match a {
        Prim::OrElse(mut v) => { v.push(b); Prim::OrElse(v) }
        a => Prim::OrElse(vec![a, b]),
    }
}

pub(crate) fn lookup(alias: &str) -> Option<AliasPrim> {
    use AliasPrim::*;
    Some(match alias {
        // binary combinators
        "andthen" => Binary(seq2),
        "orelse" => Binary(or2),
        // unary combinators
        "optional" => Unary(|p| Prim::Optional(Arc::new(p))),
        "many" => Unary(|p| Prim::Many(Arc::new(p))),
        "many1" => Unary(|p| Prim::Many1(Arc::new(p))),
        "many1Indent" => Unary(|p| Prim::Many1Indent(Arc::new(p))),
        "atomic" => Unary(|p| Prim::Atomic(Arc::new(p))),
        "lookahead" => Unary(|p| Prim::Lookahead(Arc::new(p))),
        "notFollowedBy" => Unary(|p| Prim::NotFollowedBy(Arc::new(p))),
        "group" => Unary(|p| Prim::Group(Arc::new(p))),
        "withPosition" => Unary(|p| Prim::WithPosition(Arc::new(p))),
        // literal leaves / token classes
        "num" => Const(Prim::NumLit),
        "str" => Const(Prim::StrLit),
        "char" => Const(Prim::CharLit),
        "name" => Const(Prim::NameLit),
        "scientific" => Const(Prim::ScientificLit),
        "ident" => Const(Prim::Ident),
        // position / whitespace checks
        "ws" => Const(Prim::CheckWsBefore),
        "noWs" => Const(Prim::CheckNoWsBefore),
        "colGt" => Const(Prim::CheckColGt),
        "colGe" => Const(Prim::CheckColGe),
        "colEq" => Const(Prim::CheckColEq),
        "lineEq" => Const(Prim::CheckLineEq),
        // pretty-printer hints: parse nothing / transparent
        "ppSpace" | "ppHardSpace" | "ppLine" | "ppAllowUngrouped"
        | "ppHardLineUnlessUngrouped" => Epsilon,
        "ppGroup" | "ppRealGroup" | "ppRealFill" | "ppIndent" | "ppDedent"
        | "ppDedentIfGrouped" | "patternIgnore" => Transparent,
        _ => return None,
    })
}
```

- [ ] **Step 4: Run tests**

Run: `cargo test -p leanr_grammar`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_grammar/src/alias.rs
git commit -m "feat(grammar): initial parser-alias table (M3b2a Task 5)"
```

---

### Task 6: `leanr_grammar` — the `ParserDescr` Expr interpreter

Walk a parser entry's constant: its declared **type** picks leading/trailing/raw (`mkParserOfConstant`, Extension.lean:255-276); its **value** is a `ParserDescr` constructor tree (13 constructors, tags per Init/Prelude.lean:5363-5449) walked structurally via `Store::expr_node`. Skip-and-record anything else.

**Files:**
- Create: `crates/leanr_grammar/src/descr.rs` (replacing stub; goldens live in its in-crate `#[cfg(test)]` module, against `NotaDep.olean`)

**Interfaces:**
- Consumes: `alias::lookup` (Task 5); `SnapshotBuilder::kind` for interning; `Store::{expr_node, to_name, str_at, nat_at}`; `ConstantInfo::{constant_val, Defn}`.
- Produces (used by Task 7):
  ```rust
  pub(crate) enum Interpreted { Leading(Prim), Trailing(Prim) }
  pub(crate) fn interpret(
      decl: NameId,
      consts: &HashMap<NameId, &ConstantInfo>,
      store: &Store,
      builder: &mut SnapshotBuilder,
  ) -> Result<Interpreted, SkipReason>;
  ```

- [ ] **Step 1: Write the failing golden test**

`crates/leanr_grammar/tests/descr_golden.rs` — goes through the public `assemble` (Task 7) would be circular, so test through a tiny `pub(crate)`-exposing seam: add `#[doc(hidden)] pub mod internal { pub use crate::descr::{interpret, Interpreted}; }` to `lib.rs` for test access (mirrors how fingerprint seams were exposed in M3b1), or make this an in-crate `#[cfg(test)]` module. Use the in-crate route:

In `crates/leanr_grammar/src/descr.rs`:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashMap;
    use std::path::Path;

    use leanr_kernel::bank::Store;
    use leanr_olean::{EntryScope, ModuleData, ParserEntry};
    use leanr_syntax::grammar::Prim;

    fn load_notadep() -> (Store, ModuleData) {
        let p = Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("../../tests/fixtures/syntax/import/NotaDep.olean");
        let mut st = Store::persistent();
        let md = ModuleData::parse(&std::fs::read(p).unwrap(), &mut st).unwrap();
        (st, md)
    }

    fn interpret_named(suffix: &str) -> Result<Interpreted, crate::SkipReason> {
        let (st, md) = load_notadep();
        let consts: HashMap<_, _> = md
            .constants
            .iter()
            .map(|c| (c.constant_val().name, c))
            .collect();
        let decl = md
            .parser_entries
            .iter()
            .find_map(|e| match (&e.scope, &e.entry) {
                (EntryScope::Global, ParserEntry::Parser { decl, .. })
                    if st.to_name(None, Some(*decl)).to_string().ends_with(suffix) =>
                {
                    Some(*decl)
                }
                _ => None,
            })
            .unwrap_or_else(|| panic!("no parser entry ending {suffix}"));
        let mut b = leanr_syntax::builtin::builder();
        interpret(decl, &consts, &st, &mut b)
    }

    #[test]
    fn infixl_interprets_as_trailing_node() {
        // infixl:65 " ⊕⊕ " ⇒ TrailingParserDescr =
        //   trailingNode `«term_⊕⊕_» 65 65 (symbol " ⊕⊕ " >> cat term 66)
        // (rbp 66 = p+1 for left-assoc; kind name is Lean's mangling —
        //  both already pinned by ImportMixfix.stx.jsonl.)
        let Interpreted::Trailing(p) = infixl().expect("interpreted") else {
            panic!("expected trailing")
        };
        fn infixl() -> Result<Interpreted, crate::SkipReason> {
            interpret_named("«term_⊕⊕_»")
        }
        let Prim::TrailingNode { prec, lhs_prec, body, .. } = p else {
            panic!("expected TrailingNode, got {p:?}")
        };
        assert_eq!((prec, lhs_prec), (65, 65));
        let Prim::Seq(items) = &*body else { panic!("expected Seq, got {body:?}") };
        assert!(matches!(&items[0], Prim::Symbol(s) if s == "⊕⊕"),
            "first item {:?}", items[0]);
        assert!(matches!(&items[1], Prim::Category { name, rbp } if name == "term" && *rbp == 66),
            "second item {:?}", items[1]);
    }

    #[test]
    fn prefix_interprets_as_leading_node() {
        let r = interpret_named("«term⋄⋄_»").expect("interpreted");
        let Interpreted::Leading(Prim::Node { prec, .. }) = r else {
            panic!("expected leading Node")
        };
        assert_eq!(prec, Some(100));
    }

    #[test]
    fn category_reference_interprets() {
        // syntax "wrap[" widget "]" : term — body contains cat widget.
        let r = interpret_named("wrap[").unwrap_or_else(|e| panic!("skip: {e:?}"));
        let Interpreted::Leading(prim) = r else { panic!("expected leading") };
        let dbg = format!("{prim:?}");
        assert!(dbg.contains("widget"), "no widget category in {dbg}");
    }
}
```

(The raw-`Parser` skip goes through the public API, so its assertion lives in Task 7's `import_golden.rs`, not here.)

Notes:
- The `interpret_named("wrap[")` lookup key: `syntax`-declared parsers get their kind/decl name from Lean's mangling; if `ends_with("wrap[")` doesn't match the actual decl name, run the Task 3 decode test with a debug print of all parser-entry decl names and use the real one (it is stable — pinned toolchain).
- Expected prec/rbp values are Lean's derivation; they are already visible in the committed `ImportMixfix.stx.jsonl` parse trees and in M3b1's `notation.rs` tables (`infixl:p` → `TrailingNode{prec:p, lhs_prec:p}`, rhs rbp `p+1`). If a golden assertion disagrees with the actual interpreted value AND the fixture dump agrees with the interpreter, fix the test; if the dump disagrees, fix the interpreter — the dump is the oracle.

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_grammar`
Expected: FAIL — `interpret` undefined.

- [ ] **Step 3: Implement the interpreter**

`crates/leanr_grammar/src/descr.rs` core (complete logic; helper bodies shown once):

```rust
//! Interprets a `ParserDescr` constant's term-bank value into a `Prim`.
//! ORACLE-PORT of `compileParserDescr`/`mkParserOfConstant`
//! (Lean/Parser/Extension.lean:255-304): structural walk only — no
//! evaluator. Anything that is not a literal constructor tree
//! skips-and-records (M3b2a spec §Error handling).

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use leanr_kernel::bank::{ExprId, NameId, Store};
use leanr_kernel::bank::terms::Node;
use leanr_kernel::decl::ConstantInfo;
use leanr_syntax::grammar::{Prim, SnapshotBuilder};

use crate::alias::{self, AliasPrim};
use crate::SkipReason;

pub(crate) enum Interpreted {
    Leading(Prim),
    Trailing(Prim),
}

struct Cx<'a> {
    store: &'a Store,
    consts: &'a HashMap<NameId, &'a ConstantInfo>,
    builder: &'a mut SnapshotBuilder,
    visiting: HashSet<NameId>,
}

pub(crate) fn interpret(
    decl: NameId,
    consts: &HashMap<NameId, &ConstantInfo>,
    store: &Store,
    builder: &mut SnapshotBuilder,
) -> Result<Interpreted, SkipReason> {
    let mut cx = Cx { store, consts, builder, visiting: HashSet::new() };
    cx.decl(decl)
}

impl Cx<'_> {
    /// Leading/trailing from the constant's declared TYPE
    /// (mkParserOfConstant): ParserDescr → leading,
    /// TrailingParserDescr → trailing, Parser/TrailingParser → raw skip.
    fn decl(&mut self, decl: NameId) -> Result<Interpreted, SkipReason> {
        let info = self.consts.get(&decl).ok_or(SkipReason::MissingConstant)?;
        let ty = self.const_head_name(info.constant_val().ty);
        let value = match info {
            ConstantInfo::Defn(d) => d.value,
            _ => return Err(SkipReason::UnsupportedShape("non-def parser constant")),
        };
        match ty.as_deref() {
            Some("Lean.ParserDescr") => Ok(Interpreted::Leading(self.descr(value)?)),
            Some("Lean.TrailingParserDescr") => Ok(Interpreted::Trailing(self.descr(value)?)),
            Some("Lean.Parser.Parser") | Some("Lean.Parser.TrailingParser") => {
                Err(SkipReason::RawParser)
            }
            _ => Err(SkipReason::UnsupportedShape("unexpected parser constant type")),
        }
    }

    /// The 13-constructor walk (tags per Init/Prelude.lean:5363-5449;
    /// dispatch is by CONSTRUCTOR NAME on the app-spine head, which is
    /// stable across tag renumbering).
    fn descr(&mut self, e: ExprId) -> Result<Prim, SkipReason> {
        let (head, args) = self.app_spine(e);
        let Some(head) = head else {
            return Err(SkipReason::UnsupportedShape("descr head is not a const"));
        };
        let name = self.name_string(head);
        match (name.as_str(), args.len()) {
            ("ParserDescr.const", 1) => {
                let alias = self.eval_name(args[0])?;
                match alias::lookup(&alias) {
                    Some(AliasPrim::Const(p)) => Ok(p),
                    Some(AliasPrim::Epsilon) => Ok(Prim::Seq(vec![])),
                    Some(_) => Err(SkipReason::UnsupportedShape("alias arity mismatch")),
                    None => Err(SkipReason::UnknownAlias(alias)),
                }
            }
            ("ParserDescr.unary", 2) => {
                let alias = self.eval_name(args[0])?;
                let inner = self.descr(args[1])?;
                match alias::lookup(&alias) {
                    Some(AliasPrim::Unary(f)) => Ok(f(inner)),
                    Some(AliasPrim::Transparent) => Ok(inner),
                    Some(_) => Err(SkipReason::UnsupportedShape("alias arity mismatch")),
                    None => Err(SkipReason::UnknownAlias(alias)),
                }
            }
            ("ParserDescr.binary", 3) => {
                let alias = self.eval_name(args[0])?;
                let (a, b) = (self.descr(args[1])?, self.descr(args[2])?);
                match alias::lookup(&alias) {
                    Some(AliasPrim::Binary(f)) => Ok(f(a, b)),
                    Some(_) => Err(SkipReason::UnsupportedShape("alias arity mismatch")),
                    None => Err(SkipReason::UnknownAlias(alias)),
                }
            }
            ("ParserDescr.node", 3) => {
                let kind = self.intern_kind(args[0])?;
                let prec = self.eval_prec(args[1])?;
                Ok(Prim::Node { kind, prec: Some(prec), body: Arc::new(self.descr(args[2])?) })
            }
            ("ParserDescr.trailingNode", 4) => {
                let kind = self.intern_kind(args[0])?;
                let prec = self.eval_prec(args[1])?;
                let lhs_prec = self.eval_prec(args[2])?;
                Ok(Prim::TrailingNode { kind, prec, lhs_prec, body: Arc::new(self.descr(args[3])?) })
            }
            ("ParserDescr.symbol", 1) => {
                Ok(Prim::Symbol(trim_symbol(&self.eval_string(args[0])?)))
            }
            ("ParserDescr.nonReservedSymbol", 2) => {
                Ok(Prim::NonReservedSymbol(trim_symbol(&self.eval_string(args[0])?)))
            }
            ("ParserDescr.cat", 2) => Ok(Prim::Category {
                name: self.eval_name(args[0])?,
                rbp: self.eval_prec(args[1])?,
            }),
            ("ParserDescr.parser", 1) => {
                // Reference to another parser decl: recurse (cycle-guarded).
                let target = self.eval_name_id(args[0])?;
                if !self.visiting.insert(target) {
                    return Err(SkipReason::Cycle);
                }
                let r = self.decl(target);
                self.visiting.remove(&target);
                match r? {
                    Interpreted::Leading(p) | Interpreted::Trailing(p) => Ok(p),
                }
            }
            ("ParserDescr.nodeWithAntiquot", 3) => {
                // Antiquot behavior itself is M3b2b; the real-source path
                // is the plain node (compileParserDescr wraps only for
                // quotation contexts).
                let kind = self.intern_kind(args[1])?;
                Ok(Prim::Node { kind, prec: None, body: Arc::new(self.descr(args[2])?) })
            }
            ("ParserDescr.sepBy", 4) | ("ParserDescr.sepBy1", 4) => {
                let item = Arc::new(self.descr(args[0])?);
                let sep = trim_symbol(&self.eval_string(args[1])?);
                // args[2] is psep (the separator PARSER — usually
                // `symbol sep`); leanr's SepBy carries the separator
                // token directly, matching the builtin ports.
                let allow_trailing = self.eval_bool(args[3])?;
                Ok(if name.ends_with('1') {
                    Prim::SepBy1 { item, sep, allow_trailing }
                } else {
                    Prim::SepBy { item, sep, allow_trailing }
                })
            }
            ("ParserDescr.unicodeSymbol", 3) => {
                // Parses either form; tokens for both are harvested.
                let uni = trim_symbol(&self.eval_string(args[0])?);
                let ascii = trim_symbol(&self.eval_string(args[1])?);
                Ok(Prim::OrElse(vec![Prim::Symbol(uni), Prim::Symbol(ascii)]))
            }
            _ => Err(SkipReason::UnsupportedShape("unknown ParserDescr constructor")),
        }
    }
}
```

Helpers on `Cx` (complete these; all total, all skip on surprise):

```rust
/// Uncurry an application spine: `App(App(Const c, a), b)` → (c, [a, b]).
/// Walks through `Mdata` transparently. Returns head const NameId.
fn app_spine(&self, e: ExprId) -> (Option<NameId>, Vec<ExprId>) { /* loop on
    self.store.expr_node(None, id): App{f,arg} pushes arg and recurses on f;
    Const{name: Some(n), ..} terminates; Mdata unwraps; else (None, vec![]).
    Reverse args at the end. */ }

fn name_string(&self, n: NameId) -> String {
    self.store.to_name(None, Some(n)).to_string()
}

/// Evaluate a `Name`-typed literal expr: Name.anonymous /
/// Name.str p s / Name.num p n / Name.mkStr1..mkStr8 / Name.mkSimple /
/// Name.mkNum. Anything else → UnsupportedShape("name literal").
fn eval_name_id(&mut self, e: ExprId) -> Result<NameId, SkipReason> { ... }
fn eval_name(&mut self, e: ExprId) -> Result<String, SkipReason> {
    Ok(self.name_string(self.eval_name_id(e)?))
}

/// Expr literal leaves: Node::LitStr → str_at; Node::LitNat → nat_at
/// (skip if > u32::MAX for precs); Bool.true/Bool.false consts.
fn eval_string(&self, e: ExprId) -> Result<String, SkipReason> { ... }
fn eval_prec(&self, e: ExprId) -> Result<u32, SkipReason> { ... }
fn eval_bool(&self, e: ExprId) -> Result<bool, SkipReason> { ... }

/// Kind names intern via the builder (single interner for the whole
/// assembled snapshot).
fn intern_kind(&mut self, e: ExprId) -> Result<leanr_syntax::kind::SyntaxKind, SkipReason> {
    let name = self.eval_name(e)?;
    Ok(self.builder.kind(&name))
}
```

And the free helper `fn trim_symbol(s: &str) -> String { s.trim().to_string() }` (Lean symbol strings carry pretty-print padding — `" ⊕⊕ "`; the token is the trimmed core, exactly as M3b1's `trim_lean_symbol` does — reuse that logic's semantics; if `notation.rs::trim_lean_symbol` is `pub(crate)`, prefer promoting it to `pub` in `leanr_syntax::grammar::notation` and calling it instead of duplicating).

**Empirical pins for this task** (fixture-driven, like every oracle port):
- `eval_name_id` must handle whatever Name-literal encoding the elaborator actually emitted into `NotaDep.olean` (`Name.mkStr2`-style helper apps vs `Name.str` ctor chains vs `Nat`-indexed). Run the golden test; extend the match until the three goldens pass; leave a comment enumerating the observed shapes.
- `eval_prec`: Lean encodes small Nat literals as `Node::LitNat`; if `NotaDep`'s precs arrive as `OfNat.ofNat`-wrapped apps instead, unwrap that one shape (head `OfNat.ofNat`, third arg is the literal) and comment it.

- [ ] **Step 4: Run tests**

Run: `cargo test -p leanr_grammar`
Expected: PASS (3 goldens + alias tests).

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_grammar
git commit -m "feat(grammar): ParserDescr Expr interpreter with skip-and-record (M3b2a Task 6)"
```

---

### Task 7: `leanr_grammar` — snapshot assembly + hermetic import gate

Fold a loaded closure's entries into `builtin::builder()` in closure order; global entries only; scoped → recorded `ScopedInactive`; uninterpretable parsers → recorded, **tokens still folded** (token entries are separate `.token` entries, so this falls out naturally — assert it). Then the hermetic CI gate: parse each importer fixture under the assembled snapshot and compare byte round-trip + canonical trees against the committed oracle dumps.

**Files:**
- Modify: `crates/leanr_grammar/src/assemble.rs` (replace `todo!`)
- Test: `crates/leanr_grammar/tests/import_golden.rs`

**Interfaces:**
- Consumes: Task 3 types, Task 4 builder seams, Task 6 `interpret`.
- Produces: `pub fn assemble(modules: &[(Arc<Name>, ModuleData)], store: &Store) -> AssembledGrammar` — the one entry point Tasks 8 and 9 (CLI, sweep) call.

- [ ] **Step 1: Write the failing tests**

`crates/leanr_grammar/tests/import_golden.rs`:

```rust
use std::path::{Path, PathBuf};
use std::sync::Arc;

use leanr_grammar::{assemble, SkipReason};
use leanr_kernel::bank::Store;
use leanr_olean::ModuleData;

fn dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/syntax/import")
}

/// Hermetic single-module "closure": NotaDep only. Importer fixtures
/// avoid Init-declared notation, so folding just NotaDep matches the
/// oracle (corpus self-containment discipline — see design spec).
fn notadep_grammar() -> (Store, leanr_grammar::AssembledGrammar) {
    let mut st = Store::persistent();
    let bytes = std::fs::read(dir().join("NotaDep.olean")).unwrap();
    let md = ModuleData::parse(&bytes, &mut st).unwrap();
    let name = Arc::new(leanr_kernel::name::Name::Anonymous); // display-only
    let g = assemble(&[(name, md)], &st);
    (st, g)
}

#[test]
fn importers_parse_green_against_oracle_dumps() {
    let (_st, g) = notadep_grammar();
    for stem in ["ImportMixfix", "ImportMunch", "ImportCat", "ImportOverload"] {
        let src = std::fs::read_to_string(dir().join(format!("{stem}.lean"))).unwrap();
        let want = std::fs::read_to_string(dir().join(format!("{stem}.stx.jsonl"))).unwrap();
        let r = leanr_syntax::parse_module(&src, &g.snapshot);
        assert_eq!(r.tree.text(), src, "{stem}: byte round-trip");
        assert!(r.errors.is_empty(), "{stem}: {:?}", r.errors);
        let got = leanr_syntax::canon::canon_jsonl(&r.tree);
        for (i, (g_line, w_line)) in got.lines().zip(want.lines()).enumerate() {
            assert_eq!(g_line, w_line, "{stem} line {i}");
        }
        assert_eq!(got.lines().count(), want.lines().count(), "{stem} line count");
    }
}

#[test]
fn scoped_entry_is_skipped_and_recorded() {
    let (st, g) = notadep_grammar();
    assert!(
        g.skipped.iter().any(|s| s.reason == SkipReason::ScopedInactive),
        "scoped ⊖⊖ should be recorded: {:?}",
        g.skipped
    );
    // And its parser must NOT be active: ⊖⊖ has no term production.
    let r = leanr_syntax::parse_module("#check 1 ⊖⊖ 2\n", &g.snapshot);
    assert!(!r.errors.is_empty(), "scoped notation must not parse");
    let _ = st;
}

#[test]
fn raw_parser_entry_skips_but_tokens_fold() {
    let mut st = Store::persistent();
    let bytes = std::fs::read(dir().join("NotaDepMeta.olean")).unwrap();
    let md = ModuleData::parse(&bytes, &mut st).unwrap();
    let name = Arc::new(leanr_kernel::name::Name::Anonymous);
    let g = assemble(&[(name, md)], &st);
    assert!(
        g.skipped.iter().any(|s| s.reason == SkipReason::RawParser
            && s.decl.ends_with("rawWidget")),
        "raw Parser skip missing: {:?}",
        g.skipped
    );
}

#[test]
fn fingerprint_distinguishes_import_sets() {
    let builtin_fp = leanr_syntax::builtin::snapshot().fingerprint();
    let (_st, g) = notadep_grammar();
    assert_ne!(g.snapshot.fingerprint(), builtin_fp);
    // Deterministic across assemblies.
    let (_st2, g2) = notadep_grammar();
    assert_eq!(g.snapshot.fingerprint(), g2.snapshot.fingerprint());
}

#[test]
fn samefile_overlay_composes_on_imported_base() {
    // ImportOverload declares infixl " ⊕⊕ " same-file over the imported
    // one — already covered by the oracle-dump test above; this pins
    // the *mechanism*: parse must succeed with zero errors, proving
    // M3b1 threading runs on an assembled (non-builtin) base.
    let (_st, g) = notadep_grammar();
    let src = std::fs::read_to_string(dir().join("ImportOverload.lean")).unwrap();
    let r = leanr_syntax::parse_module(&src, &g.snapshot);
    assert!(r.errors.is_empty(), "{:?}", r.errors);
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_grammar --test import_golden`
Expected: FAIL — `assemble` is `todo!`.

- [ ] **Step 3: Implement assembly**

Replace the `assemble` body in `crates/leanr_grammar/src/assemble.rs`:

```rust
pub fn assemble(modules: &[(Arc<Name>, ModuleData)], store: &Store) -> AssembledGrammar {
    // One constants map across the closure (parser decls may reference
    // descr constants from any dependency).
    let consts: HashMap<NameId, &ConstantInfo> = modules
        .iter()
        .flat_map(|(_, md)| md.constants.iter())
        .map(|c| (c.constant_val().name, c))
        .collect();

    let mut b = leanr_syntax::builtin::builder();
    let mut skipped = Vec::new();
    let name_of = |id: NameId| store.to_name(None, Some(id)).to_string();

    for (_module, md) in modules {
        for entry in &md.parser_entries {
            let e = match &entry.scope {
                EntryScope::Global => &entry.entry,
                EntryScope::Scoped(_) => {
                    if let ParserEntry::Parser { decl, .. } = &entry.entry {
                        skipped.push(SkippedEntry {
                            decl: name_of(*decl),
                            reason: SkipReason::ScopedInactive,
                        });
                    }
                    // Scoped token/category/kind entries are likewise
                    // inactive until M3b3; skip silently (nothing to name).
                    continue;
                }
            };
            match e {
                ParserEntry::Token(t) => b.token(t),
                ParserEntry::Kind(k) => {
                    b.kind(&name_of(*k));
                }
                ParserEntry::Category { cat, behavior, .. } => {
                    b.category(&name_of(*cat), map_behavior(*behavior));
                }
                ParserEntry::Parser { cat, decl } => {
                    let cat_name = name_of(*cat);
                    match crate::descr::interpret(*decl, &consts, store, &mut b) {
                        Ok(crate::descr::Interpreted::Leading(p)) => {
                            b.category(&cat_name, Default::default()); // ensure exists (idempotent)
                            b.leading_prim(&cat_name, p);
                        }
                        Ok(crate::descr::Interpreted::Trailing(p)) => {
                            b.category(&cat_name, Default::default());
                            b.trailing_prim(&cat_name, p);
                        }
                        Err(reason) => skipped.push(SkippedEntry {
                            decl: name_of(*decl),
                            reason,
                        }),
                    }
                }
            }
        }
    }
    AssembledGrammar { snapshot: b.finish(), skipped }
}

fn map_behavior(b: leanr_olean::CatBehavior) -> leanr_syntax::grammar::LeadingIdentBehavior {
    use leanr_syntax::grammar::LeadingIdentBehavior as L;
    match b {
        leanr_olean::CatBehavior::Default => L::Default,
        leanr_olean::CatBehavior::Symbol => L::Symbol,
        leanr_olean::CatBehavior::Both => L::Both,
    }
}
```

(If `SnapshotBuilder::category` takes `LeadingIdentBehavior` by value with no `Default` impl visible, use `LeadingIdentBehavior::Default` explicitly. Lean guarantees a category entry precedes its parsers in the entry stream — `addParserCategory` registers the entry at declaration — so the ensure-exists call is belt-and-braces for out-of-closure-order references, matching `Entry.category`'s own "insert iff not present".)

- [ ] **Step 4: Run tests**

Run: `cargo test -p leanr_grammar`
Expected: PASS — all five gate tests. Any canonical-tree mismatch is a real interpreter/derivation bug: diff `got` vs `want` line by line; the usual suspects are kind-name mangling (must match Lean's dumped names byte-for-byte) and placeholder rbp values.

- [ ] **Step 5: Run the full workspace**

Run: `cargo test --workspace`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_grammar
git commit -m "feat(grammar): closure entry folding + hermetic import-corpus gate (M3b2a Task 7)"
```

---

### Task 8: CLI — import-aware `leanr parse`

`Parse` gains `--path` (same semantics as `Check`: repeatable roots, combined with `LEAN_PATH` and `lean --print-libdir` via the existing `discover_roots`) and `--verbose` (list skipped entries to stderr). With no resolvable roots or no imports: today's builtin behavior, unchanged.

**Files:**
- Modify: `crates/leanr_cli/src/main.rs` (Command::Parse fields + `parse_cmd`), `crates/leanr_cli/Cargo.toml` (add `leanr_grammar` dep)
- Test: `crates/leanr_cli/tests/parse_imports.rs` (new; assert_cmd like existing CLI tests)

**Interfaces:**
- Consumes: `leanr_syntax::parse_header_imports`, `leanr_olean::{SearchPath, load_closure}`, `leanr_grammar::assemble`, existing `discover_roots`/`parse_module_name`.
- Produces: `leanr parse <file> [--dump] [--verbose] [--path <root>]...`

- [ ] **Step 1: Write the failing test**

`crates/leanr_cli/tests/parse_imports.rs` (hermetic: the fixture dir contains the stub `Init.olean`, so the closure `[Init, NotaDep]` resolves without a toolchain):

```rust
use assert_cmd::Command;
use std::path::{Path, PathBuf};

fn fixture_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/syntax/import")
}

#[test]
fn parse_with_path_uses_imported_notation() {
    let dir = fixture_dir();
    let want = std::fs::read_to_string(dir.join("ImportMixfix.stx.jsonl")).unwrap();
    let out = Command::cargo_bin("leanr")
        .unwrap()
        .args(["parse", "--dump", "--path"])
        .arg(&dir)
        .arg(dir.join("ImportMixfix.lean"))
        .env_remove("LEAN_PATH")
        .assert()
        .success();
    let stdout = String::from_utf8(out.get_output().stdout.clone()).unwrap();
    // Dump includes the header line; oracle dump includes it too.
    assert_eq!(stdout, want);
}

#[test]
fn parse_without_path_keeps_builtin_behavior() {
    // No --path and no LEAN_PATH containing NotaDep: import unresolved →
    // must still exit successfully IF the file parses under builtins;
    // ImportMixfix does NOT (uses ⊕⊕), so expect parse errors reported.
    let dir = fixture_dir();
    Command::cargo_bin("leanr")
        .unwrap()
        .args(["parse"])
        .arg(dir.join("ImportMixfix.lean"))
        .env_remove("LEAN_PATH")
        .assert()
        .failure();
}

#[test]
fn verbose_lists_skipped_entries() {
    let dir = fixture_dir();
    // NotaDepMeta has a raw @[term_parser]; importing it must WARN, not fail.
    std::fs::write(
        dir.join("../../../..").join("target/ImportRawTmp.lean"),
        "import NotaDepMeta\n#check 1\n",
    )
    .unwrap();
    let tmp = dir.join("../../../..").join("target/ImportRawTmp.lean");
    let out = Command::cargo_bin("leanr")
        .unwrap()
        .args(["parse", "--verbose", "--path"])
        .arg(&dir)
        .arg(&tmp)
        .env_remove("LEAN_PATH")
        .assert();
    // NotaDepMeta imports Lean (unresolvable hermetically) → this test
    // asserts the ERROR path is clean: exit failure with a module-not-
    // found message naming Lean, not a panic.
    let stderr = String::from_utf8(out.get_output().stderr.clone()).unwrap();
    assert!(stderr.contains("Lean"), "stderr: {stderr}");
}
```

(Adjust the tmp-file plumbing to `tempfile::TempDir` — already a `leanr_cli` dev-dependency — rather than writing into `target/`; the test body above shows intent, the implementer should use `TempDir` idiomatically. The third test pins the unresolvable-import error path; the happy skipped-entry listing is already unit-covered in Task 7.)

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_cli --test parse_imports`
Expected: FAIL — unknown `--path` for parse.

- [ ] **Step 3: Implement**

`Cargo.toml`: add `leanr_grammar = { version = "0.1.0", path = "../leanr_grammar" }`.

`main.rs` — extend the variant (mirror `Check`'s `path` arg docs):

```rust
Parse {
    file: PathBuf,
    /// Print the canonical JSONL tree dump.
    #[arg(long)]
    dump: bool,
    /// Olean search roots for resolving the file's imports (repeatable,
    /// highest priority first; combined with LEAN_PATH and
    /// `lean --print-libdir`, like `check`). Without any resolvable
    /// root the file parses under the builtin grammar only.
    #[arg(long = "path")]
    path: Vec<PathBuf>,
    /// List imported parser entries that were skipped (raw parsers,
    /// unknown aliases, scoped) to stderr.
    #[arg(long)]
    verbose: bool,
},
```

Dispatch: `Command::Parse { file, dump, path, verbose } => parse_cmd(&file, dump, path, verbose)`.

`parse_cmd` — replace the snapshot line (main.rs:282):

```rust
fn parse_cmd(file: &Path, dump: bool, path: Vec<PathBuf>, verbose: bool) -> ExitCode {
    // ... existing read + UTF-8 decode unchanged ...
    let imports = leanr_syntax::parse_header_imports(&src);
    let assembled; // keep alive for &snapshot borrow
    let snap = if imports.is_empty() {
        None
    } else {
        let roots = discover_roots(path);
        if roots.is_empty() {
            None // no roots: builtin-only (documented fallback)
        } else {
            let sp = leanr_olean::SearchPath::new(roots);
            let targets: Vec<_> = imports.iter().map(|m| parse_module_name(m)).collect();
            let mut st = leanr_kernel::bank::Store::persistent();
            match leanr_olean::load_closure(&sp, &targets, &mut st) {
                Ok(loaded) => {
                    assembled = leanr_grammar::assemble(&loaded, &st);
                    if verbose {
                        for s in &assembled.skipped {
                            eprintln!("skipped parser entry {} ({:?})", s.decl, s.reason);
                        }
                    }
                    Some(&assembled.snapshot)
                }
                Err(e) => {
                    eprintln!("error[E0306]: cannot load imports: {e}");
                    return ExitCode::FAILURE;
                }
            }
        }
    };
    let builtin;
    let snap = match snap {
        Some(s) => s,
        None => { builtin = leanr_syntax::builtin::snapshot(); &builtin }
    };
    let result = leanr_syntax::parse_module(&src, snap);
    // ... existing dump/error rendering unchanged ...
}
```

(Pick the next free `E03xx` error code by grepping `main.rs` for `E03`; `E0306` assumed free — adjust if taken. The unresolved-imports policy is **fail loudly** when roots were given but the closure doesn't resolve — silently falling back to builtins would mis-parse and "succeed".)

- [ ] **Step 4: Run tests**

Run: `cargo test -p leanr_cli`
Expected: PASS (new + existing CLI tests; existing `parse_cmd` callers in tests use the no-import fixtures, which hit the unchanged builtin path).

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_cli
git commit -m "feat(cli): import-aware leanr parse via --path/LEAN_PATH (M3b2a Task 8)"
```

---

### Task 9: Mathlib sweep + pass-list ratchet (local, `--ignored`)

The honest coverage gate: sweep every `.lean` file in the fetched Mathlib closure, compare against cached oracle dumps, and ratchet a checked-in pass-list. Oracle dumps use the **elaborating** dumper (grammar can grow mid-file in arbitrary real files); cached per `(oracle-githash, blake3(file))` so only the first run pays elaboration.

**Files:**
- Test: `crates/leanr_grammar/tests/mathlib_sweep.rs` (new, `#[ignore]`)
- Create: `tests/fixtures/syntax/mathlib-passlist.txt` (empty placeholder header line; populated by Task 10)
- Modify: `mise.toml` (tasks `parse:mathlib`, `passlist:update`)

**Interfaces:**
- Consumes: env `LEANR_MATHLIB_DIR` (the `.mathlib` checkout), `LEANR_OLEAN_PATH` (Lake's resolved `LEAN_PATH`), optional `LEANR_SWEEP_LIMIT` (int, smoke runs), `LEANR_PASSLIST_UPDATE=1` (rewrite mode); `assemble` + `load_closure` + `parse_header_imports`.
- Produces: the ratchet gate + `tests/fixtures/syntax/mathlib-passlist.txt` (sorted, one path-relative-to-`.mathlib` per line, `#`-comment header).

- [ ] **Step 1: Write the sweep test (it IS the deliverable; no TDD split — the "failing" state is the empty pass-list)**

`crates/leanr_grammar/tests/mathlib_sweep.rs`:

```rust
//! Local-only Mathlib parse sweep + pass-list ratchet (M3b2a
//! acceptance; grows into M3b3's 100% gate). Needs `mise run
//! mathlib:fetch` first. Run via `mise run parse:mathlib`.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::Arc;

use leanr_grammar::assemble;
use leanr_kernel::bank::Store;
use leanr_olean::SearchPath;

fn passlist_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/syntax/mathlib-passlist.txt")
}

/// Oracle dump with per-file cache under target/leanr-stx-cache/.
/// Key: (oracle githash, blake3 of file bytes). Dumper: the elaborating
/// one — arbitrary real files may grow the grammar mid-file.
fn oracle_dump(mathlib: &Path, lean_path: &str, githash: &str, file: &Path) -> Option<String> {
    let bytes = std::fs::read(file).ok()?;
    let key = format!("{githash}-{}", blake3::hash(&bytes).to_hex());
    let cache = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../target/leanr-stx-cache")
        .join(&key);
    if let Ok(hit) = std::fs::read_to_string(&cache) {
        return Some(hit);
    }
    let dumper = Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures/syntax/dump_syntax_elab.lean");
    let out = Command::new("lean")
        .env("LEAN_PATH", lean_path)
        .current_dir(mathlib)
        .arg("--run")
        .arg(&dumper)
        .arg(file)
        .output()
        .ok()?;
    if !out.status.success() {
        return None; // oracle itself failed on this file → not sweepable yet
    }
    let s = String::from_utf8(out.stdout).ok()?;
    std::fs::create_dir_all(cache.parent().unwrap()).ok()?;
    std::fs::write(&cache, &s).ok();
    Some(s)
}

#[test]
#[ignore = "needs .mathlib (mise run mathlib:fetch); run via mise run parse:mathlib"]
fn mathlib_sweep_ratchet() {
    let mathlib = PathBuf::from(std::env::var("LEANR_MATHLIB_DIR").expect("LEANR_MATHLIB_DIR"));
    let lean_path = std::env::var("LEANR_OLEAN_PATH").expect("LEANR_OLEAN_PATH");
    let githash = std::fs::read_to_string(
        Path::new(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures/oracle-githash.txt"),
    )
    .expect("oracle-githash.txt (mise run fixtures:regen)")
    .trim()
    .to_string();
    let limit: usize = std::env::var("LEANR_SWEEP_LIMIT")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(usize::MAX);

    let roots: Vec<PathBuf> = lean_path.split(':').filter(|s| !s.is_empty()).map(Into::into).collect();
    let sp = SearchPath::new(roots);

    // Enumerate: Mathlib/**/*.lean + each package's source tree.
    let mut files: Vec<PathBuf> = Vec::new();
    collect_lean_files(&mathlib.join("Mathlib"), &mut files);
    if let Ok(pkgs) = std::fs::read_dir(mathlib.join(".lake/packages")) {
        for p in pkgs.flatten() {
            collect_lean_files(&p.path(), &mut files);
        }
    }
    files.sort();
    files.truncate(limit);

    // Snapshot cache keyed by the file's import list.
    let mut snap_cache: BTreeMap<Vec<String>, Option<Arc<leanr_syntax::grammar::GrammarSnapshot>>> =
        BTreeMap::new();

    let mut green: Vec<String> = Vec::new();
    for file in &files {
        let rel = file.strip_prefix(&mathlib).unwrap_or(file).display().to_string();
        let Ok(src) = std::fs::read_to_string(file) else { continue };
        let imports = leanr_syntax::parse_header_imports(&src);
        let snap = snap_cache.entry(imports.clone()).or_insert_with(|| {
            let mut st = Store::persistent();
            let targets: Vec<_> = imports
                .iter()
                .map(|m| dotted_to_name(m))
                .collect();
            leanr_olean::load_closure(&sp, &targets, &mut st)
                .ok()
                .map(|loaded| Arc::new(assemble(&loaded, &st).snapshot))
        });
        let Some(snap) = snap else { continue };
        let r = leanr_syntax::parse_module(&src, snap);
        if r.tree.text() != src || !r.errors.is_empty() {
            continue;
        }
        let Some(want) = oracle_dump(&mathlib, &lean_path, &githash, file) else { continue };
        if leanr_syntax::canon::canon_jsonl(&r.tree) == want {
            green.push(rel);
        }
    }
    green.sort();

    let committed: Vec<String> = std::fs::read_to_string(passlist_path())
        .unwrap_or_default()
        .lines()
        .filter(|l| !l.is_empty() && !l.starts_with('#'))
        .map(String::from)
        .collect();

    let regressions: Vec<_> = committed.iter().filter(|f| !green.contains(f)).collect();
    let newly_green: Vec<_> = green.iter().filter(|f| !committed.contains(f)).collect();
    eprintln!(
        "sweep: {} files, {} green, {} on pass-list, {} regressions, {} newly green",
        files.len(), green.len(), committed.len(), regressions.len(), newly_green.len()
    );

    if std::env::var("LEANR_PASSLIST_UPDATE").as_deref() == Ok("1") {
        let mut out = String::from(
            "# Mathlib-closure files that parse oracle-green (M3b2a ratchet).\n\
             # Regenerate: mise run passlist:update. NEVER hand-edit to hide a regression.\n",
        );
        for f in &green {
            out.push_str(f);
            out.push('\n');
        }
        std::fs::write(passlist_path(), out).unwrap();
        return;
    }
    assert!(regressions.is_empty(), "pass-list regressions: {regressions:#?}");
}

fn collect_lean_files(dir: &Path, out: &mut Vec<PathBuf>) {
    let Ok(rd) = std::fs::read_dir(dir) else { return };
    for e in rd.flatten() {
        let p = e.path();
        if p.is_dir() {
            // Skip build dirs — only source trees.
            if p.file_name().is_some_and(|n| n == ".lake" || n == "build") {
                continue;
            }
            collect_lean_files(&p, out);
        } else if p.extension().is_some_and(|x| x == "lean") {
            out.push(p);
        }
    }
}

fn dotted_to_name(dotted: &str) -> Arc<leanr_kernel::name::Name> {
    use leanr_kernel::name::Name;
    let mut n = Arc::new(Name::Anonymous);
    for part in dotted.split('.') {
        n = Arc::new(Name::Str { parent: n, part: part.to_string() });
    }
    n
}
```

Notes: `blake3` must be added to `leanr_grammar`'s `[dev-dependencies]` (already in the workspace tree via `leanr_syntax`, license-clean). `dotted_to_name` duplicates the CLI helper because `leanr_cli` is a bin crate — three lines, acceptable; if `Name::Str`'s field names differ (check `leanr_kernel::name`), match the real definition. Also verify `collect_lean_files` skips the `Mathlib.lean` umbrella and package build dirs correctly on the first run.

- [ ] **Step 2: Create the placeholder pass-list**

`tests/fixtures/syntax/mathlib-passlist.txt`:

```
# Mathlib-closure files that parse oracle-green (M3b2a ratchet).
# Regenerate: mise run passlist:update. NEVER hand-edit to hide a regression.
```

- [ ] **Step 3: Add mise tasks**

In `mise.toml` (after `check:mathlib`):

```toml
[tasks."parse:mathlib"]
description = "M3b2a Mathlib parse sweep vs the pass-list ratchet (needs mathlib:fetch). LEANR_SWEEP_LIMIT=N for a smoke run."
run = "sh -c 'LEANR_MATHLIB_DIR=\"$PWD/.mathlib\" LEANR_OLEAN_PATH=\"$(cd .mathlib && lake env printenv LEAN_PATH)\" cargo test --release -p leanr_grammar --test mathlib_sweep -- --ignored --nocapture'"

[tasks."passlist:update"]
description = "Rewrite tests/fixtures/syntax/mathlib-passlist.txt from a fresh sweep (review the diff before committing)"
run = "sh -c 'LEANR_PASSLIST_UPDATE=1 LEANR_MATHLIB_DIR=\"$PWD/.mathlib\" LEANR_OLEAN_PATH=\"$(cd .mathlib && lake env printenv LEAN_PATH)\" cargo test --release -p leanr_grammar --test mathlib_sweep -- --ignored --nocapture'"
```

- [ ] **Step 4: Smoke-run the sweep**

Run: `LEANR_SWEEP_LIMIT=25 mise run parse:mathlib`
Expected: completes without panics; prints `sweep: 25 files, N green, 0 on pass-list, 0 regressions, N newly green`. N may be small — that's honest data, not failure. Debug any *panic* (never acceptable: the sweep must be total).

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_grammar tests/fixtures/syntax/mathlib-passlist.txt mise.toml
git commit -m "test(grammar): Mathlib parse sweep + pass-list ratchet harness (M3b2a Task 9)"
```

---

### Task 10: M3b2a final gate

Run every gate, populate the initial pass-list, record acceptance.

**Files:**
- Modify: `tests/fixtures/syntax/mathlib-passlist.txt` (populated), `docs/superpowers/specs/2026-07-16-m3b2a-imported-extensions-design.md` (acceptance recorded line)

- [ ] **Step 1: Full hermetic gates**

Run: `cargo test --workspace && mise run lint && mise run lint:deps`
Expected: all PASS.

- [ ] **Step 2: Parser acceptance script**

Run: `mise run parse:acceptance`
Expected: all 4 steps green (fresh oracle dumps match committed, `leanr_syntax` release tests, CLI dump diffs, fuzz smoke). If step [1]/[3] iterate only the flat fixture dir, extend `scripts/parse-acceptance.sh` with a fifth step that re-dumps the `import/` corpus (same commands as the Task 2 regen lines) and diffs `leanr parse --dump --path tests/fixtures/syntax/import <f>` against each committed `Import*.stx.jsonl`.

- [ ] **Step 3: Fuzz smoke both targets**

Run: `mise run fuzz`
Expected: no findings in 60s each (`module_data` now exercising entry decode; `parse_module` unchanged).

- [ ] **Step 4: Populate the initial pass-list (the acceptance number)**

Run: `mise run passlist:update` (full sweep — first run pays oracle elaboration; expect hours, cached thereafter)
Then: `mise run parse:mathlib`
Expected: second run is green against the fresh pass-list, 0 regressions. Review `git diff --stat tests/fixtures/syntax/mathlib-passlist.txt` — the acceptance bar is a **non-trivial** list including files that use imported notation (spot-check a few entries are real Mathlib/Batteries modules, not only `.lake` stubs).

- [ ] **Step 5: Record acceptance in the spec**

Append to the spec's Goal section (mirroring M3a/M3b1's "complete as of" convention), with the real numbers:

```markdown
**Acceptance recorded (2026-MM-DD):** initial sweep over the pinned
Mathlib closure: NNNN files swept, NNN oracle-green on the committed
pass-list (commit <sha>); hermetic import corpus + all prior gates
green.
```

- [ ] **Step 6: Commit**

```bash
git add tests/fixtures/syntax/mathlib-passlist.txt scripts/parse-acceptance.sh \
        docs/superpowers/specs/2026-07-16-m3b2a-imported-extensions-design.md
git commit -m "test(grammar): populate initial Mathlib pass-list + record M3b2a acceptance (M3b2a Task 10)"
```

---

## Plan Self-Review Notes (resolved inline)

- **Spec coverage:** typed decode → Task 3; `leanr_grammar` interpreter → Tasks 5-6; assembly + new categories → Task 7 (+Task 4 seams); import-aware CLI → Task 8; sweep + ratchet → Tasks 9-10; hermetic CI corpus → Tasks 2+7; skip-and-record incl. tokens-still-fold, scoped-skip, never-panic → Tasks 3, 6, 7; fingerprint/M5 seam → Task 7 test; fuzz → Tasks 3/10. Spec's `extend(delta)` wording → amended in Task 1 (recorded rationale).
- **Deliberate scope cuts vs spec text:** `prio` dropped at decode (recorded in Task 3 interface note); `--verbose` skipped-entry listing covered by unit test + stderr path rather than a golden.
- **Empirical pins** (fixture-decided, marked in-task): behavior scalar-vs-boxed (Task 3), Name-literal Expr shapes and `OfNat` unwrapping (Task 6), exact decl-name for `wrap[` (Task 6), `dump_syntax_elab.lean` LEAN_PATH handling (Task 2). Each has an explicit decision procedure; none is a TBD.
- **Type consistency check:** `ParserEntry`/`EntryScope`/`ScopedParserEntry`/`CatBehavior` (Task 3) consumed by Tasks 6-7 with the same shapes; `AliasPrim::lookup` (Task 5) consumed by Task 6; `interpret`/`Interpreted` (Task 6) consumed by Task 7; `assemble`/`AssembledGrammar`/`SkipReason` (Tasks 1/7) consumed by Tasks 8-9; `builder`/`leading_prim`/`trailing_prim`/`parse_header_imports` (Task 4) consumed by Tasks 6-9.
