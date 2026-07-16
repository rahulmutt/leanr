# M3b2b — The General Surface Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `leanr parse` handles quotations/antiquotations oracle-faithfully and parses + derives grammar from the general declaration commands (`syntax`, `declare_syntax_cat`, syntaxAbbrev, `macro`, shape-only `macro_rules`, and import-arrived `elab`/`elab_rules`/`binder_predicate`), with the Mathlib sweep parallelized and re-baselined first so pass-list growth measures this slice honestly.

**Architecture:** Antiquotation is **engine-level**: `Ps` gains a `quot_depth` counter (the seam `CatCacheKey`'s doc at parse.rs:761-767 explicitly reserves); quotation shapes wrap their bodies in new `Prim::IncQuotDepth`/`DecQuotDepth` variants; a central `try_antiquot` (the `mkAntiquot` port) is offered at category entry, `Prim::Node` entry, and the leaf arms when depth > 0 — no registered production changes, no fingerprint changes. Antiquot node kinds (`<kind>.antiquot` etc.) intern into the existing `Overlay` kind space. Derivation generalizes M3b1's `notation.rs`: a shared `GrammarDelta` enum covers notation, `declare_syntax_cat`, and the full `syntax`-item surface (new `grammar/surface.rs`), keyed on command node kind so imported command shapes (`elab` family) derive identically. The parser-alias table moves from `leanr_grammar` to `leanr_syntax::grammar::alias` so source-level derivation and olean-descr interpretation share one pinned table.

**Tech Stack:** Rust workspace (edition 2021); `rowan`/`blake3` in `leanr_syntax`; `rayon` as a **dev-dependency** of `leanr_grammar` only (test-only; already in Cargo.lock transitively via salsa); pinned Lean toolchain `v4.32.0-rc1` for fixtures/oracle only.

## Global Constraints

- **Oracle discipline:** correctness = byte round-trip + structural oracle-tree equality vs the pinned toolchain (`lean-toolchain` = v4.32.0-rc1). Never bump the pin. Regenerate fixtures only via `mise run fixtures:regen`.
- **Engine-level antiquot gating** (spec §Architecture): depth 0 offers NO antiquot alternative anywhere; `$x` at top level fails exactly as the oracle fails it. Snapshot fingerprints of existing grammars must not change (`builder_finish_equals_builtin_snapshot`-style invariance).
- **Skip-and-record, never guess:** a `syntax` body with an unhandled combinator derives nothing (whole command skipped); its atoms still register as tokens. Same discipline as M3b2a's imported skips.
- **Crate boundaries:** `leanr_syntax` keeps zero workspace deps (the alias table moves INTO it, never a dep FROM it). `leanr_olean`/`leanr_kernel` untouched. No logic in `leanr_cli`.
- **New external deps:** exactly one — `rayon` under `leanr_grammar` `[dev-dependencies]` (justification: test-only sweep parallelization, already license-vetted in-tree via salsa). `mise run lint:deps` must stay green.
- **CI vs local:** everything under plain `cargo test --workspace` is hermetic. Mathlib sweep stays `--ignored`/mise-run.
- **Exhaustive matches are load-bearing:** every new `Prim` variant needs arms in `run` (parse.rs:1286), `encode_prim` (grammar/mod.rs:542), `walk_symbols` (grammar/mod.rs:1261), and `first_tokens` (grammar/mod.rs:1073) — the compiler enforces this; never add a wildcard.
- **Empirical pins:** exact antiquot/quotation tree shapes, node-kind names, and token boundaries are pinned by oracle dumps (the committed `.stx.jsonl` is always the arbiter: if a golden assertion disagrees with the dump, fix the code, not the dump). Consult the pinned toolchain source at `~/.elan/toolchains/*/lib/lean4/library/` or the Lean checkout under `.mathlib` for `Lean/Parser/Extra.lean` (`mkAntiquot`, `mkAntiquotSplice`, `withAntiquotSuffixSplice`), `Lean/Parser/Term.lean` (quotation shapes), `Lean/Parser/Syntax.lean` (stx-item and command shapes).
- **Commit style:** `type(scope): summary (M3b2b Task N)` matching M3b1/M3b2a history.

## File Structure

```
crates/leanr_grammar/Cargo.toml            +rayon dev-dependency
crates/leanr_grammar/tests/mathlib_sweep.rs  parallel two-phase sweep (Task 1)
crates/leanr_grammar/src/alias.rs          becomes re-export shim of the moved table (Task 5)
crates/leanr_grammar/src/descr.rs          nodeWithAntiquot/sepBy antiquot flags real (Task 4)
crates/leanr_syntax/src/grammar/mod.rs     +Prim::{IncQuotDepth, DecQuotDepth, DynamicQuotBody,
                                            WithoutAnonymousAntiquot} + encode/walk/first_tokens arms
crates/leanr_syntax/src/grammar/alias.rs   NEW: the shared parser-alias table (moved, now pub)
crates/leanr_syntax/src/grammar/overlay.rs +register_category/has_category/category_behavior;
                                            fingerprint_into covers categories
crates/leanr_syntax/src/grammar/notation.rs derive() → derive_delta() returning GrammarDelta
crates/leanr_syntax/src/grammar/surface.rs NEW: syntax-command item walk → SyntaxSpec/GrammarDelta
crates/leanr_syntax/src/parse.rs           +Ps.quot_depth (+CatCacheKey field), try_antiquot/antiquot,
                                            splice hooks in many_impl/sep_by_impl/Optional,
                                            category() overlay-category fallback, run_module wiring
crates/leanr_syntax/src/lex.rs             backtick falls through to table munch when not a name literal
crates/leanr_syntax/src/builtin/term/term_quot.rs  NEW: Term.quot/dynamicQuot (+ siblings per dumps)
crates/leanr_syntax/src/builtin/command/command_syntax.rs  NEW: stx category + syntax/declare_syntax_cat/
                                            syntaxAbbrev/macro_rules/macro command shapes
crates/leanr_syntax/src/builtin/mod.rs     register new modules + "stx" category
crates/leanr_syntax/tests/never_hang.rs    nested-quotation / $-storm inputs
tests/fixtures/syntax/Quot*.lean|.stx.jsonl     NEW fixtures (parse-only dumper; auto-discovered)
tests/fixtures/syntax/Stx*.lean|.stx.jsonl      NEW fixtures (elab dumper — grammar grows mid-file)
tests/fixtures/syntax/mathlib-passlist.txt      re-baselined (Task 1), grown (Task 10)
mise.toml                                  regen loops learn the Stx*/Quot* split
docs/superpowers/specs/2026-07-16-m3b2b-general-surface-design.md  acceptance recorded (Task 10)
```

**Fixture naming convention (load-bearing for regen):** `Quot*.lean` = quotation/antiquot fixtures with **no mid-file grammar growth** → plain `dump_syntax.lean` loop picks them up automatically (flat-dir glob). `Stx*.lean` = fixtures containing `syntax`/`macro`/`declare_syntax_cat`/`macro_rules` commands (grammar grows mid-file) → the **elaborating** dumper, via an explicit new loop next to `fixtures:regen-notation`, and excluded from the plain loop. `oracle_golden.rs` discovers both automatically (flat `read_dir`), so every fixture must be committed together with the code that makes it green.

---

### Task 1: Parallelize the Mathlib sweep + full-closure re-baseline

The M3b2a follow-up, done first so the ratchet measures M3b2b honestly. The single-threaded full sweep was stopped at 4.5h; the dominant cost is the per-file oracle `lean` subprocess (cached by `(githash, blake3(file))` thereafter). Restructure into two parallel phases: (A) build the per-import-set snapshots concurrently, (B) sweep files concurrently against the shared snapshots. `GrammarSnapshot` is immutable after `finish()` (no interior mutability) so `Arc<GrammarSnapshot>` crosses threads; each phase-A task owns its own `Store` (never shared).

**Files:**
- Modify: `crates/leanr_grammar/Cargo.toml` (`[dev-dependencies]` += rayon)
- Modify: `crates/leanr_grammar/tests/mathlib_sweep.rs`
- Modify: `tests/fixtures/syntax/mathlib-passlist.txt` (re-baselined by the full run)

**Interfaces:**
- Consumes: existing env contract (`LEANR_MATHLIB_DIR`, `LEANR_OLEAN_PATH`, `LEANR_SWEEP_LIMIT`, `LEANR_PASSLIST_UPDATE`).
- Produces: the same test/ratchet contract, now parallel; a full-closure pass-list baseline for Task 10 to grow against. **The bounded-run gating semantics (commits `9c8c68a`/`4d0b815`) must be preserved exactly** — bounded sweeps gate only swept entries; full sweeps also gate deleted entries.

- [ ] **Step 1: Add rayon as a dev-dependency**

In `crates/leanr_grammar/Cargo.toml`:

```toml
[dev-dependencies]
# ... existing entries (blake3) stay ...
rayon = "1"
```

Run: `cargo tree -p leanr_grammar --edges dev | grep rayon` — Expected: `rayon v1.12.0` (resolves to the version already in Cargo.lock via salsa).
Run: `mise run lint:deps` — Expected: PASS (advisory/license clean; rayon is Apache-2.0/MIT).

- [ ] **Step 2: Restructure the sweep into two parallel phases**

In `crates/leanr_grammar/tests/mathlib_sweep.rs`, replace the sequential per-file loop (the `snap_cache` BTreeMap + `for file in &files` section) with the two-phase structure below. **Keep unchanged:** `passlist_path`, `oracle_dump`, `collect_lean_files`, `dotted_to_name`, the env/githash/limit preamble, the file enumeration + `files.truncate(limit)`, and the entire ratchet/`LEANR_PASSLIST_UPDATE` tail including the bounded-run gating logic — read the current tail first and leave its semantics byte-identical (it distinguishes bounded from full runs; that logic was hardened in two follow-up commits and is covered by its own comments).

```rust
use rayon::prelude::*;

// ... after files.sort(); files.truncate(limit); ...

// Phase A: group files by import list, build each import set's
// snapshot once, in parallel. Each closure owns its Store; only the
// immutable Arc<GrammarSnapshot> crosses threads.
let mut by_imports: std::collections::BTreeMap<Vec<String>, Vec<PathBuf>> = Default::default();
for file in &files {
    let Ok(src) = std::fs::read_to_string(file) else { continue };
    by_imports
        .entry(leanr_syntax::parse_header_imports(&src))
        .or_default()
        .push(file.clone());
}
let snaps: std::collections::BTreeMap<Vec<String>, Option<Arc<leanr_syntax::grammar::GrammarSnapshot>>> =
    by_imports
        .keys()
        .cloned()
        .collect::<Vec<_>>()
        .into_par_iter()
        .map(|imports| {
            let mut st = Store::persistent();
            let targets: Vec<_> = imports.iter().map(|m| dotted_to_name(m)).collect();
            let snap = leanr_olean::load_closure(&sp, &targets, &mut st)
                .ok()
                .map(|loaded| Arc::new(assemble(&loaded, &st).snapshot));
            (imports, snap)
        })
        .collect();

// Phase B: sweep all files in parallel. oracle_dump subprocesses
// parallelize here too (the real wall-clock win on a cold cache).
let mut green: Vec<String> = by_imports
    .par_iter()
    .flat_map(|(imports, group)| {
        let snap = &snaps[imports];
        group
            .par_iter()
            .filter_map(|file| {
                let snap = snap.as_ref()?;
                let rel = file.strip_prefix(&mathlib).unwrap_or(file).display().to_string();
                let src = std::fs::read_to_string(file).ok()?;
                let r = leanr_syntax::parse_module(&src, snap);
                if r.tree.text() != src || !r.errors.is_empty() {
                    return None;
                }
                let want = oracle_dump(&mathlib, &lean_path, &githash, file)?;
                (leanr_syntax::canon::canon_jsonl(&r.tree) == want).then_some(rel)
            })
            .collect::<Vec<_>>()
    })
    .collect();
green.sort();
```

Implementation notes:
- If `GrammarSnapshot` turns out not to be `Sync` (compile error on `par_iter`), the offending field will be named in the error; fix by auditing that field for interior mutability rather than wrapping in a lock — the type is meant to be immutable-after-build (it is the M5 cache value).
- The `sp: SearchPath` is borrowed by phase A closures — it must be `Sync`; if not, construct it before the loop and share via `&sp` only if the compiler accepts, else build one per closure (cheap: it's a Vec of PathBufs).
- `RAYON_NUM_THREADS` tunes parallel `lean` subprocess count if a machine hits memory pressure; document it in the `parse:mathlib` mise task description (one-line edit).

- [ ] **Step 3: Bounded smoke run**

Run: `LEANR_SWEEP_LIMIT=200 mise run parse:mathlib`
Expected: completes (minutes, warm dump cache from M3b2a), `0 regressions` against the committed 23-entry pass-list, and wall-clock visibly below the M3b2a sequential 200-file run. Any panic is a bug (the sweep must stay total).

- [ ] **Step 4: Full-closure re-baseline**

Run: `mise run passlist:update` (full sweep — first full run pays oracle elaboration for uncached files; hours even parallel; leave it running) followed by `mise run parse:mathlib`.
Expected: second run green, 0 regressions. `git diff --stat tests/fixtures/syntax/mathlib-passlist.txt` shows growth over the 23-entry bounded baseline (every previously-listed file must still be present — a disappearance is a regression to debug, not accept). Record the file/green counts from the sweep stderr for the commit message.

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_grammar Cargo.lock tests/fixtures/syntax/mathlib-passlist.txt mise.toml
git commit -m "test(grammar): parallelize Mathlib sweep + full-closure pass-list re-baseline (M3b2b Task 1)"
```

---

### Task 2: Quotation shapes + quotation-depth plumbing

Quotation depth becomes real state, and the quotation term shapes (`` `(...) ``, `` `(cat| ...) ``) join the builtin grammar. No antiquots yet — depth is set but nothing reads it until Task 3, so this task's fixtures are quotation-of-plain-content files. Oracle definitions: `Lean/Parser/Term.lean` at the pinned toolchain (`Term.quot`, `Term.dynamicQuot`, and — the dumps will say which others the fixtures hit, e.g. `Term.precheckedQuot`; port exactly the set the dumps name).

**Files:**
- Modify: `crates/leanr_syntax/src/grammar/mod.rs` (3 new `Prim` variants + arms + constructors)
- Modify: `crates/leanr_syntax/src/parse.rs` (`Ps.quot_depth`, `CatCacheKey.quot_depth`, run arms)
- Modify: `crates/leanr_syntax/src/lex.rs` (backtick falls through to table munch)
- Create: `crates/leanr_syntax/src/builtin/term/term_quot.rs`; register from `builtin/term.rs`
- Create: `tests/fixtures/syntax/QuotBasic.lean` (+ committed `.stx.jsonl`)

**Interfaces:**
- Produces (consumed by Tasks 3, 4, 6):
  ```rust
  // grammar/mod.rs — Prim variants
  IncQuotDepth(Arc<Prim>),        // body parses at depth+1
  DecQuotDepth(Arc<Prim>),        // body parses at depth-1 (saturating)
  DynamicQuotBody,                // ident >> "|" >> incQuotDepth(category <ident text>)
  // terse constructors
  pub fn inc_quot_depth(p: Prim) -> Prim;
  pub fn dec_quot_depth(p: Prim) -> Prim;
  // parse.rs — Ps field (crate-private)
  quot_depth: u32,                // 0 outside quotations; NOT in Savepoint (push/pop pairs
                                  // inside single run() frames, like forbidden_stack);
                                  // IS in CatCacheKey (cached category results are depth-dependent)
  ```

- [ ] **Step 1: Author the fixture and regenerate its dump**

`tests/fixtures/syntax/QuotBasic.lean` (bodies chosen antiquot-free; every construct here must be independently supported by the M3a/M3b1 grammar so the quotation is the only new surface):

```lean
def a := `(1 + 2)
def b := `(fun x => x)
def c := `(tactic| rfl)
def d := `(term| 42)
def e := `(#check 1)
```

Run: `mise run fixtures:regen`
Expected: `QuotBasic.stx.jsonl` appears (plain `dump_syntax.lean` loop — flat glob, no `Notation`/`Stx` prefix). **Read the dump now**: its node kinds are the exact port list for Step 4 (expect `Lean.Parser.Term.quot`, `Lean.Parser.Term.dynamicQuot`; if line `a`'s kind is `Lean.Parser.Term.precheckedQuot` wrapping a quot, that shape joins the port list too). If any line's dump reveals a construct out of M3b2b scope, simplify that fixture line rather than expanding scope. NOTE: `cargo test` is now red (`oracle_golden` discovers the fixture; leanr can't parse it yet) — this is the failing-test state, resolved by Steps 2-5 before commit.

- [ ] **Step 2: Lexer — backtick falls through to table munch**

Failing test in `crates/leanr_syntax/src/lex.rs` tests (follow the existing test-module idiom, e.g. `french_quote_escapes_and_letterlike`):

```rust
#[test]
fn backtick_paren_lexes_as_atom_when_in_table() {
    let mut t = TokenTable::default();
    t.insert("`(");
    t.insert("`");
    // "`(" present and next char not id-first → 2-byte atom, maximal munch.
    assert_eq!(lex_all("`(", &t)[0], (TokenKind::Atom, "`("));
    // A name literal still wins when the char after the backtick is id-first.
    assert_eq!(lex_all("`foo", &t)[0].0, TokenKind::NameLit);
    // Bare "`" before a non-id char: the 1-byte atom.
    assert_eq!(lex_all("` x", &t)[0], (TokenKind::Atom, "`"));
}
```

Run: `cargo test -p leanr_syntax backtick_paren` — Expected: FAIL (backtick branch currently claims the byte for name-literal lexing).

Implement: in `next_token`'s backtick branch, only enter name-literal lexing when the following char is id-first (mirroring the oracle: Lean's tokenizer tries the token table for `` `( `` because `(` cannot start a name); otherwise fall through to the existing table-munch tail. Read the branch first — it already has a fallthrough for disambiguation failures (lex.rs:305's comment); extend that guard rather than duplicating logic. Re-run: PASS. Then `cargo test -p leanr_syntax` — the untouched corpus must stay green (no existing fixture contains a bare backtick before a non-id char except via `doubleQuotedName`, whose `raw_char` path is unaffected; if a fixture regresses, the guard is too broad — a name literal must still win for id-first).

- [ ] **Step 3: `Prim` variants + `quot_depth` plumbing**

In `grammar/mod.rs`, add to the `Prim` enum (after `DocCommentBody`):

```rust
    /// ORACLE `incQuotDepth p`: body parses with quotation depth +1
    /// (antiquotation alternatives become active — engine-level, Task 3).
    IncQuotDepth(Arc<Prim>),
    /// ORACLE `decQuotDepth p`: the `$(e)` nested-term escape parses its
    /// body one level shallower (saturating at 0).
    DecQuotDepth(Arc<Prim>),
    /// ORACLE `parserOfStack 1` as used by `Term.dynamicQuot`: consume an
    /// ident naming a category, then `|`, then that category's parser at
    /// depth+1. Engine-special because the category is named by input
    /// text (precedent: `UnknownTacticIdent`, `DocCommentBody`).
    DynamicQuotBody,
```

Terse constructors next to `atomic`/`cat`:

```rust
pub fn inc_quot_depth(p: Prim) -> Prim {
    Prim::IncQuotDepth(Arc::new(p))
}
pub fn dec_quot_depth(p: Prim) -> Prim {
    Prim::DecQuotDepth(Arc::new(p))
}
```

Exhaustive-match arms (compiler drives you to each site):
- `encode_prim` (grammar/mod.rs:542): next free tag bytes, one per variant, recursing into the inner prim; `DynamicQuotBody` is a bare tag.
- `walk_symbols` (grammar/mod.rs:1261): recurse into inner for the two wrappers; `DynamicQuotBody => {}` (the `|` atom is registered by the shape's own `sym("|")` — see Step 4 layout note).
- `first_tokens` (grammar/mod.rs:1073): `IncQuotDepth(p) | DecQuotDepth(p)` delegate to inner; `DynamicQuotBody` → `Ft::Tokens(vec![FirstTok::Ident])`.

In `parse.rs`:
- `Ps` field `quot_depth: u32` (init `0` in `Ps::new`). NOT added to `Savepoint`: increments/decrements pair inside single `run()` frames, so backtracking cannot leak depth (same argument as `forbidden_stack`/`pos_stack`, which `Savepoint` also omits).
- `CatCacheKey` (parse.rs:789) gains `quot_depth: u32`, populated from `self.quot_depth` where `category()` builds the key (parse.rs:2287) — a term memoized at depth 0 must never satisfy a depth-1 lookup once Task 3 lands.
- `run` arms:

```rust
            Prim::IncQuotDepth(q) => {
                self.quot_depth += 1;
                let r = self.run(q);
                self.quot_depth -= 1;
                r
            }
            Prim::DecQuotDepth(q) => {
                let saved = self.quot_depth;
                self.quot_depth = saved.saturating_sub(1);
                let r = self.run(q);
                self.quot_depth = saved;
                r
            }
            Prim::DynamicQuotBody => self.dynamic_quot_body(),
```

- New method (next to `doc_comment_body`):

```rust
    /// ORACLE `Term.dynamicQuot`'s `ident >> "|" >> incQuotDepth
    /// (parserOfStack 1)` tail: the just-parsed ident names the category.
    fn dynamic_quot_body(&mut self) -> PResult {
        let (t, at, sp) = self.peek_for_match();
        if t.kind != TokenKind::Ident {
            self.restore(&sp);
            return Err(self.fail_expecting("<quotation category>", at));
        }
        let cat_name = self.src[at..at + t.len as usize].to_string();
        self.bump(t, KIND_IDENT);
        self.expect_atom("|", false)?;
        self.quot_depth += 1;
        let r = self.category(&cat_name, 0);
        self.quot_depth -= 1;
        r
    }
```

- [ ] **Step 4: Port the quotation shapes**

`crates/leanr_syntax/src/builtin/term/term_quot.rs`, new file, following the `term_pragma.rs` module idiom (`pub(super) fn register(b: &mut SnapshotBuilder)` called from `term.rs`'s `register`). Initial port — **adjust node layout to the Step 1 dump byte-exactly** (child count and null-node placement are what the dump pins; the shapes below are the expected structure from the oracle source):

```rust
//! Quotation term shapes (M3b2b Task 2). ORACLE-PORT `Lean/Parser/Term.lean`:
//! `Term.quot := leading_parser "`(" >> withoutPosition (incQuotDepth
//! (termParser <|> many1Unbox commandParser)) >> ")"` and
//! `Term.dynamicQuot := leading_parser "`(" >> ident >> "|" >>
//! incQuotDepth (parserOfStack 1) >> ")"`. Antiquot behavior inside is
//! Task 3; here the bodies just parse at depth+1.

use crate::grammar::*;

pub(super) fn register(b: &mut SnapshotBuilder) {
    // dynamicQuot must be offered alongside quot on the same "`(" head;
    // longest-match picks it when `ident |` follows (`(tactic| rfl)`)
    // because the plain-term candidate stops at the `|`.
    b.leading2(
        "term",
        "Lean.Parser.Term.dynamicQuot",
        MAX_PREC,
        seq([
            sym("`("),
            Prim::DynamicQuotBody,
            sym(")"),
        ]),
    );
    b.leading2(
        "term",
        "Lean.Parser.Term.quot",
        MAX_PREC,
        seq([
            sym("`("),
            inc_quot_depth(or_else([
                cat("term", 0),
                many1(cat("command", 0)),
            ])),
            sym(")"),
        ]),
    );
}
```

Empirical pins (decide each against the dump, comment the observed shape):
- Whether line `a`'s outer kind is `quot` directly or `precheckedQuot`-wrapped — if wrapped, port `precheckedQuot` as the registered production with `quot` as an inner `nd(...)` node.
- Whether the command alternative is `many1` of command or a dedicated node (`many1Unbox` flattens a singleton — if the dump shows the single `#check` WITHOUT a wrapping null node, model it as `or_else([cat("term",0), seq([cat("command",0), many(cat("command",0))])])` and match the event shape; the dump decides).
- The `withoutPosition` wrapper is position-transparent in this engine (no `WithPosition` frame) — omit unless a colGt check inside a fixture body proves otherwise.

Register the module in `builtin/term.rs`'s `register` (after the existing `term_pragma::register(b)` call site idiom) and `mod term_quot;` in the `term/` module list.

- [ ] **Step 5: Green the fixture**

Run: `cargo test -p leanr_syntax --test oracle_golden`
Expected: PASS including `QuotBasic` (byte round-trip + line-by-line dump equality). Iterate node layout against the dump until green — the dump is the oracle. Then `cargo test --workspace` — Expected: PASS (fingerprint-sensitive tests: the builtin snapshot grew two productions, which is fine — only tests asserting *specific* fingerprints would break, and none do; `builder_finish_equals_builtin_snapshot` compares builder-vs-snapshot, not a pinned value).

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_syntax tests/fixtures/syntax/QuotBasic.lean tests/fixtures/syntax/QuotBasic.stx.jsonl
git commit -m "feat(syntax): quotation term shapes + quotation-depth plumbing (M3b2b Task 2)"
```

---

### Task 3: The antiquotation alternative (`mkAntiquot` port, engine-level)

The heart of the slice. One central `antiquot` parser + a `try_antiquot` gate, offered when `quot_depth > 0` at the places a node begins: category entry (before leading dispatch), `Prim::Node` entry, and the `Ident`/literal leaf arms. Antiquot node kinds (`<kind>.antiquot`, `antiquotName`, `antiquotNestedExpr`) intern into the **overlay** kind space (`Overlay::intern` is idempotent and `merged_kinds` already materializes overlay kinds at tree build — no snapshot/fingerprint change). Oracle: `mkAntiquot` in `Lean/Parser/Extra.lean` — read it at the pinned toolchain before implementing; the shape below is its expected structure.

**Files:**
- Modify: `crates/leanr_syntax/src/parse.rs` (`try_antiquot`, `antiquot`, call sites)
- Modify: `crates/leanr_syntax/src/grammar/mod.rs` (`WithoutAnonymousAntiquot` variant + arms)
- Create: `tests/fixtures/syntax/QuotAntiquot.lean` (+ dump)

**Interfaces:**
- Produces (consumed by Tasks 4, 8):
  ```rust
  // parse.rs (crate-private)
  /// None = not applicable here (depth 0, next token not `$`, or the
  /// atomic `$`-prefix failed → state restored, caller parses normally).
  /// Some(r) = the antiquot alternative ran and committed.
  fn try_antiquot(&mut self, name: &str, kind_name: &str, anonymous: bool) -> Option<PResult>;
  // grammar/mod.rs
  Prim::WithoutAnonymousAntiquot(Arc<Prim>),   // `$x` (no `:name`) rejected inside
  ```

- [ ] **Step 1: Author the fixture and regenerate**

`tests/fixtures/syntax/QuotAntiquot.lean`:

```lean
def a := `($x)
def b := `($x + $y)
def c := `($x:ident)
def d := `($(f 1) + 1)
def e := `(fun y => $body)
def f := `(tactic| exact $h)
def g := `(`($$x))
def h := `($x + 1 * $y)
```

Run: `mise run fixtures:regen`. **Study `QuotAntiquot.stx.jsonl` before writing code** — it pins: the antiquot node kind for a category position (expect `term.antiquot` for lines a/b — the category name, not a `Lean.Parser.*` path), the child layout (expect four children: the `$` atom, a null node holding extra `$`s, the ident or `antiquotNestedExpr` node, and the `antiquotName` node or null), the `$$` escape's tree at nested depth (line g), and the typed-antiquot suffix layout (line c). Every layout decision in Step 3 defers to this file.

- [ ] **Step 2: Write the failing engine unit test**

In `parse.rs`'s `#[cfg(test)]` module (existing idiom `new_for_test` at 2846):

```rust
#[test]
fn antiquot_only_inside_quotation() {
    let snap = crate::builtin::snapshot();
    // Inside `(...): `$x` parses as a term.antiquot node.
    let r = crate::parse_module("def a := `($x)\n", &snap);
    assert!(r.errors.is_empty(), "{:?}", r.errors);
    assert!(
        crate::canon::canon_jsonl(&r.tree).contains("term.antiquot"),
        "no antiquot node in {}",
        crate::canon::canon_jsonl(&r.tree)
    );
    // Outside a quotation, `$x` is NOT an antiquot (macroDollarArg
    // territory / plain failure — exactly what depth 0 means).
    let r0 = crate::parse_module("def a := $x\n", &snap);
    assert!(!crate::canon::canon_jsonl(&r0.tree).contains("antiquot"));
}
```

Run: `cargo test -p leanr_syntax antiquot_only_inside` — Expected: FAIL (no antiquot machinery).

- [ ] **Step 3: Implement `try_antiquot` / `antiquot`**

In `parse.rs`, next to `expect_atom`:

```rust
    /// ORACLE-PORT `mkAntiquot` (Lean/Parser/Extra.lean). The gate: only
    /// at quot_depth > 0 with `$` next. The `$`-prefix is atomic — if it
    /// fails before the spliced term, state restores and the caller
    /// parses normally (None). After the prefix, the antiquot commits.
    fn try_antiquot(&mut self, name: &str, kind_name: &str, anonymous: bool) -> Option<PResult> {
        if self.quot_depth == 0 {
            return None;
        }
        let (t, at) = self.peek_significant_readonly();
        if t.kind != TokenKind::Atom || &self.src[at..at + t.len as usize] != "$" {
            return None;
        }
        Some(self.antiquot(name, kind_name, anonymous))
    }

    /// node `<kind_name>.antiquot`:
    ///   "$"  many(noWs "$")  noWs (ident <|> "(" decQuotDepth(term) ")")
    ///   (":" name | null-if-anonymous)
    /// Child layout is pinned by QuotAntiquot.stx.jsonl — adjust the
    /// start/finish placement below to reproduce it byte-exactly.
    fn antiquot(&mut self, name: &str, kind_name: &str, anonymous: bool) -> PResult {
        let kind = self.overlay.intern(&format!("{kind_name}.antiquot"));
        let sp = self.save();
        self.start(kind);
        // --- atomic prefix ---
        let prefix = (|| -> PResult {
            self.expect_atom("$", false)?;
            // Extra `$`s (nested-quotation escape). Each must be
            // whitespace-adjacent to the previous.
            self.start(KIND_NULL);
            loop {
                let sp2 = self.save();
                let (t, at2) = self.peek_significant_readonly();
                let is_dollar =
                    t.kind == TokenKind::Atom && &self.src[at2..at2 + t.len as usize] == "$";
                if !is_dollar || self.had_ws_before_current() {
                    self.restore(&sp2);
                    break;
                }
                self.expect_atom("$", false)?;
            }
            self.finish();
            if self.had_ws_before_current() {
                let at2 = self.pos;
                return Err(self.fail_expecting("<no space before spliced term>", at2));
            }
            Ok(())
        })();
        if prefix.is_err() {
            // Prefix failed → not an antiquot after all; unwind fully.
            self.restore(&sp);
            return prefix;
        }
        // --- committed body ---
        let r = (|| -> PResult {
            // ident, or `(` decQuotDepth(term) `)` as antiquotNestedExpr.
            let (t, at2, sp2) = self.peek_for_match();
            match t.kind {
                TokenKind::Ident => self.bump(t, KIND_IDENT),
                TokenKind::Atom if &self.src[at2..at2 + t.len as usize] == "(" => {
                    self.restore(&sp2);
                    let nested = self.overlay.intern("antiquotNestedExpr");
                    self.start(nested);
                    let inner = (|| -> PResult {
                        self.expect_atom("(", false)?;
                        self.run(&Prim::DecQuotDepth(Arc::new(Prim::Category {
                            name: "term".into(),
                            rbp: 0,
                        })))?;
                        self.expect_atom(")", false)
                    })();
                    self.finish();
                    inner?;
                }
                _ => {
                    self.restore(&sp2);
                    return Err(self.fail_expecting("<antiquot ident or (term)>", at2));
                }
            }
            // Optional `:name` suffix (antiquotName node); when
            // !anonymous the suffix is mandatory.
            let sp3 = self.save();
            let (t, at3) = self.peek_significant_readonly();
            let is_colon =
                t.kind == TokenKind::Atom && &self.src[at3..at3 + t.len as usize] == ":";
            if is_colon && !self.had_ws_before_current() {
                let named = self.overlay.intern("antiquotName");
                self.start(named);
                let inner = (|| -> PResult {
                    self.expect_atom(":", false)?;
                    self.expect_atom(name, true) // nonReservedSymbol: ident allowed
                })();
                self.finish();
                if inner.is_err() {
                    self.restore(&sp3);
                    if !anonymous {
                        let at4 = self.pos;
                        return Err(self.fail_expecting("<:kind>", at4));
                    }
                    self.start(KIND_NULL);
                    self.finish();
                }
            } else if anonymous {
                self.start(KIND_NULL);
                self.finish();
            } else {
                let at4 = self.pos;
                return Err(self.fail_expecting("<:kind>", at4));
            }
            Ok(())
        })();
        self.finish(); // the antiquot node always closes (Node-arm idiom)
        if r.is_ok() {
            self.lhs_prec = crate::grammar::MAX_PREC; // leadingNode kind maxPrec
        }
        r
    }
```

Empirical pins against the Step 1 dump (each is a deliberate decision point, not a TBD — the dump answers it in minutes):
- Whether the extra-`$` null node exists even when empty (Lean's `many` always emits a null node — expected yes, hence unconditional `start/finish`).
- Whether `:name` after a typed antiquot in a *category* position matches only the category name or any ident (`expect_atom(name, true)` vs accepting any ident and comparing later — line c decides; **crucially, `$x:ident` in a term position is a TERM antiquot with `antiquotName` "ident"**, not an ident-leaf antiquot: the suffix names the *expected kind*, and dispatch happens at the category level. If the dump shows kind `term.antiquot` with suffix `ident`, the `name` parameter must accept arbitrary idents in category positions — implement what the dump shows).
- Whether a `,`/anonymous suffix slot (`pushNone`) appears as a null child in every antiquot node (expected: yes when `anonymous`).
- `$$x` at depth 2 (line g): one extra `$` consumed into the null node, and the *inner* quotation's antiquot only — verify the outer quotation's parse leaves `$$x` intact per the dump.

- [ ] **Step 4: Wire the call sites**

1. **Category entry** — in `category()`'s leading-dispatch closure (parse.rs:2399, right before `dispatch` at 2415):

```rust
            if let Some(r) = self.try_antiquot(name, name, true) {
                r?;
                // Antiquot is the lhs; fall through to the trailing loop
                // (e.g. `$x + $y`: antiquot lhs, `+` trailing).
            } else {
                // ... existing leading dispatch + longest_match block,
                //     unchanged, moved into this else ...
            }
```

The category antiquot's `kind_name` is the bare category name (`term.antiquot` — pinned by the dump) and it is always anonymous.

2. **`Prim::Node` entry** (parse.rs:1293) — before the prec gate:

```rust
            Prim::Node { kind, prec, body } => {
                let kind_name = self.kinds.name(*kind).to_string();
                if let Some(r) = self.try_antiquot(
                    kind_name.rsplit('.').next().unwrap_or(&kind_name),
                    &kind_name,
                    self.anon_antiquot_ok,
                ) {
                    if r.is_ok() {
                        self.lhs_prec = prec.unwrap_or(0);
                    }
                    return r;
                }
                // ... existing arm body unchanged ...
```

Perf note: the added work on the hot path is one `quot_depth == 0` check (the `try_antiquot` early return) — the `kind_name` string materialization must happen ONLY after the depth check; restructure so depth 0 pays nothing:

```rust
                if self.quot_depth > 0 {
                    let kind_name = self.kinds.name(*kind).to_string();
                    let short = kind_name.rsplit('.').next().unwrap_or(&kind_name).to_string();
                    if let Some(r) = self.try_antiquot(&short, &kind_name, self.anon_antiquot_ok) {
                        if r.is_ok() { self.lhs_prec = prec.unwrap_or(0); }
                        return r;
                    }
                }
```

3. **Leaf arms** (`Ident`, `NumLit`, `StrLit`, `CharLit`, `NameLit`, `ScientificLit`): same pattern, with `(name, kind_name)` = (`"ident"`, `"ident"`), (`"num"`, `"num"`), etc. — Lean's leaf parsers are `withAntiquot (mkAntiquot "ident" identKind) identNoAntiquot` and friends. Only add each hook when a fixture line exercises it (line c covers ident); leave the others for the corpus/sweep to demand, with a note in the arm (`// antiquot hook: added on demand, see M3b2b plan Task 3`).

4. **`WithoutAnonymousAntiquot`** — `Prim` variant + `Ps` flag:

```rust
// grammar/mod.rs, Prim:
    /// ORACLE `withoutAnonymousAntiquot p`: inside, a bare `$x` (no
    /// `:name`) is not accepted by node antiquots.
    WithoutAnonymousAntiquot(Arc<Prim>),
// parse.rs, Ps field:
    anon_antiquot_ok: bool,   // init true in Ps::new
// run arm:
            Prim::WithoutAnonymousAntiquot(q) => {
                let saved = self.anon_antiquot_ok;
                self.anon_antiquot_ok = false;
                let r = self.run(q);
                self.anon_antiquot_ok = saved;
                r
            }
```

`encode_prim`/`walk_symbols`/`first_tokens`: delegate to inner (new tag byte in encode). No builtin uses it yet (the `opt(never())` placeholders in `term_pragma.rs` stay as they are); Task 4's descr mapping produces it for imported parsers.

- [ ] **Step 5: Green the tests and fixture**

Run: `cargo test -p leanr_syntax antiquot_only_inside` — Expected: PASS.
Run: `cargo test -p leanr_syntax --test oracle_golden` — Expected: PASS including `QuotAntiquot` (iterate the layout pins against the dump).
Run: `cargo test --workspace` — Expected: PASS. Existing corpus must be untouched (depth is 0 everywhere outside the new fixtures; the only behavior change at depth 0 is none at all).

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_syntax tests/fixtures/syntax/QuotAntiquot.lean tests/fixtures/syntax/QuotAntiquot.stx.jsonl
git commit -m "feat(syntax): engine-level antiquotation alternative gated on quotation depth (M3b2b Task 3)"
```

---

### Task 4: Splices and antiquot suffixes (`$xs,*`, `$[...]?`) + real descr flags

The repetition antiquot forms. Oracle (`Lean/Parser/Extra.lean`): `mkAntiquotSplice` → node `<kind>.antiquot_scope` = `atomic("$" >> many "$" >> "[") >> p >> "]" >> suffix`; `withAntiquotSuffixSplice` → node `<kind>.antiquot_suffix_splice` = `<elem antiquot> >> suffix` (the `$xs,*` form). These hook into `many_impl`, `sep_by_impl`, and the `Optional` arm when depth > 0. On the imported side, `leanr_grammar/src/descr.rs`'s `nodeWithAntiquot`/`sepBy` mappings stop erasing antiquot information.

**Files:**
- Modify: `crates/leanr_syntax/src/parse.rs` (splice hooks)
- Modify: `crates/leanr_grammar/src/descr.rs` (`nodeWithAntiquot` name arg honored; sepBy antiquot behavior comment updated)
- Create: `tests/fixtures/syntax/QuotSplice.lean` (+ dump)

**Interfaces:**
- Consumes: `try_antiquot`/`antiquot` (Task 3); `Prim::WithoutAnonymousAntiquot`.
- Produces: `fn try_antiquot_splice(&mut self, kind_name: &str, suffix: Option<&str>) -> Option<PResult>` (parse.rs, crate-private), called from `many_impl`/`sep_by_impl`/`Optional`.

- [ ] **Step 1: Author the fixture and regenerate**

`tests/fixtures/syntax/QuotSplice.lean`:

```lean
def a := `(⟨$xs,*⟩)
def b := `(f $args*)
def c := `(⟨$[$x]?,*⟩)
def d := `(tactic| exact ⟨$proofs,*⟩)
```

Run: `mise run fixtures:regen`. The dump pins: the suffix token boundaries (**does `,*` lex as ONE atom or as `,` + `*`? the atom spans answer definitively** — if one atom, `",*"` must be registered in the token table by the splice machinery; that registration goes in `builtin::builder()` next to the base tokens, with an ORACLE comment), the `antiquot_suffix_splice` node kind prefix for a sepBy position (expect `sepBy.antiquot_suffix_splice` — the pseudo-kind `sepBy`, not the element's kind), and the `$[...]` scope layout for line c (expect `sepBy.antiquot_scope` or `null.antiquot_scope` — read it).

- [ ] **Step 2: Implement the splice hooks**

In `parse.rs`:

```rust
    /// ORACLE `withAntiquotSpliceAndSuffix`/`mkAntiquotSplice`: in a
    /// repetition position at depth > 0, `$xs<suffix>` (suffix splice)
    /// and `$[<p>]<suffix>` (scope) are alternatives to the element.
    /// `kind_name` is the pseudo-kind (`"sepBy"` for sepBy positions,
    /// `"many"` for many positions, `"optional"` for optional — pin the
    /// names against the dump). Returns None if not applicable.
    fn try_antiquot_splice(
        &mut self,
        kind_name: &str,
        suffix: Option<&str>,
        scope_body: Option<&Prim>,
    ) -> Option<PResult> {
        if self.quot_depth == 0 {
            return None;
        }
        let (t, at) = self.peek_significant_readonly();
        if t.kind != TokenKind::Atom || &self.src[at..at + t.len as usize] != "$" {
            return None;
        }
        // `$[` → scope form; `$ident`/`$( ` → suffix-splice form.
        // Distinguish by lookahead on the token after `$` (noWs).
        Some(self.antiquot_splice(kind_name, suffix, scope_body))
    }
```

`antiquot_splice` follows the `antiquot` implementation pattern from Task 3: interned overlay kinds `{kind_name}.antiquot_scope` / `{kind_name}.antiquot_suffix_splice`, atomic `$`-prefix, then either `[ body ]` (running `scope_body` — the repetition's element prim — at the same depth) or the element's own antiquot via `self.antiquot(...)`, then the suffix atom(s) if `suffix` is `Some` (`expect_atom(suffix, false)`; register `",*"`-style combined tokens per the Step 1 pin). Complete the body by transcription from Task 3's `antiquot` with those two branches — every helper it needs (`save`/`restore`/`start`/`finish`/`expect_atom`/overlay interning) already exists.

Call sites:
- `many_impl` (parse.rs:1734): at the top of the loop body, before `self.run(q)`:
  ```rust
            if let Some(r) = self.try_antiquot_splice("many", Some("*"), Some(q)) {
                match r {
                    Ok(()) => { n += 1; continue; }
                    Err(f) => break Err(f),
                }
            }
  ```
- `sep_by_impl` (parse.rs:1790): same position, `("sepBy", Some(&format!("{sep}*")), Some(item))` — and a matching `break 'outer Ok(())` treatment: after a suffix splice, the repetition is COMPLETE (the `,*` consumed the whole list) — pin the continuation behavior against line a's dump (expected: the splice IS the entire null-node content).
- `Optional` arm (parse.rs:1330): `("optional", Some("?"), Some(q))` before the normal body, inside the null wrap.
- Pseudo-kind names (`"many"`, `"sepBy"`, `"optional"`) are the pin: the dump's `.antiquot_scope`/`.antiquot_suffix_splice` kind prefixes name them exactly.

- [ ] **Step 3: Real descr flags in `leanr_grammar`**

In `crates/leanr_grammar/src/descr.rs`, the `("ParserDescr.nodeWithAntiquot", 3)` arm (descr.rs:162): the constructor is `nodeWithAntiquot (name : String) (kind : SyntaxNodeKind) (p : ParserDescr) (anonymous := false)` — with engine-level gating, the `Prim::Node { kind, .. }` mapping already gets antiquot behavior automatically from the Task 3 Node hook; the `name` arg only matters when it differs from the kind's last component (rare). Update the comment to say the engine now provides the behavior, and wrap in `Prim::WithoutAnonymousAntiquot` when the decoded `anonymous` field is false — **pin the field's presence/encoding against `NotaDep.olean`** (the arity may be 3 with anonymous defaulted; if no 4th field exists in practice, record that in the comment and leave the wrap out). Add a unit golden in descr.rs's test module asserting the arm still interprets `wrap[` identically (regression guard for the comment-only/wrap change).

- [ ] **Step 4: Green everything**

Run: `cargo test -p leanr_syntax --test oracle_golden && cargo test -p leanr_grammar && cargo test --workspace`
Expected: all PASS, `QuotSplice` green against its dump.

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_syntax crates/leanr_grammar tests/fixtures/syntax/QuotSplice.lean tests/fixtures/syntax/QuotSplice.stx.jsonl
git commit -m "feat(syntax): antiquot splices and scopes in repetition positions (M3b2b Task 4)"
```

---

### Task 5: Move the parser-alias table to `leanr_syntax::grammar::alias`

The source-level `syntax`-command combinators (Task 8) and the olean descr interpreter resolve the SAME `parserAliases` names. One pinned table, two consumers. `leanr_syntax` keeps zero workspace deps (the table is pure `Prim` construction); `leanr_grammar` re-exports it internally so `descr.rs` is untouched beyond an import path.

**Files:**
- Create: `crates/leanr_syntax/src/grammar/alias.rs` (the moved table, now `pub`)
- Modify: `crates/leanr_syntax/src/grammar/mod.rs` (`pub mod alias;`)
- Modify: `crates/leanr_grammar/src/alias.rs` (becomes a re-export shim)

**Interfaces:**
- Produces (consumed by Task 8 and by `leanr_grammar::descr`):
  ```rust
  // leanr_syntax::grammar::alias
  pub enum AliasPrim { Const(Prim), Epsilon, Unary(fn(Prim) -> Prim), Transparent, Binary(fn(Prim, Prim) -> Prim) }
  pub fn lookup(alias: &str) -> Option<AliasPrim>;
  ```

- [ ] **Step 1: Move the file**

Copy `crates/leanr_grammar/src/alias.rs` verbatim to `crates/leanr_syntax/src/grammar/alias.rs` with exactly these edits: `pub(crate)` → `pub` on `AliasPrim` and `lookup`; the `use leanr_syntax::grammar::Prim;` import becomes `use super::Prim;`; the module doc gains one line: "Shared by the olean descr interpreter (`leanr_grammar`) and the source-level `syntax`-command derivation (`grammar::surface`) — one pinned table, two consumers." The `#[cfg(test)]` module moves with it (same edits to its imports).

Add `pub mod alias;` to `grammar/mod.rs`'s module list.

- [ ] **Step 2: Shim `leanr_grammar`**

Replace `crates/leanr_grammar/src/alias.rs`'s entire content with:

```rust
//! Moved to `leanr_syntax::grammar::alias` (M3b2b Task 5) so the
//! source-level `syntax`-command derivation shares the same pinned
//! table. This shim keeps `descr.rs`'s import path stable.

pub(crate) use leanr_syntax::grammar::alias::{lookup, AliasPrim};
```

- [ ] **Step 3: Verify**

Run: `cargo test --workspace`
Expected: PASS — `leanr_grammar`'s descr goldens and the moved alias tests both green; no other change.

- [ ] **Step 4: Commit**

```bash
git add crates/leanr_syntax crates/leanr_grammar
git commit -m "refactor(syntax): parser-alias table moves to leanr_syntax::grammar::alias (M3b2b Task 5)"
```

---

### Task 6: The general command shapes (`stx` category + `syntax`/`declare_syntax_cat`/syntaxAbbrev/`macro_rules`/`macro`)

SHAPES only — pure M3a-style grammar-production porting (exactly like M3b1's `command_notation.rs`, whose module doc states the same discipline); derivation is Tasks 7-8. The `syntax` command's items live in Lean's `stx` category (`Lean/Parser/Syntax.lean`: `Syntax.paren`, `Syntax.cat`, `Syntax.atom`, `Syntax.unary`, `Syntax.binary`, `Syntax.sepBy`, `Syntax.sepBy1`, `Syntax.nonReserved` — read the file at the pinned toolchain for exact bodies). `macro_rules`/`macro` bodies contain quotations — Tasks 2-4 made those parseable.

**Files:**
- Create: `crates/leanr_syntax/src/builtin/command/command_syntax.rs`
- Modify: `crates/leanr_syntax/src/builtin/command.rs` (module + register call), `crates/leanr_syntax/src/builtin/mod.rs` (`b.category("stx", Default)`)
- Create: `tests/fixtures/syntax/StxShapes.lean` (+ dump), `tests/fixtures/syntax/QuotMacroRules.lean` (+ dump)
- Modify: `mise.toml` (`Stx*` joins the elab-dumper loop, excluded from the plain loop)

**Interfaces:**
- Produces (consumed by Tasks 7-8): command productions with Lean-exact kinds — `Lean.Parser.Command.syntax`, `Lean.Parser.Command.syntaxAbbrev`, `Lean.Parser.Command.syntaxCat` (declare_syntax_cat), `Lean.Parser.Command.macro_rules`, `Lean.Parser.Command.macro` (kind names pinned by the dumps — if a dump shows a different name, e.g. `declare_syntax_cat` under another kind, the dump wins); the `stx` category with the `Lean.Parser.Syntax.*` productions.

- [ ] **Step 1: Wire the fixture regen split, author fixtures, regenerate**

In `mise.toml`:
1. The plain `dump_syntax.lean` loop's exclusion pattern (which already excludes `dump_syntax*.lean` and `Notation*.lean`) also excludes `Stx*.lean` — read the existing `sh -c` line and extend its filter the same way `Notation*` is excluded.
2. In `fixtures:regen-notation`'s run-list, duplicate the `Notation*` elab-dump loop for `Stx*` (same `dump_syntax_elab.lean` invocation, glob `Stx*.lean`, still excluding nothing else).

`tests/fixtures/syntax/StxShapes.lean` (declaration-only — everything elaborates without use-sites, so the elab dumper is happy; each line exercises one stx-item class):

```lean
declare_syntax_cat widgetish
syntax "wob" : widgetish
syntax num : widgetish
syntax:65 "probe" term : term
syntax (name := probed) "probe!" term,* : term
syntax "grab[" widgetish "]" : term
syntax "many_of" term+ : term
syntax "opt_of" (term)? : term
syntax "sep_of" sepBy(term, ", ") : term
syntax "nonres" &"weird" : term
syntax myNum := num
```

`tests/fixtures/syntax/QuotMacroRules.lean`:

```lean
syntax "probe" term : term
macro_rules | `(probe $x) => `($x + 1)
macro "twice" x:term : term => `($x + $x)
#check probe 4
#check twice 3
```

Run: `mise run fixtures:regen`. Expected: both dumps appear via the elab loop. **Read both dumps**: they pin every command kind name, the `stx`-item node kinds and layouts, the `macro` command's arg shapes (`Lean.Parser.Command.macroArg` with the `x:term` ident-colon layout), and `macro_rules`' alt structure (expect it reusing `Term.matchAlts` — whose port already exists for `match`). `QuotMacroRules`'s `#check probe 4` line ALSO pins Task 8's derivation output (the `probe` production's node kind and tree) — this fixture goes green only at Task 8; **keep it uncommitted until then** (`git add` excludes it in this task's commit; the flat-dir `oracle_golden` discovery means the working tree stays red on it until Task 8 — acceptable locally, but do not push between Tasks 6 and 8 with it added).

Correction to keep CI green task-by-task: since `oracle_golden.rs` auto-discovers committed fixtures, commit `StxShapes.*` in THIS task (green after Step 3) and leave `QuotMacroRules.*` untracked until Task 8 (list it in `.git/info/exclude` locally if the noise bothers, but do NOT add it to `.gitignore`).

- [ ] **Step 2: Failing test**

`StxShapes` is the failing test: after regen, `cargo test -p leanr_syntax --test oracle_golden` fails on it (unknown commands). Confirm that's the only new failure.

- [ ] **Step 3: Port the shapes**

`crates/leanr_syntax/src/builtin/command/command_syntax.rs`, following `command_notation.rs`'s idiom exactly (module doc with the oracle dump excerpts, helper fns building sub-node prims via `nd`, one `pub(super) fn register(b: &mut SnapshotBuilder)`). Structure (bodies transcribed from `Lean/Parser/Syntax.lean` + pinned by the StxShapes dump):

```rust
//! `syntax`-family command shapes (M3b2b Task 6). SHAPES only —
//! derivation is grammar/surface.rs. ORACLE-PORT Lean/Parser/Syntax.lean.

use super::super::attr::{attr_kind, attributes};
use super::super::command::{doc_comment, named_prio, nd};
use crate::grammar::*;

/// The `stx` category productions (Lean/Parser/Syntax.lean).
fn register_stx_items(b: &mut SnapshotBuilder) {
    // Syntax.cat := ident >> optional (":" prec)   (precedence idiom from
    // command_notation.rs::precedence — reuse that helper's shape)
    // Syntax.atom := strLit
    // Syntax.nonReserved := "&" strLit
    // Syntax.unary := ident:max "(" many1 stx ")"      e.g. optional(...), many(...)
    // Syntax.binary := ident:max "(" many1 stx ", " many1 stx ")"  e.g. orelse
    // Syntax.sepBy / sepBy1 := "sepBy(" ... ")" per the oracle source
    // Syntax.paren := "(" many1 stx ")"
    // EACH transcribed from the oracle source and adjusted to the dump.
    ...
}

pub(super) fn register(b: &mut SnapshotBuilder) {
    register_stx_items(b);
    // declare_syntax_cat: "declare_syntax_cat" ident (behavior)?
    // syntax: docComment? attributes? attrKind "syntax" (":" prec)?
    //         (name := ...)? (priority := ...)? many1(stx) ":" ident
    // syntaxAbbrev: docComment? "syntax" ident ":=" many1(stx)
    // macro_rules: docComment? attrKind "macro_rules" (kind)? matchAlts
    // macro: docComment? attrKind "macro" (":" prec)? (name/prio)?
    //        many1(macroArg) ":" ident " => " term-or-quot-seq tail
    // EACH registered with b.leading2("command", "<dump kind>", MAX_PREC, seq([...]))
    ...
}
```

The `...` bodies are transcription work with the dump as arbiter — the plan deliberately does not fabricate them: **every child slot comes from the dump**, the way `command_notation.rs`'s module doc embeds its dumps. Budget note for the implementer: this is the largest single porting step in the plan (comparable to M3b1's command_notation.rs task); the shapes are mechanical once the dump is in front of you. `macroArg`/`macroDollarArg` partially exist in `term_pragma.rs` (term-side) — check whether the command-side `macroArg` is the same node kind before creating a duplicate; if the kinds match, lift the helper to a shared location (`builtin/command.rs`'s `nd` idiom) rather than re-porting.

Register the module in `builtin/command.rs` (`mod command_syntax;` + `command_syntax::register(b);` in its `register`) and add `b.category("stx", LeadingIdentBehavior::Default)` in `builtin/mod.rs::builder()` next to the other categories — **pin the behavior**: if `$x:ident`-style leading-ident dispatch inside `stx` misbehaves, the oracle's `declare_syntax_cat`-equivalent registration for `stx` names the behavior (Lean/Parser/Syntax.lean's category registration).

- [ ] **Step 4: Green StxShapes; verify workspace**

Run: `cargo test -p leanr_syntax --test oracle_golden` — Expected: PASS on `StxShapes` (iterate against the dump); `QuotMacroRules` still absent (untracked). `cargo test --workspace` — Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_syntax tests/fixtures/syntax/StxShapes.lean tests/fixtures/syntax/StxShapes.stx.jsonl mise.toml
git commit -m "feat(syntax): stx category + syntax-family command shapes (M3b2b Task 6)"
```

---

### Task 7: `GrammarDelta` + overlay categories + `declare_syntax_cat`

The derivation return type generalizes (notation is no longer the only grammar-growing command), the overlay learns to carry new categories, and `category()` falls back to overlay categories on base miss. After this task, `declare_syntax_cat widgetish` followed by `` `(widgetish| ...) `` dynamic-quotes into the new category (empty until Task 8 registers productions into it).

**Files:**
- Modify: `crates/leanr_syntax/src/grammar/notation.rs` (`derive` → `derive_delta`), `crates/leanr_syntax/src/grammar/overlay.rs`, `crates/leanr_syntax/src/parse.rs` (`run_module` wiring, `command_may_grow_grammar`, `category()` fallback)

**Interfaces:**
- Produces (consumed by Task 8):
  ```rust
  // notation.rs
  pub enum GrammarDelta {
      Production(NotationSpec),
      NewCategory { name: String, behavior: LeadingIdentBehavior },
  }
  pub fn derive_delta(node: &SyntaxNode, kinds: &KindInterner) -> Option<GrammarDelta>;
  // overlay.rs
  pub fn register_category(&mut self, name: &str, behavior: LeadingIdentBehavior);
  pub fn has_category(&self, name: &str) -> bool;
  pub fn category_behavior(&self, name: &str) -> Option<LeadingIdentBehavior>;
  ```

- [ ] **Step 1: Failing tests**

In `overlay.rs`'s test module:

```rust
#[test]
fn overlay_categories_register_and_fingerprint() {
    let base = crate::builtin::snapshot();
    let mut ov = Overlay::new(&base);
    assert!(!ov.has_category("widgetish"));
    ov.register_category("widgetish", LeadingIdentBehavior::Default);
    assert!(ov.has_category("widgetish"));
    // A new category changes the effective fingerprint.
    let mut h1 = blake3::Hasher::new();
    Overlay::new(&base).fingerprint_into(&mut h1);
    let mut h2 = blake3::Hasher::new();
    ov.fingerprint_into(&mut h2);
    assert_ne!(h1.finalize(), h2.finalize());
}
```

In `parse.rs`'s test module (end-to-end through the public API):

```rust
#[test]
fn declare_syntax_cat_creates_a_quotable_category() {
    let snap = crate::builtin::snapshot();
    let src = "declare_syntax_cat widgetish\ndef q := `(widgetish| $x)\n";
    let r = crate::parse_module(src, &snap);
    assert_eq!(r.tree.text(), src);
    assert!(r.errors.is_empty(), "{:?}", r.errors);
    assert!(crate::canon::canon_jsonl(&r.tree).contains("widgetish.antiquot"));
}
```

(`$x` is the one thing an EMPTY category can parse inside a quotation — the category antiquot needs no productions; that is exactly why this test is possible before Task 8.)

Run: `cargo test -p leanr_syntax overlay_categories declare_syntax_cat` — Expected: FAIL.

- [ ] **Step 2: Implement**

`overlay.rs`: field `categories: HashMap<String, LeadingIdentBehavior>` on `Overlay` (init empty in `new`); the three methods are direct map ops. `fingerprint_into` (overlay.rs:177): after the tokens section, hash categories sorted by name (name bytes + the behavior byte, same encoding as the base fingerprint's behavior byte). `is_empty()` must also check `categories.is_empty()`.

`notation.rs`: introduce `GrammarDelta`; `derive_delta` dispatches on the outer kind — the two existing notation kinds map to `Production(...)` via the existing `derive_mixfix`/`derive_notation` (unchanged), and the `declare_syntax_cat` kind (as pinned by StxShapes' dump, expected `Lean.Parser.Command.syntaxCat`) maps to `NewCategory` (ident child = name; optional behavior child → `LeadingIdentBehavior`, defaulting `Default`; reuse `contains_error_or_missing` as the guard). Keep `derive` as a thin wrapper (`derive_delta(..).and_then(|d| match d { Production(s) => Some(s), _ => None })`) ONLY if other call sites exist — check with `grep -rn "notation::derive" crates/` and update call sites instead if the wrapper would be single-use.

`parse.rs`:
- `command_may_grow_grammar` (parse.rs:971): the kind-name check extends from the two notation kinds to the full grammar-growing set — make it a slice constant shared with Task 8:
  ```rust
  pub(crate) const GRAMMAR_GROWING_KINDS: &[&str] = &[
      "Lean.Parser.Command.mixfix",
      "Lean.Parser.Command.notation",
      "Lean.Parser.Command.syntaxCat",   // pinned by StxShapes dump
      // Task 8 appends: syntax, syntaxAbbrev, macro, and the imported
      // elab-family kinds.
  ];
  ```
- `run_module`'s grow arm (parse.rs:213-227): `derive` call becomes `derive_delta`; match the delta:
  ```rust
  if let Some(delta) = crate::grammar::notation::derive_delta(&subtree.root(), &subtree.kinds) {
      match delta {
          GrammarDelta::Production(spec) => { ps.overlay.register(spec); }
          GrammarDelta::NewCategory { name, behavior } => {
              ps.overlay.register_category(&name, behavior);
          }
      }
      ps.clear_category_cache();
  }
  ```
- `category()` fallback (parse.rs:2279): the current early-return on `snap_category` miss gains the overlay path. Borrow shape: `snap_category` returns `&'a Category` (snapshot lifetime); an overlay-backed category has no base `Category` to borrow, so bind an owned empty one:
  ```rust
  let owned_empty: Category;
  let cat: &Category = match self.snap_category(name) {
      Some(c) => c,
      None => match self.overlay.category_behavior(name) {
          Some(behavior) => {
              owned_empty = Category { ident_behavior: behavior, ..Default::default() };
              &owned_empty
          }
          None => {
              let at = self.pos;
              return Err(self.fail_expecting(&format!("<category {name}>"), at));
          }
      },
  };
  ```
  If the borrow checker rejects `&owned_empty` living across the `&mut self` uses below (the reason `snap_category` returns `'a`), the fix is mechanical: `cat` is only read via `dispatch(cat, ...)` and `cat.leading_parsers[...]`/`cat.trailing_parsers[...]` clones — for the empty category those are no-ops, so clone the (empty) `Category` value up front and pass `&owned_empty` only into `dispatch` calls, which take `&Category` by shared borrow before any `&mut self` call in each iteration. Restructure minimally; do not change behavior for base categories.

- [ ] **Step 3: Green + workspace**

Run: `cargo test -p leanr_syntax overlay_categories declare_syntax_cat` — Expected: PASS.
Run: `cargo test --workspace` — Expected: PASS (M3b1 notation threading behavior identical through the new enum).

- [ ] **Step 4: Commit**

```bash
git add crates/leanr_syntax
git commit -m "feat(syntax): GrammarDelta + overlay categories + declare_syntax_cat threading (M3b2b Task 7)"
```

---

### Task 8: Generalized derivation — `grammar/surface.rs`

The source-level twin of `leanr_grammar::descr`: walk a parsed `syntax`/`syntaxAbbrev`/`macro` (and import-arrived `elab`/`binder_predicate`) command tree into a `NotationSpec`, via the shared alias table. `macro_rules`/`elab_rules` stay shape-only (no delta). After this task `QuotMacroRules` goes green and the pass-list can grow with macro-defining files.

**Files:**
- Create: `crates/leanr_syntax/src/grammar/surface.rs`
- Modify: `crates/leanr_syntax/src/grammar/notation.rs` (`derive_delta` dispatches the new kinds to `surface`), `crates/leanr_syntax/src/grammar/mod.rs` (`pub mod surface;`), `crates/leanr_syntax/src/parse.rs` (`GRAMMAR_GROWING_KINDS` grows)
- Commit: `tests/fixtures/syntax/QuotMacroRules.lean` + dump (authored in Task 6), plus new `tests/fixtures/syntax/StxDeclareUse.lean` (+ dump)

**Interfaces:**
- Consumes: `alias::lookup` (Task 5), `NotationSpec`/`GrammarDelta`/`mangle_kind` machinery (notation.rs), overlay categories (Task 7).
- Produces:
  ```rust
  // surface.rs
  /// Derivation for the general command surface. None = this command
  /// derives nothing (shape-only command, or an item the walk cannot
  /// interpret — skip-and-record discipline: the command still parsed;
  /// a use-site of the underivable syntax diverges and stays off the
  /// pass-list, exactly like an uninterpretable imported entry).
  pub fn derive_surface(node: &SyntaxNode, kinds: &KindInterner) -> Option<GrammarDelta>;
  ```

- [ ] **Step 1: Author the second fixture; regenerate**

`tests/fixtures/syntax/StxDeclareUse.lean` (the acceptance jewel — category + productions + quotation use + direct use):

```lean
declare_syntax_cat widgetish
syntax "wob" : widgetish
syntax num : widgetish
syntax "grab[" widgetish "]" : term
macro_rules
  | `(grab[wob]) => `(0)
  | `(grab[$n:num]) => `($n)
#check grab[wob]
#check grab[42]
```

Run: `mise run fixtures:regen` (elab loop; `Stx*` glob from Task 6). The dump pins the derived kinds for anonymous `syntax` declarations (Lean's `mkNameFromParserSyntax` mangling — e.g. the `grab[...]` production's kind; compare against `mangle_kind`'s existing output for the same atom sequence and extend `mangle_kind_unescaped` where the general items introduce new atom classes).

- [ ] **Step 2: Failing state**

`git add tests/fixtures/syntax/QuotMacroRules.* tests/fixtures/syntax/StxDeclareUse.*` — now `cargo test -p leanr_syntax --test oracle_golden` fails on both (derivation missing). That is this task's failing test.

- [ ] **Step 3: Implement `surface.rs`**

```rust
//! Source-level derivation for the general `syntax`-command surface
//! (M3b2b Task 8) — the twin of `leanr_grammar::descr` (which walks the
//! same combinators as olean Exprs). Skip-and-record: any item outside
//! the walk returns None and the command derives nothing.

use super::alias::{self, AliasPrim};
use super::notation::{mangle_kind, trim_lean_symbol, GrammarDelta, NotationSpec};
use super::{LeadingIdentBehavior, Prim, LEAD_PREC, MAX_PREC};
use crate::kind::KindInterner;
use crate::tree::SyntaxNode;

pub fn derive_surface(node: &SyntaxNode, kinds: &KindInterner) -> Option<GrammarDelta> {
    let name = kinds.name(node.kind());
    match name {
        "Lean.Parser.Command.syntax" => derive_syntax_cmd(node, kinds),
        "Lean.Parser.Command.syntaxAbbrev" => derive_syntax_abbrev(node, kinds),
        "Lean.Parser.Command.macro" => derive_macro_cmd(node, kinds),
        // Imported shapes (kind names pinned against Mathlib dumps
        // during Step 5 — grep the sweep's divergence report):
        "Lean.Parser.Command.elab" => derive_elab_cmd(node, kinds),
        "Lean.Parser.Command.binderPredicate" => derive_binder_predicate(node, kinds),
        // Shape-only: parse fine, derive nothing.
        "Lean.Parser.Command.macro_rules" | "Lean.Parser.Command.elab_rules" => None,
        _ => None,
    }
}
```

The walkers (complete logic, layout indices pinned by the StxShapes/StxDeclareUse dumps):

- `derive_syntax_cmd`: children per the dump (docComment?, attrs?, attrKind, "syntax" atom, prec?, namedName?, namedPrio?, many1(stx) null node, ":" atom, category ident). Read category from the trailing ident; walk each stx item via `stx_item`; determine leading/trailing: **if the first item is `Syntax.cat` naming the same category**, it becomes the Pratt lhs (trailing production, `lhs_prec` from its precedence or the default per Lean's `checkLeftRec` — mirror `build_spec`'s existing split logic in notation.rs, which already implements exactly this for notation items); kind name from `namedName` if present else `mangle_kind` over the items' atom skeleton; build `NotationSpec { category, kind_name, leading, prec, lhs_prec, tokens, body }` → `GrammarDelta::Production`.
- `stx_item(node, kinds) -> Option<(Prim, MangleItem)>`, the core walk:
  ```rust
  match kinds.name(node.kind()) {
      "Lean.Parser.Syntax.atom" => Symbol(trim_lean_symbol(&strip_quotes(...))),
      "Lean.Parser.Syntax.nonReserved" => NonReservedSymbol(...),
      "Lean.Parser.Syntax.cat" => Prim::Category { name, rbp: prec.unwrap_or(0) },
      // rbp default: pin against the dump/Lean's `toParserDescr` —
      // a bare `term` in a syntax body maps to categoryParser at 0
      // unless followed by `:prec`; verify with StxShapes' `probe`.
      "Lean.Parser.Syntax.unary" => alias::lookup(fn_ident)? applied to inner,
      "Lean.Parser.Syntax.binary" => alias::lookup(fn_ident)? applied to both inners,
      "Lean.Parser.Syntax.sepBy" | "...sepBy1" => Prim::SepBy/SepBy1 { item, sep: trim, allow_trailing: per the allowTrailingSep arg },
      "Lean.Parser.Syntax.paren" => recurse (Seq of inner items),
      _ => return None,   // skip-and-record: unknown item kills the derivation
  }
  ```
  Postfix sugar (`term+`, `(term)?`, `term,*`): Lean elaborates these to `Syntax.unary`/`Syntax.sepBy` nodes BEFORE they hit the tree, or keeps dedicated kinds — **the StxShapes dump tells you which node kinds `many_of`/`opt_of`/`probe!`'s items carry**; write one arm per kind the dump shows, no speculative arms.
- `derive_syntax_abbrev`: ident = kind name (dump pins qualification), items walk as above, always leading, category — pin from the dump (syntaxAbbrev declares a `ParserDescr` constant usable by name; its registered production surface is what the dump's use-sites show — if StxShapes' `myNum` line has no category registration effect, model it as `None` + record, and note that abbrev *references* from other syntax bodies are a `Syntax.cat`-like item that resolves through... read `toParserDescr`'s handling; if it requires constant-reference resolution, that is skip-and-record territory for M3b2b, noted in the spec's skip list).
- `derive_macro_cmd`: pattern args (`macroArg` = strLit or `ident ":" cat` per the QuotMacroRules dump) map to Symbol/Category items; precedence/name/prio slots as in `derive_syntax_cmd`; RHS ignored entirely. `derive_elab_cmd`/`derive_binder_predicate`: same walkers over their (imported) layouts — implement the arms when Step 5's sweep data shows the layouts; until then they return None with a `// pinned in Step 5` comment (recorded, not guessed).
- `notation.rs::derive_delta` grows: after its existing kind dispatch, `_ => surface::derive_surface(node, kinds)` — one entry point for `run_module`.
- `GRAMMAR_GROWING_KINDS` (Task 7) appends `syntax`, `syntaxAbbrev`, `macro`, `macro_rules`, `elab`-family kinds — keep the list minimal (shape-only kinds like `macro_rules`/`elab_rules` never grow the grammar and stay OFF the list): syntax, syntaxAbbrev, macro, elab, binderPredicate, plus Task 7's three.
- Tokens: `NotationSpec.tokens` gets every Symbol atom (the existing `Overlay::register` inserts them — same path as notation).

- [ ] **Step 4: Green the fixtures**

Run: `cargo test -p leanr_syntax --test oracle_golden`
Expected: PASS on `QuotMacroRules` and `StxDeclareUse` (iterate: derived kind names against the dumps first — mangling mismatches are the likely first failure; then tree layout). Then `cargo test --workspace` — PASS.

- [ ] **Step 5: Pin the imported elab-family layouts from the sweep**

Run: `LEANR_SWEEP_LIMIT=500 mise run parse:mathlib` and inspect newly-green/still-red counts. Pick 2-3 red Mathlib files whose only divergence is an `elab`/`binder_predicate` declaration (the verbose CLI parse — `cargo run -p leanr_cli -- parse --verbose --path <roots> <file>` — names the first diverging command). Pin `Lean.Parser.Command.elab`'s actual kind name + child layout from those files' oracle dumps (cached under `target/leanr-stx-cache/`), implement `derive_elab_cmd`/`derive_binder_predicate` arms, re-sweep, confirm those files go green. If the layouts demand machinery beyond the existing walkers, record the gap (skip-and-record) and leave those arms returning None — the spec explicitly tolerates this; do not force it.

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_syntax tests/fixtures/syntax/QuotMacroRules.lean tests/fixtures/syntax/QuotMacroRules.stx.jsonl \
        tests/fixtures/syntax/StxDeclareUse.lean tests/fixtures/syntax/StxDeclareUse.stx.jsonl
git commit -m "feat(syntax): generalized syntax-command derivation via grammar/surface (M3b2b Task 8)"
```

---

### Task 9: Robustness — never-hang inputs, fuzz, depth-cache correctness

The quotation engine adds recursion (quots in quots) and backtracking paths (antiquot prefix unwinding); this task locks in the totality and cache-correctness properties before the acceptance gate.

**Files:**
- Modify: `crates/leanr_syntax/tests/never_hang.rs`, `crates/leanr_syntax/src/parse.rs` (test module)

- [ ] **Step 1: never-hang inputs**

Add to `never_hang.rs`, using the existing `in_worker` harness and input-shape idioms:

```rust
#[test]
fn nested_quotations_terminate() {
    for depth in [5usize, 20, 100, 1000] {
        let src = format!(
            "def a := {}1{}\n",
            "`(".repeat(depth),
            ")".repeat(depth)
        );
        in_worker(&format!("nested quots depth {depth}"), move || {
            let snap = leanr_syntax::builtin::snapshot();
            let r = leanr_syntax::parse_module(&src, &snap);
            assert_eq!(r.tree.text(), src, "lossless at depth {depth}");
        });
    }
}

#[test]
fn dollar_storms_terminate() {
    for src in [
        format!("def a := `({}x)\n", "$".repeat(500)),
        format!("def a := `({} x)\n", "$ ".repeat(500)),
        format!("def a := `(⟨{}⟩)\n", "$[".repeat(200)),
        "def a := $x\n".to_string(), // depth 0: plain failure, fast
    ] {
        in_worker("dollar storm", move || {
            let snap = leanr_syntax::builtin::snapshot();
            let r = leanr_syntax::parse_module(&src, &snap);
            assert_eq!(r.tree.text(), src, "lossless");
        });
    }
}
```

Run: `cargo test -p leanr_syntax --test never_hang` — Expected: PASS within budget. Any hang or panic is a Task 3/4 backtracking bug (the atomic-prefix restore path is the suspect: verify every early return in `antiquot`/`antiquot_splice` restores or finishes symmetrically).

- [ ] **Step 2: depth-keyed cache correctness test**

In `parse.rs`'s test module — the cache-poisoning regression this plan's `CatCacheKey.quot_depth` field prevents:

```rust
#[test]
fn category_cache_is_quot_depth_keyed() {
    // The same byte offset parses `term` both inside and outside a
    // quotation ($x legal only inside). If the cache ignored depth,
    // whichever ran first would poison the other.
    let snap = crate::builtin::snapshot();
    let src = "def a := `($x + $x)\n";
    let r = crate::parse_module(src, &snap);
    assert!(r.errors.is_empty(), "{:?}", r.errors);
    let n = crate::canon::canon_jsonl(&r.tree).matches("term.antiquot").count();
    assert_eq!(n, 2, "both $x occurrences must be antiquots");
}
```

Run: `cargo test -p leanr_syntax category_cache_is_quot_depth_keyed` — Expected: PASS (it already passes if Task 2's key field landed correctly; this pins it against regression).

- [ ] **Step 3: fuzz smoke**

Run: `mise run fuzz`
Expected: no findings in 60s per target. The `parse_module` target now reaches every quotation/antiquot path from arbitrary input against the builtin snapshot (which registers the new shapes) — no target changes needed.

- [ ] **Step 4: Commit**

```bash
git add crates/leanr_syntax
git commit -m "test(syntax): never-hang quotation storms + depth-keyed cache pin (M3b2b Task 9)"
```

---

### Task 10: M3b2b final gate — sweep growth + acceptance recording

**Files:**
- Modify: `tests/fixtures/syntax/mathlib-passlist.txt` (grown), `docs/superpowers/specs/2026-07-16-m3b2b-general-surface-design.md` (acceptance recorded)
- Possibly modify: `scripts/parse-acceptance.sh` (only if its fixture-diff steps don't glob the new `Quot*`/`Stx*` fixtures — read it; the M3b2a fifth step's pattern is the template)

- [ ] **Step 1: Full hermetic gates**

Run: `cargo test --workspace && mise run lint && mise run lint:deps`
Expected: all PASS.

- [ ] **Step 2: Parse-acceptance script**

Run: `mise run parse:acceptance`
Expected: all steps green — fresh oracle dumps for the full fixture corpus (now including `Quot*`/`Stx*`) match committed, release tests, CLI dump diffs, fuzz smoke, import corpus. If any step's glob misses the new fixtures, extend it (same shape as the existing per-fixture loops) and re-run.

- [ ] **Step 3: Grow the pass-list (the acceptance number)**

Run: `mise run passlist:update` (parallel now — Task 1), then `mise run parse:mathlib`.
Expected: 0 regressions; `git diff tests/fixtures/syntax/mathlib-passlist.txt` shows growth over Task 1's re-baseline. Spot-check 3-5 newly-green files actually USE the M3b2b surface (`grep -l 'macro_rules\|syntax\|`(' on them) — the honest-measurement check. Record: files swept, green count, delta vs Task 1 baseline.

- [ ] **Step 4: Record acceptance in the spec**

Append to the spec's Goal section (the M3a/M3b1/M3b2a convention), with real numbers:

```markdown
**Acceptance recorded (2026-MM-DD):** hermetic corpus green (QuotBasic/
QuotAntiquot/QuotSplice/StxShapes/QuotMacroRules/StxDeclareUse — byte
round-trip + oracle-tree equality); all gates green (workspace tests,
lint, deps, parse-acceptance incl. new corpus, fuzz both targets,
never-hang quotation storms). Parallel full-closure sweep: NNNN files,
NNN green on the committed pass-list (Task 1 baseline NNN → +NN from
the general surface), 0 regressions. Remaining divergence classes
recorded for M3b3: <top skip reasons from the sweep>.
```

- [ ] **Step 5: Commit**

```bash
git add tests/fixtures/syntax/mathlib-passlist.txt scripts/parse-acceptance.sh \
        docs/superpowers/specs/2026-07-16-m3b2b-general-surface-design.md
git commit -m "test(syntax): grow Mathlib pass-list + record M3b2b acceptance (M3b2b Task 10)"
```

---

## Plan Self-Review Notes (resolved inline)

- **Spec coverage:** sweep parallelization + re-baseline → Task 1; quotation shapes + depth plumbing (`incQuotDepth`/`decQuotDepth`, dynamic quot) → Task 2; uniform antiquot alternative at category/Node/leaf entry + `withoutAnonymousAntiquot` → Task 3; splices/scopes in repetition positions + descr flags → Task 4; one shared alias table → Task 5; general command shapes incl. the `stx` category → Task 6; `GrammarDelta`, overlay categories, `declare_syntax_cat` → Task 7; generalized derivation keyed on command kind incl. imported `elab`-family recognition, `macro`/`elab` desugar, shape-only rules commands → Task 8; never-panic/never-hang + fuzz + depth-keyed cache → Task 9; acceptance pattern (hermetic corpus + ratchet growth, no numeric target) → Tasks 6-8 fixtures + Task 10. Spec's "namespace-qualified kind naming deferred to M3b3" → not implemented anywhere here, consistent; skip-and-record → surface.rs `None` paths + Task 8 Step 5's recorded gaps.
- **Deliberate scope notes:** syntaxAbbrev cross-reference resolution may land as skip-and-record (Task 8 records the decision in the spec if so); `elab`/`binder_predicate` derivation arms are implemented from sweep evidence (Task 8 Step 5) and may remain recorded-None if their layouts demand out-of-scope machinery; leaf antiquot hooks beyond `ident` are added on corpus demand (Task 3 Step 4.3).
- **Empirical pins** (fixture-decided, each with a decision procedure, no TBDs): quotation node set + command-alternative layout (Task 2 dump); antiquot child layout, `$$` escape, `:name` suffix semantics, null-slot placement (Task 3 dump); `,*` token boundary, splice pseudo-kind names, sepBy-splice completion semantics (Task 4 dump); every command/stx-item kind name + layout (Task 6 dumps); derived-kind mangling for anonymous `syntax` (Task 8 dump); imported elab-family layouts (Task 8 Step 5, sweep-driven).
- **Type consistency check:** `Prim::{IncQuotDepth, DecQuotDepth, DynamicQuotBody}` + `inc_quot_depth`/`dec_quot_depth` (Task 2) consumed by Tasks 3/4/6; `try_antiquot(name, kind_name, anonymous) -> Option<PResult>` and `Prim::WithoutAnonymousAntiquot` (Task 3) consumed by Task 4 and descr; `try_antiquot_splice(kind_name, suffix, scope_body)` (Task 4) called from many/sepBy/Optional arms; `alias::{AliasPrim, lookup}` public path (Task 5) consumed by surface.rs (Task 8) and re-exported shim (leanr_grammar); `GrammarDelta::{Production, NewCategory}` + `derive_delta` + `register_category`/`has_category`/`category_behavior` (Task 7) consumed by Task 8 and run_module; `derive_surface` (Task 8) dispatched from `derive_delta`; `GRAMMAR_GROWING_KINDS` introduced Task 7, extended Task 8.
- **Task-by-task green:** every fixture is committed in the task that makes it green (`oracle_golden` auto-discovers); the one deliberate exception (`QuotMacroRules`, authored Task 6, committed Task 8) is called out with handling instructions in both tasks.
