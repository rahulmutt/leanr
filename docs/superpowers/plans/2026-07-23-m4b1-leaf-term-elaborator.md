# M4b-1 Leaf Term Elaborator Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** A new `leanr_elab` crate whose `TermElabM` elaborates leaf terms — string literals, `Sort`/`Type`/`Prop`, global-constant identifiers, type ascription `(e : T)`, and holes `_` — into `Expr`, agreeing byte-for-byte with the pinned oracle on a committed differential corpus, behind a new `mise run elab:fast` regression gate.

**Architecture:** `leanr_elab` sits on the finished `MetaM` core. `TermElabM<'e>` wraps `leanr_meta::MetaCtx<'e>` and adds only `level_names`. `elab_term` dispatches on the interned `SyntaxKind` name of a `leanr_syntax::SyntaxNode` to one builtin leaf elaborator each; a kind with no registered elaborator is a hard `ElabError::UnsupportedSyntax`. The oracle harness mirrors M4a exactly: `dump_elab.lean` emits canonical Expr-JSON, and a hermetic `oracle_elab.rs` replays it (parse the source through `leanr_syntax`, elaborate, canonicalize, compare). The canonical scheme gains one node (`lmvar`) for unassigned universe metavariables that universe-polymorphic constants produce.

**Tech Stack:** Rust 2021, `leanr_meta` (`MetaCtx`, `is_def_eq`, `infer_type`, `instantiate_mvars`, `MVarDecl`/`MVarKind`/`LMVarId`), `leanr_kernel` (term bank `Store`: `expr_const`/`expr_sort`/`expr_lit_str`/`expr_mvar`/`level_*`; `EnvView`; `ConstantInfo`), `leanr_syntax` (`SyntaxNode`, `KindInterner`, `GrammarSnapshot`, `builtin::snapshot`), `serde_json` (tests only).

**Spec:** [docs/superpowers/specs/2026-07-23-m4b1-leaf-term-elaborator-design.md](../specs/2026-07-23-m4b1-leaf-term-elaborator-design.md)

## Global Constraints

- **Oracle pin:** `leanprover/lean4:v4.33.0-rc1`, Mathlib `c732b96d05efdb1fb84511dfdc24a8f70005ae99` (`lean-toolchain` / `mathlib-pin`). Never bump outside a milestone boundary.
- **Oracle source is the specification.** `LEAN=$(lean --print-prefix)/src/lean/Lean/Elab` holds the pinned elaborator source. Where this plan's transcription and the source disagree, **the source wins** — fix the transcription and record the correction in the commit message. Never transcribe from memory; open the cited file. Line numbers are from v4.33.0-rc1; if a citation is off by a few lines, the surrounding `def` name is authoritative — re-grep.
- **The fixture is authoritative over this plan's expected values.** Every "Expected" `Expr`-JSON literal in this plan is the author's transcription of what the oracle *should* emit. When `dump_elab.lean` is run under the pinned toolchain (Task 4), the committed `elab-queries.jsonl` is ground truth; if it disagrees with a value written here, the fixture wins and the implementation matches the fixture (not this plan's prose).
- **Kernel & olean TCB untouched.** This plan does not modify `leanr_kernel` or `leanr_olean` (verify `git status --short crates/leanr_kernel crates/leanr_olean` is empty before every commit). `leanr_meta`'s **`src/`** is untouched too (only its shared test-support file changes, in Task 2).
- **Signature reconciliation rule (from the M4a plans, it worked):** if the compiler reports a mismatch between this plan's code and a real API, read the real signature (`crates/leanr_kernel/src/bank/`, `crates/leanr_meta/src/lib.rs`, `crates/leanr_syntax/src/`) and adjust **this plan's code**, never the depended-on crate.
- **Failure semantics:** every `leanr_elab` failure is *incompleteness*, never unsoundness — the kernel independently re-checks anything elaboration ultimately produces. New failure modes are `ElabError` variants, never a wrong `ExprId`.
- **Named seams, no silent divergence.** Every form deliberately not built this slice — binders, application, `num`/`char` literals, coercions, macro expansion, `open`/alias/dot-notation resolution, postponement — must surface as a named `ElabError` branch or a doc-commented seam citing the slice that owns it. A syntax kind with no elaborator returns `ElabError::UnsupportedSyntax(kind_name)`; it is never silently skipped.
- **Both gates stay green after every task.** `mise run meta:fast` (existing) and `mise run elab:fast` (new, from Task 4) must pass at the end of every task. Each implementation task commits only fixtures its own code answers correctly — never a fixture the current code diverges on.
- **Workflows:** named mise tasks; CI runs `mise run ci`. Local fixture regen is `mise run fixtures:regen` (needs the elan toolchain; never runs in CI).

## Prerequisites (verify, do not redo)

M4a plans 1–4 are merged. Confirm:

```bash
cat lean-toolchain                                   # leanprover/lean4:v4.33.0-rc1
cargo test --release -p leanr_meta 2>&1 | tail -1    # green
cargo test --release -p leanr_syntax 2>&1 | tail -1  # green
mise run meta:fast 2>&1 | tail -3                    # green
```

`leanr_meta` exposes `MetaCtx`, `Config`, `MetaError`, `MVarDecl`, `MVarKind`, `MVarId`, `LMVarId`, `MetavarContext`, `TransparencyMode`; `MetaCtx::infer_type`, `is_def_eq`, `instantiate_mvars`. `leanr_syntax` exposes `parse_module`, `SyntaxTree`/`SyntaxNode`, `KindInterner` (`name`/`lookup`/`intern`), `builtin::snapshot() -> GrammarSnapshot`. The M4a differential gate is `crates/leanr_meta/tests/oracle_fast.rs` over `tests/fixtures/meta/{Meta0.olean,meta-queries.jsonl}`, with the canonical Expr/Level-JSON scheme in `crates/leanr_meta/tests/support/mod.rs`.

Read once before starting (regions this plan transcribes):

```bash
LEAN=$(lean --print-prefix)/src/lean/Lean/Elab
sed -n '/builtin_term_elab.*prop/,+40p' $LEAN/BuiltinTerm.lean   # elabProp/elabSort/elabType
grep -n 'elabStrLit\|elabIdent\|elabParen\|elabHole\|resolveName\|mkFreshLevelMVar\|elabTermEnsuringType\|ensureHasType' $LEAN/*.lean
```

## File Structure

Created / modified by this plan:

| Path | Responsibility |
|---|---|
| `crates/leanr_syntax/src/parse.rs` (modify) | add `pub fn parse_term(src, snap) -> ParseResult` |
| `crates/leanr_meta/tests/support/mod.rs` (modify) | `lmvar` in the canonical scheme; `fixture_in`/`replay_fixture_in(subdir, name)` |
| `crates/leanr_meta/tests/oracle_fast.rs` (modify) | one unit test for the `lmvar` round-trip |
| `crates/leanr_elab/Cargo.toml` (create) | new crate manifest |
| `crates/leanr_elab/src/lib.rs` (create) | crate root; re-exports |
| `crates/leanr_elab/src/error.rs` (create) | `ElabError` |
| `crates/leanr_elab/src/elab.rs` (create) | `TermElabM` state + `elab_term`/`elab_term_ensuring_type` + fresh-mvar helpers |
| `crates/leanr_elab/src/dispatch.rs` (create) | kind-name → elaborator table |
| `crates/leanr_elab/src/builtin/mod.rs` (create) | builtin submodule root |
| `crates/leanr_elab/src/builtin/lit.rs` (create) | string literal |
| `crates/leanr_elab/src/builtin/sort.rs` (create) | `Sort`/`Type`/`Prop` |
| `crates/leanr_elab/src/builtin/ident.rs` (create) | identifier → global const |
| `crates/leanr_elab/src/builtin/ascription.rs` (create) | `(e : T)` |
| `crates/leanr_elab/src/builtin/hole.rs` (create) | `_` |
| `crates/leanr_elab/src/resolve.rs` (create) | global-name resolution |
| `crates/leanr_elab/tests/oracle_elab.rs` (create) | the differential gate |
| `crates/leanr_elab/tests/support/` (create) | `#[path]`-includes the meta scheme (Task 4) |
| `tests/fixtures/elab/Elab0.lean` (+ `.olean`) (create) | fixture environment |
| `tests/fixtures/elab/dump_elab.lean` (create) | the dumper |
| `tests/fixtures/elab/elab-queries.jsonl` (create) | committed corpus (grown per task) |
| `Cargo.toml` (modify) | add `crates/leanr_elab` to workspace members |
| `mise.toml` (modify) | `elab:fast` task; `fixtures:regen-elab`; wire into `test`/`ci`/`fixtures:regen` |

---

### Task 1: `parse_term` in `leanr_syntax`

The elaborator's input is a single term, but the only public parse entry is `parse_module` (whole file). Expose a term-category parse that reuses the existing `Prim::Category` machinery, on the same `MIN_STACK_BYTES` worker thread `parse_module` uses.

**Files:**
- Modify: `crates/leanr_syntax/src/parse.rs`
- Modify: `crates/leanr_syntax/src/lib.rs` (re-export if the crate re-exports `parse_module`; match that pattern)

**Interfaces:**
- Consumes: `GrammarSnapshot`, `Ps`, `Prim`, `ParseResult`, `MIN_STACK_BYTES` (all already in `parse.rs`).
- Produces: `pub fn parse_term(src: &str, snap: &GrammarSnapshot) -> ParseResult` — parses `src` as one `term`-category node; the returned `ParseResult` exposes the `SyntaxTree`/root exactly as `parse_module`'s does (same `ParseResult` type).

**Background:** `run_module` starts a `module` node, runs the header, then loops `Prim::Category { name: "command", rbp: 0 }`. A term parse is the single-category analogue: start a synthetic root, run `Prim::Category { name: "term", rbp: 0 }` once, finish. Wrap it in the same `std::thread::scope` + `MIN_STACK_BYTES` worker as `parse_module` (the Pratt recursion needs the deep stack — Global Constraint: never segfault).

- [ ] **Step 1: Write the failing test**

Add to `crates/leanr_syntax/src/parse.rs` `#[cfg(test)] mod tests` (or the crate's parse test file, matching where `parse_module` tests live):

```rust
    #[test]
    fn parse_term_roundtrips_a_leaf() {
        let snap = crate::builtin::snapshot();
        for src in ["\"hello\"", "Nat", "Type", "Prop", "(x : Nat)", "_"] {
            let res = super::parse_term(src, &snap);
            assert_eq!(res.tree.text(), src, "parse_term must be lossless for {src:?}");
        }
    }
```

(If `ParseResult`'s field is not `tree`, read the struct in `parse.rs` and use the real accessor — Signature reconciliation rule.)

- [ ] **Step 2: Run the test to verify it fails**

Run: `cargo test -p leanr_syntax parse_term_roundtrips_a_leaf 2>&1 | tail -5`
Expected: FAIL — `parse_term` not found.

- [ ] **Step 3: Implement `parse_term`**

Add to `crates/leanr_syntax/src/parse.rs`, next to `parse_module`:

```rust
/// Parse `src` as a single `term`-category node. The elaborator's input
/// entry point (M4b-1): `parse_module` parses whole files, but a term
/// elaborator consumes one term. Same `MIN_STACK_BYTES` worker as
/// `parse_module` — the Pratt recursion needs the deep stack.
pub fn parse_term(src: &str, snap: &GrammarSnapshot) -> ParseResult {
    std::thread::scope(|scope| {
        let worker = std::thread::Builder::new()
            .stack_size(MIN_STACK_BYTES)
            .spawn_scoped(scope, || parse_term_here(src, snap))
            .expect("spawn the parse worker thread");
        match worker.join() {
            Ok(r) => r,
            Err(panic) => std::panic::resume_unwind(panic),
        }
    })
}

fn parse_term_here(src: &str, snap: &GrammarSnapshot) -> ParseResult {
    let kinds = snap.kinds();
    // A synthetic single-node root, mirroring `run_module`'s `module`
    // wrap, so `finish` sees exactly one balanced root. Reuse "module"
    // as the root kind (it is only a container here); the term is its
    // single child.
    let root = kinds.lookup("module").expect("interned by builtin::snapshot");
    let mut ps = Ps::new(src, snap);
    ps.start(root);
    let _ = ps.run(&Prim::Category { name: "term".into(), rbp: 0 });
    finish_parse(ps, snap) // whatever `run_module` calls to produce a ParseResult
}
```

Read `run_module`'s tail to see how it turns a finished `Ps` into a `ParseResult` (it builds events → `build_tree`); call the identical path from `parse_term_here`. If `run_module` inlines that finish, extract a small shared `fn finish_parse(ps, snap) -> ParseResult` and call it from both (DRY) — a pure refactor with `parse_module`'s existing tests as the safety net.

- [ ] **Step 4: Run tests**

Run: `cargo test -p leanr_syntax 2>&1 | tail -5`
Expected: PASS (the new test and every existing parse test).

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_syntax/src/parse.rs crates/leanr_syntax/src/lib.rs
git commit -m "feat(syntax): parse_term — single term-category parse entry (M4b-1 Task 1)"
```

---

### Task 2: `lmvar` in the canonical scheme + subdir fixture helpers

A universe-polymorphic constant (e.g. `List`) elaborates to a term carrying an unassigned **level metavariable**. The canonical Level-JSON scheme cannot represent it — `encode_level` panics on `LevelRow::MVar`. Add one node, `{"k":"lmvar","i":N}`, numbered in first-occurrence order per query record (as expr mvars already are). Also add `fixture_in`/`replay_fixture_in(subdir, name)` so `leanr_elab`'s gate can point the shared loader at `tests/fixtures/elab`.

**Files:**
- Modify: `crates/leanr_meta/tests/support/mod.rs`
- Modify: `crates/leanr_meta/tests/oracle_fast.rs` (the round-trip unit test)

**Interfaces:**
- Consumes: `Store::level_mvar(base, Option<NameId>) -> Result<LevelId, _>`, `EncSt` (the per-record first-occurrence numbering state), `synth_name` (mints a stable `NameId` from a prefix+index), `LevelRow::MVar(Option<NameId>)`.
- Produces (in `support/mod.rs`):
  - `encode_level` now takes `&mut EncSt` and emits `{"k":"lmvar","i":N}` on `LevelRow::MVar`.
  - `decode_level` handles `"lmvar"`, interning a fresh level mvar per distinct `i` via a `HashMap<u64, NameId>` threaded like `mvars`.
  - `pub fn fixture_in(subdir: &str, name: &str) -> PathBuf` and `pub fn replay_fixture_in(subdir: &str, name: &str) -> Replayed`; existing `fixture`/`replay_fixture` delegate with `"meta"`.

**Background:** `encode_expr` already threads `&mut EncSt st` and numbers expr mvars in first-occurrence order (`EncSt` holds a `HashMap` for expr mvars). `encode_level` is currently `(store, base, l)` with no state — it is called from `encode_expr`'s `Sort`/`Const` arms. Add a level-mvar map to `EncSt` (mirroring the expr-mvar map) and thread `st` into `encode_level`. On the decode side, `decode_level` currently takes `(scratch, base, v)`; give it a `&mut HashMap<u64, NameId>` for level mvars, allocate a fresh `NameId` (via `synth_name(scratch, base, "u", i)`) the first time each `i` is seen, and intern `scratch.level_mvar(base, Some(nid))`.

- [ ] **Step 1: Write the failing test**

Add to `crates/leanr_meta/tests/oracle_fast.rs`:

```rust
#[test]
fn encode_decode_level_mvar_roundtrips() {
    use serde_json::json;
    let mut scratch = leanr_kernel::bank::Store::scratch();
    // Build `Sort (max ?u0 ?u1)` where ?u0/?u1 are two distinct mvars,
    // plus a second occurrence of ?u0, so numbering + sharing are both
    // exercised.
    let n0 = support::synth_name(&mut scratch, None, "u", 0);
    let n1 = support::synth_name(&mut scratch, None, "u", 1);
    let u0 = scratch.level_mvar(None, Some(n0)).unwrap();
    let u1 = scratch.level_mvar(None, Some(n1)).unwrap();
    let m = scratch.level_max(None, u0, u1).unwrap();
    let mm = scratch.level_max(None, m, u0).unwrap(); // ?u0 appears again
    let level_json = {
        let mut st = support::EncSt::new();
        support::encode_level(&scratch, None, mm, &mut st)
    };
    // First occurrence order: ?u0 -> 0, ?u1 -> 1, reuse -> 0.
    assert_eq!(
        level_json,
        json!({"k":"max",
               "a":{"k":"max","a":{"k":"lmvar","i":0},"b":{"k":"lmvar","i":1}},
               "b":{"k":"lmvar","i":0}})
    );
    // Decode back and re-encode: must be identical (round-trip).
    let mut lm = std::collections::HashMap::new();
    let back = support::decode_level(&mut scratch, None, &level_json, &mut lm);
    let mut st2 = support::EncSt::new();
    assert_eq!(support::encode_level(&scratch, None, back, &mut st2), level_json);
}
```

- [ ] **Step 2: Run the test to verify it fails**

Run: `cargo test -p leanr_meta encode_decode_level_mvar_roundtrips 2>&1 | tail -8`
Expected: FAIL to compile — `encode_level`/`decode_level` signatures don't match; `EncSt::new` may differ. (Read `EncSt`'s real constructor and adjust the test call — Signature reconciliation rule.)

- [ ] **Step 3: Extend the scheme**

In `crates/leanr_meta/tests/support/mod.rs`:

Add a level-mvar map to `EncSt` beside its expr-mvar map (same first-occurrence pattern — a `HashMap<NameId, u64>` plus a counter, or reuse the existing helper that assigns the next index for expr mvars, keyed in a separate map). Then:

```rust
pub fn encode_level(store: &Store, base: Option<&Store>, l: LevelId, st: &mut EncSt) -> Value {
    match *store.level_row(base, l) {
        LevelRow::Zero => json!({"k": "zero"}),
        LevelRow::Succ(u) => json!({"k": "succ", "u": encode_level(store, base, u, st)}),
        LevelRow::Max(a, b) => json!({"k": "max",
            "a": encode_level(store, base, a, st), "b": encode_level(store, base, b, st)}),
        LevelRow::IMax(a, b) => json!({"k": "imax",
            "a": encode_level(store, base, a, st), "b": encode_level(store, base, b, st)}),
        LevelRow::Param(n) => json!({"k": "param", "n": name_to_string(store, base, n)}),
        LevelRow::MVar(n) => json!({"k": "lmvar", "i": st.level_mvar_index(n)}),
    }
}
```

`st.level_mvar_index(n: Option<NameId>) -> u64` returns the first-occurrence index for this level mvar (assigning the next unused index on first sight), exactly as the expr-mvar side numbers `Node::Mvar`. Update `encode_expr`'s `Sort`/`Const` arms to pass `st` into `encode_level`.

Then `decode_level`:

```rust
pub fn decode_level(
    scratch: &mut Store, base: Option<&Store>, v: &Value,
    lmvars: &mut HashMap<u64, NameId>,
) -> LevelId {
    let k = v["k"].as_str().expect("decode_level: missing k");
    match k {
        "zero" => scratch.level_zero(base).expect("intern level zero"),
        "succ" => { let u = decode_level(scratch, base, &v["u"], lmvars);
                    scratch.level_succ(base, u).expect("succ") }
        "max"  => { let a = decode_level(scratch, base, &v["a"], lmvars);
                    let b = decode_level(scratch, base, &v["b"], lmvars);
                    scratch.level_max(base, a, b).expect("max") }
        "imax" => { let a = decode_level(scratch, base, &v["a"], lmvars);
                    let b = decode_level(scratch, base, &v["b"], lmvars);
                    scratch.level_imax(base, a, b).expect("imax") }
        "param" => { let nid = decode_name(scratch, base, v["n"].as_str().expect("n"));
                     scratch.level_param(base, Some(nid)).expect("param") }
        "lmvar" => {
            let i = v["i"].as_u64().expect("lmvar i");
            let nid = *lmvars.entry(i).or_insert_with(|| synth_name(scratch, base, "u", i));
            scratch.level_mvar(base, Some(nid)).expect("intern level mvar")
        }
        other => panic!("decode_level: unknown level kind {other:?}"),
    }
}
```

Update `decode_expr`'s `Sort`/`Const` arms and every existing `decode_level` caller to thread a `&mut HashMap<u64, NameId>` for level mvars (add one beside each call site's existing `mvars` map). Add the two `*_in` helpers:

```rust
pub fn fixture_in(subdir: &str, name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("../../tests/fixtures").join(subdir).join(name)
}
pub fn fixture(name: &str) -> PathBuf { fixture_in("meta", name) }
pub fn replay_fixture_in(subdir: &str, name: &str) -> Replayed { /* body of replay_fixture, using fixture_in(subdir, name) */ }
pub fn replay_fixture(name: &str) -> Replayed { replay_fixture_in("meta", name) }
```

- [ ] **Step 4: Run tests**

Run: `cargo test -p leanr_meta 2>&1 | tail -5 && mise run meta:fast 2>&1 | tail -3`
Expected: PASS — the new round-trip test AND the whole existing meta gate (the corpus has no level mvars today, so the threaded signatures must not change its output).

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_meta/tests/support/mod.rs crates/leanr_meta/tests/oracle_fast.rs
git commit -m "test(meta): canonical scheme gains lmvar node + subdir fixture helpers (M4b-1 Task 2)"
```

---

### Task 3: `leanr_elab` crate skeleton, `TermElabM`, dispatch

Stand up the crate: `TermElabM` over `MetaCtx`, the `ElabError` type, the kind-name dispatch table returning `UnsupportedSyntax` for everything, and the two entry points. No leaf elaborator yet — this task's deliverable is "the crate compiles and an unregistered kind errors cleanly."

**Files:**
- Create: `crates/leanr_elab/Cargo.toml`, `src/lib.rs`, `src/error.rs`, `src/elab.rs`, `src/dispatch.rs`
- Modify: `Cargo.toml` (workspace members)

**Interfaces:**
- Consumes: `leanr_meta::{MetaCtx, MetaError, MVarDecl, MVarKind, MVarId, LMVarId}`, `leanr_kernel::bank::{ExprId, LevelId, NameId, Store}`, `leanr_kernel::EnvView`, `leanr_syntax::{SyntaxNode, KindInterner}`.
- Produces:
  - `pub struct TermElabM<'e>` with `pub mctx: leanr_meta::MetaCtx<'e>` and `pub level_names: Vec<NameId>`.
  - `pub fn TermElabM::new(mctx: MetaCtx<'e>) -> Self`.
  - `pub fn TermElabM::elab_term(&mut self, node: &SyntaxNode, kinds: &KindInterner, expected: Option<ExprId>) -> Result<ExprId, ElabError>`.
  - `pub fn TermElabM::elab_term_ensuring_type(&mut self, node: &SyntaxNode, kinds: &KindInterner, expected: Option<ExprId>) -> Result<ExprId, ElabError>`.
  - `pub enum ElabError { UnsupportedSyntax(String), UnknownIdent(String), AmbiguousIdent(String), TypeMismatch { expected: ExprId, got: ExprId }, Meta(MetaError) }` with `impl From<MetaError>`.

**Background:** the dispatch key is the term node's interned kind name: `kinds.name(node.kind())`. `elab_term` looks it up in a `match` (or a small map) and calls the registered elaborator; an unmatched name is `UnsupportedSyntax(name.to_string())`. `elab_term_ensuring_type` calls `elab_term`, then if `expected` is `Some(t)` runs `is_def_eq(infer_type(result), t)`; a `false` result is `TypeMismatch` (Global Constraint: coercion is M4b-3, so mismatch errors, never coerces). Passing the `kinds` interner explicitly (not storing it) keeps `TermElabM` independent of any single parse.

- [ ] **Step 1: Create the crate manifest and register it**

`crates/leanr_elab/Cargo.toml`:

```toml
[package]
name = "leanr_elab"
version = "0.0.0"
edition = "2021"
publish = false

[dependencies]
leanr_kernel = { path = "../leanr_kernel" }
leanr_meta = { path = "../leanr_meta" }
leanr_syntax = { path = "../leanr_syntax" }

[dev-dependencies]
leanr_olean = { path = "../leanr_olean" }
serde_json = "1"
```

(Match versions/features to how `leanr_meta/Cargo.toml` pins `serde_json`.) Add `"crates/leanr_elab"` to the workspace `members` in the root `Cargo.toml`.

- [ ] **Step 2: Write the failing test**

`crates/leanr_elab/src/dispatch.rs` (test at the bottom):

```rust
#[cfg(test)]
mod tests {
    use crate::error::ElabError;

    #[test]
    fn unregistered_kind_is_unsupported() {
        // A synthetic node of an unknown kind must dispatch to
        // UnsupportedSyntax carrying the kind name — never a panic,
        // never a wrong ExprId.
        let name = crate::dispatch::elaborator_name_for("Lean.Parser.Term.match");
        assert!(name.is_none(), "match is not a leaf and must not be registered");
    }
}
```

Here `elaborator_name_for(kind: &str) -> Option<&'static str>` is a thin, testable predicate over the registration table (returns `Some(_)` only for registered leaf kinds). It lets us test the table without constructing a full `SyntaxNode`.

- [ ] **Step 3: Run the test to verify it fails**

Run: `cargo test -p leanr_elab unregistered_kind_is_unsupported 2>&1 | tail -8`
Expected: FAIL to compile — crate/module not yet defined.

- [ ] **Step 4: Implement the skeleton**

`src/error.rs`:

```rust
use leanr_meta::MetaError;
use leanr_kernel::bank::ExprId;

#[derive(Debug)]
pub enum ElabError {
    /// A syntax kind with no leaf elaborator in M4b-1. Carries the kind
    /// name. Named seam: binders/app/num/char/match/etc. land in later
    /// M4b slices; until then their kinds arrive here, never silently.
    UnsupportedSyntax(String),
    UnknownIdent(String),
    AmbiguousIdent(String),
    /// ensureHasType mismatch. In slice 1 this errors; coercion
    /// insertion (mkCoe) is M4b-3.
    TypeMismatch { expected: ExprId, got: ExprId },
    Meta(MetaError),
}

impl From<MetaError> for ElabError {
    fn from(e: MetaError) -> Self { ElabError::Meta(e) }
}
```

`src/dispatch.rs`:

```rust
use leanr_kernel::bank::ExprId;
use leanr_syntax::{KindInterner, SyntaxNode};
use crate::elab::TermElabM;
use crate::error::ElabError;

/// The registered leaf kinds. Returns a stable label for a registered
/// kind, `None` otherwise — the single source of truth for "is this a
/// leaf we elaborate". Grown as Tasks 4–6 land their elaborators.
pub fn elaborator_name_for(kind: &str) -> Option<&'static str> {
    match kind {
        // filled in by Tasks 4–6
        _ => None,
    }
}

/// Dispatch a term node to its leaf elaborator. Unregistered kind ->
/// UnsupportedSyntax (never a panic, never a wrong ExprId).
pub fn dispatch(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let name = kinds.name(node.kind());
    match name {
        // Tasks 4–6 add one arm each, delegating to builtin::*.
        other => Err(ElabError::UnsupportedSyntax(other.to_string())),
    }
}
```

`src/elab.rs`:

```rust
use leanr_kernel::bank::{ExprId, NameId};
use leanr_meta::MetaCtx;
use leanr_syntax::{KindInterner, SyntaxNode};
use crate::dispatch;
use crate::error::ElabError;

pub struct TermElabM<'e> {
    pub mctx: MetaCtx<'e>,
    /// Universe parameters in scope, for `Sort u`. Empty for closed leaf
    /// terms; the field exists because `sort` reads it.
    pub level_names: Vec<NameId>,
}

impl<'e> TermElabM<'e> {
    pub fn new(mctx: MetaCtx<'e>) -> Self {
        TermElabM { mctx, level_names: Vec::new() }
    }

    pub fn elab_term(
        &mut self, node: &SyntaxNode, kinds: &KindInterner, expected: Option<ExprId>,
    ) -> Result<ExprId, ElabError> {
        dispatch::dispatch(self, node, kinds, expected)
    }

    pub fn elab_term_ensuring_type(
        &mut self, node: &SyntaxNode, kinds: &KindInterner, expected: Option<ExprId>,
    ) -> Result<ExprId, ElabError> {
        let e = self.elab_term(node, kinds, expected)?;
        if let Some(t) = expected {
            let inferred = self.mctx.infer_type(e)?;
            if !self.mctx.is_def_eq(inferred, t)? {
                return Err(ElabError::TypeMismatch { expected: t, got: inferred });
            }
        }
        Ok(e)
    }
}
```

`src/lib.rs`:

```rust
//! M4b-1: the leaf term elaborator. `TermElabM` over `leanr_meta`'s
//! MetaM core; elaborates string literals, sorts, global-constant
//! identifiers, ascription, and holes. See
//! docs/superpowers/specs/2026-07-23-m4b1-leaf-term-elaborator-design.md.
pub mod dispatch;
pub mod elab;
pub mod error;
pub mod resolve;   // Task 5
pub mod builtin;   // Tasks 4–6

pub use elab::TermElabM;
pub use error::ElabError;
```

For this task, create `src/resolve.rs` and `src/builtin/mod.rs` as empty stubs (`//! Task 5` / `//! Tasks 4–6`) so `lib.rs` compiles; Tasks 4–6 fill them.

- [ ] **Step 5: Run tests**

Run: `cargo test -p leanr_elab 2>&1 | tail -5`
Expected: PASS.

- [ ] **Step 6: Commit**

```bash
git add crates/leanr_elab Cargo.toml
git commit -m "feat(elab): leanr_elab skeleton — TermElabM, ElabError, dispatch (M4b-1 Task 3)"
```

---

### Task 4: String-literal elaborator + the full oracle harness

Deliver the first end-to-end green query. Build the `Elab0` fixture env, the `dump_elab.lean` dumper, the `oracle_elab.rs` gate, the `elab:fast` mise task, and the string-literal elaborator — then commit only the `str` slice of the corpus, green.

**Files:**
- Create: `crates/leanr_elab/src/builtin/lit.rs`, `crates/leanr_elab/src/builtin/mod.rs` (real), `crates/leanr_elab/tests/oracle_elab.rs`, `crates/leanr_elab/tests/support/mod.rs`
- Create: `tests/fixtures/elab/Elab0.lean` (+ `Elab0.olean`), `tests/fixtures/elab/dump_elab.lean`, `tests/fixtures/elab/elab-queries.jsonl`
- Modify: `crates/leanr_elab/src/dispatch.rs` (register `str`), `mise.toml`

**Interfaces:**
- Consumes: `Store::expr_lit_str(base, &str) -> Result<ExprId, _>`; the meta scheme's `decode_expr`/`encode_expr`/`EncSt`/`replay_fixture_in`/`fixture_in` (Task 2), reused across the crate boundary via `#[path]` include.
- Produces: `builtin::lit::elab_str(elab, node, kinds) -> Result<ExprId, ElabError>`; a committed `elab-queries.jsonl` whose records are `{"id":<str>,"src":<lean source>,"exp":<canonical Expr>}`.

**Background — reusing the scheme across crates.** The canonical decode/encode lives in `crates/leanr_meta/tests/support/mod.rs` (one source of truth — extending it, not copying it, is the anti-drift rule). `leanr_elab`'s gate includes that exact file:

```rust
// crates/leanr_elab/tests/support/mod.rs
#[path = "../../leanr_meta/tests/support/mod.rs"]
mod meta_support;
pub use meta_support::*;
```

`fixture_in`/`replay_fixture_in` use `CARGO_MANIFEST_DIR/../../tests/fixtures/<subdir>`, which resolves to the workspace `tests/fixtures/` from any `crates/<x>` crate — so `leanr_elab`'s gate calls `replay_fixture_in("elab", "Elab0.olean")` and `fixture_in("elab", "elab-queries.jsonl")` with no path surgery.

**Background — the dumper.** `dump_elab.lean` mirrors `dump_defeq.lean`'s IO/`MetaM` plumbing and its `toCanon` (extended with the `lmvar` case from Task 2). It must:
1. `Lean.enableInitializersExecution` **before** `importModules` (the pitfall documented in `dump_syntax_elab.lean`).
2. import `Elab0` with `loadExts := true`.
3. for each `(id, src)` in a hardcoded query list: `Lean.Parser.runParserCategory env \`term src` → `stx`; run `Lean.Elab.Term.elabTerm stx (expectedType? := none)` (then `Term.synthesizeSyntheticMVarsNoPostponing`? — **no**: slice 1 elaborates leaves with no postponement; call the same minimal path leanr models, i.e. `elabTerm` + `instantiateMVars`, and record that exact choice in the module header per the Global Constraint "Universe defaulting divergence" note in the spec), `instantiateMVars`, canonicalize.
4. print one JSON object per line: `{"id":…, "src":…, "exp": <canonical>}`.

Use `Name.toString (escape := false)` and the erase-binder-names / decimal-literal canonicalization rules `dump_defeq.lean` documents. **This dumper is run once under the pinned toolchain via `fixtures:regen-elab`; its output is authoritative.**

**Background — `Elab0.lean`.** Prelude-mode fixture supplying exactly the constants the corpus names. For the `str` slice, `String` (and its universe-free `Type`) must be present. Model it on `tests/fixtures/meta/Meta0.lean` (prelude header, minimal scaffold). Grow it in Tasks 5–6 as their corpora reference more constants.

- [ ] **Step 1: Write `Elab0.lean` and `dump_elab.lean`; register the `fixtures:regen-elab` task**

Create `tests/fixtures/elab/Elab0.lean` (start from `Meta0.lean`; ensure `String` is available). Create `tests/fixtures/elab/dump_elab.lean` per the Background (copy `dump_defeq.lean`'s `Core.Context`/`MetaM.toIO` plumbing and `toCanon`, add the `lmvar` case, replace the query-building loop with the parse+`elabTerm` loop). Add to `mise.toml`:

```toml
[tasks."fixtures:regen-elab"]
description = "Regenerate the M4b-1 leaf-elaboration oracle corpus (dump_elab.lean parses each term source, elaborates via Lean.Elab.Term.elabTerm, and dumps the canonical Expr). Needs the elan toolchain; never runs in CI."
run = [
  "sh -c 'cd tests/fixtures/elab && lean --run dump_elab.lean > elab-queries.jsonl'",
  # Elab0.olean built the same way Meta0.olean is (see fixtures:regen).
]
```

Wire `fixtures:regen-elab` into `fixtures:regen` (as `depends`/`depends_post`, matching how `fixtures:regen-notation` is wired). Build `Elab0.olean` alongside `Meta0.olean` (mirror that `lean` compile step in `fixtures:regen`).

- [ ] **Step 2: Write the failing gate over a `str`-only corpus**

Create `crates/leanr_elab/tests/oracle_elab.rs`:

```rust
mod support;
use support::{decode_expr, encode_expr, fixture_in, replay_fixture_in, EncSt};
use std::collections::HashMap;
use leanr_kernel::bank::Store;
use leanr_kernel::EnvView;
use leanr_meta::{Config, MetaCtx};
use leanr_syntax::{builtin, parse_term};
use leanr_elab::TermElabM;

#[test]
fn oracle_elab_gate() {
    let support::Replayed {
        env, reducibility, matchers, instances, default_instances, projection_fns,
    } = replay_fixture_in("elab", "Elab0.olean");
    let snap = builtin::snapshot();

    let queries = std::fs::read_to_string(fixture_in("elab", "elab-queries.jsonl"))
        .expect("committed elab corpus");
    let mut failures = Vec::new();
    for line in queries.lines().filter(|l| !l.trim().is_empty()) {
        let q: serde_json::Value = serde_json::from_str(line).expect("valid JSONL");
        let id = q["id"].as_str().expect("id");
        let src = q["src"].as_str().expect("src");

        // Fresh EnvView/Store/MetaCtx per query (independence — same
        // contract as oracle_fast).
        let view: EnvView = env.view();

        // Parse the SAME source through leanr's parser (Approach A).
        let parsed = parse_term(src, &snap);
        let term_node = parsed.root(); // the single term child; read ParseResult's real accessor

        let mut scratch = Store::scratch();
        let mut lm: HashMap<u64, NameId> = HashMap::new();
        let mut mv: HashMap<u64, NameId> = HashMap::new();
        let expected = decode_expr(&mut scratch, Some(view.store), &q["exp"], &mut mv, &mut lm);

        let mctx = MetaCtx::new(view, &mut scratch, Config::default(),
            &reducibility, &matchers, &instances, &default_instances, &projection_fns);
        let mut elab = TermElabM::new(mctx);
        let got = elab.elab_term_ensuring_type(&term_node, snap.kinds(), None)
            .and_then(|e| Ok(elab.mctx.instantiate_mvars(e)?));

        match got {
            Ok(g) => {
                let mut st = EncSt::new();
                let got_json = encode_expr(elab.mctx.store(), None, g, &mut st);
                if got_json != q["exp"] {
                    failures.push(format!("{id}: got {got_json} want {}", q["exp"]));
                }
            }
            Err(e) => failures.push(format!("{id}: elaboration failed: {e:?}")),
        }
    }
    assert!(failures.is_empty(), "elab divergences:\n{}", failures.join("\n"));
}
```

(This test references API names — `parsed.root()`, `elab.mctx.store()`, `MetaCtx::new`'s arg order, `decode_expr`'s mvar/lmvar map arity — that must match the real signatures. Read them and adjust per the Signature reconciliation rule; `decode_expr` gains the `lmvar` map from Task 2.)

Populate `elab-queries.jsonl` with `str` records only for now — either by hand-writing them (the canonical form of a string literal is trivial and stable) or by regenerating (`mise run fixtures:regen-elab`) with only `str` queries in `dump_elab.lean`'s list. Example record:

```json
{"id":"str/hello","src":"\"hello\"","exp":{"k":"str","v":"hello"}}
```

- [ ] **Step 3: Run the gate to verify it fails**

Run: `cargo test -p leanr_elab oracle_elab_gate 2>&1 | tail -10`
Expected: FAIL — `str` dispatches to `UnsupportedSyntax` (no elaborator yet).

- [ ] **Step 4: Implement the string-literal elaborator and register it**

`crates/leanr_elab/src/builtin/mod.rs`:

```rust
pub mod lit;
// sort, ident, ascription, hole added in Tasks 5–6.
```

`crates/leanr_elab/src/builtin/lit.rs`:

```rust
use leanr_syntax::{KindInterner, SyntaxNode};
use leanr_kernel::bank::ExprId;
use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `Lean.Elab.Term.elabStrLit` — a string literal elaborates
/// straight to `Expr.lit (.strVal s)`. The one literal that is a leaf;
/// `num`/`char` go through OfNat/Char.ofNat (M4b-3).
pub fn elab_str(
    elab: &mut TermElabM, node: &SyntaxNode, _kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let raw = node.text().to_string();           // includes the surrounding quotes
    let s = decode_string_literal(&raw);         // strip quotes, unescape
    let id = elab.mctx.store_mut().expr_lit_str(None, &s)?;
    Ok(id)
}

/// Decode a Lean string-literal token to its value. Transcribe Lean's
/// `Syntax.decodeStrLit` (escape handling); for the committed corpus
/// (plain ASCII, simple escapes) a direct unescape suffices.
fn decode_string_literal(raw: &str) -> String { /* strip `"`, handle \n \t \\ \" \uXXXX */ }
```

Read the real bank accessor for a mutable `Store` on `MetaCtx` (`store_mut` or field) and the `expr_lit_str` signature; adjust. Register in `dispatch.rs`:

```rust
pub fn elaborator_name_for(kind: &str) -> Option<&'static str> {
    match kind {
        "str" => Some("str"),
        _ => None,
    }
}
// in `dispatch`:
    match name {
        "str" => crate::builtin::lit::elab_str(elab, node, kinds),
        other => Err(ElabError::UnsupportedSyntax(other.to_string())),
    }
```

- [ ] **Step 5: Add the `elab:fast` task and wire it in**

`mise.toml`:

```toml
[tasks."elab:fast"]
description = "M4b-1 tier-1 elaboration gate: every committed leaf-term query elaborates to the oracle's Expr byte-for-byte after canonicalization. Hermetic (committed Elab0.olean + elab-queries.jsonl; no Lean, no network)."
run = "cargo test --release --package leanr_elab --test oracle_elab"
```

Add `elab:fast` to the `ci` task's `depends` list. `mise run test` already runs `cargo test --workspace`, which includes `oracle_elab` — but add `elab:fast` to `ci`'s `depends` so the release-mode gate runs there alongside `meta:fast`'s equivalent (match how the meta gate is wired; if `meta:fast` is a distinct `ci` dependency, mirror it, otherwise rely on `test`).

- [ ] **Step 6: Run both gates**

Run: `cargo test -p leanr_elab 2>&1 | tail -5 && mise run elab:fast 2>&1 | tail -3 && mise run meta:fast 2>&1 | tail -3`
Expected: PASS on all.

- [ ] **Step 7: Commit**

```bash
git add crates/leanr_elab tests/fixtures/elab mise.toml
git commit -m "feat(elab): string-literal leaf + differential oracle harness, elab:fast gate (M4b-1 Task 4)"
```

---

### Task 5: Global-name resolution + identifier elaborator (exercises `lmvar`)

An identifier resolving to a global constant elaborates to `Expr.const name levels`, with a **fresh level metavariable per universe parameter** — so `List` (one universe param) produces the `lmvar` the harness now handles.

**Files:**
- Create: `crates/leanr_elab/src/resolve.rs` (real), `crates/leanr_elab/src/builtin/ident.rs`
- Modify: `crates/leanr_elab/src/builtin/mod.rs`, `src/dispatch.rs`, `tests/fixtures/elab/{Elab0.lean,dump_elab.lean,elab-queries.jsonl}`, `Elab0.olean`

**Interfaces:**
- Consumes: `EnvView::get(NameId) -> Option<&ConstantInfo>`; `ConstantInfo`'s `level_params` (a `&[NameId]` on its `ConstantVal` — read the real field name/path in `leanr_kernel`); `Store::level_mvar`, `Store::intern_level_list`, `Store::expr_const`; `MetavarContext::declare_level`; `LMVarId`.
- Produces:
  - `resolve::resolve_global(view: &EnvView, name: NameId) -> Result<NameId, ElabError>` — returns the unique resolved constant name; `UnknownIdent` if none, `AmbiguousIdent` if more than one candidate (Global Constraint: no overload sets in slice 1).
  - `builtin::ident::elab_ident(elab, node, kinds) -> Result<ExprId, ElabError>`.
  - `TermElabM::mk_fresh_level_mvar(&mut self) -> Result<LevelId, ElabError>` (helper on `elab.rs`).

**Background — resolution scope (Global Constraint: named seam).** Slice 1 resolves the name **as written** plus current-namespace prefixes against declared globals, erroring on ambiguity. No `open`/alias/`export`/`_root_`/dot-notation — those are later slices; the corpus uses qualified names to stay inside this subset. Transcribe the *reduced* form of `Lean.Elab.resolveName`; leave a doc comment citing the full oracle `resolveName` and the deferral.

**Background — fresh universe levels.** Lean's `elabIdent`/`mkConst` mints one fresh universe metavariable per the constant's `levelParams`. `mk_fresh_level_mvar` allocates a fresh `LMVarId` (mint a unique `NameId`, e.g. via the store's name interner with an incrementing counter held in `TermElabM`), `declare_level`s it in the `mctx`, and interns `store.level_mvar(base, Some(name))`. Collect these into a `LevelsId` via `intern_level_list`, then `expr_const(base, Some(cname), levels)`.

- [ ] **Step 1: Write the failing gate rows + a resolve unit test**

Add to `tests/fixtures/elab/elab-queries.jsonl` (regenerate via `fixtures:regen-elab` after adding these to `dump_elab.lean`'s query list, or hand-write from a known-good oracle run):

```json
{"id":"ident/Nat","src":"Nat","exp":{"k":"const","n":"Nat","us":[]}}
{"id":"ident/List","src":"List","exp":{"k":"const","n":"List","us":[{"k":"lmvar","i":0}]}}
```

(`Nat` : no universe params → empty `us`. `List` : one universe param → one fresh level mvar → `lmvar` index 0. Ensure `Elab0.lean` declares both.)

Add a `resolve` unit test in `src/resolve.rs`:

```rust
#[cfg(test)]
mod tests {
    // Build a tiny env with one `Foo` const; resolve_global("Foo") -> Foo,
    // resolve_global("Nope") -> UnknownIdent. Use leanr_kernel::testenv
    // helpers (see crates/leanr_kernel/src/testenv.rs) to build the env.
}
```

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_elab 2>&1 | tail -10`
Expected: FAIL — `ident` unsupported; `resolve_global` undefined.

- [ ] **Step 3: Implement `resolve.rs`, `mk_fresh_level_mvar`, and `ident.rs`**

`src/resolve.rs`:

```rust
use leanr_kernel::bank::NameId;
use leanr_kernel::EnvView;
use crate::error::ElabError;

/// Reduced `Lean.Elab.resolveName`: global constants only, name-as-written
/// plus current-namespace prefixes, ambiguity is an error. No open/alias/
/// export/_root_/dot-notation — M4b-3/M4b-4 own those; corpus stays
/// qualified. (oracle: Lean/Elab/BuiltinNotation + Lean/ResolveName.lean.)
pub fn resolve_global(view: &EnvView, name: NameId) -> Result<NameId, ElabError> {
    if view.env().get(name).is_some() {   // read the real EnvView->Environment accessor
        return Ok(name);
    }
    Err(ElabError::UnknownIdent(/* name_to_string(name) */ String::new()))
}
```

(For slice 1 the corpus uses fully-qualified names, so the candidate set is `{name}` when declared, `{}` otherwise — ambiguity cannot arise yet, but keep the `AmbiguousIdent` branch wired for when namespace prefixes produce multiple hits, with a test added in the slice that introduces `open`.)

`mk_fresh_level_mvar` on `elab.rs` and the ident elaborator per the Background. Register `ident` in `dispatch.rs` (`"ident" => Some("ident")` / `"ident" => crate::builtin::ident::elab_ident(...)`).

- [ ] **Step 4: Run both gates**

Run: `cargo test -p leanr_elab 2>&1 | tail -5 && mise run elab:fast 2>&1 | tail -3 && mise run meta:fast 2>&1 | tail -3`
Expected: PASS — including the `List` row that exercises `lmvar` end-to-end.

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_elab tests/fixtures/elab
git commit -m "feat(elab): global-const identifier leaf + name resolution (M4b-1 Task 5)"
```

---

### Task 6: Sort, ascription, and hole elaborators

The remaining leaves: `Prop`/`Type`/`Sort e`, ascription `(e : T)`, and the hole `_`.

**Files:**
- Create: `crates/leanr_elab/src/builtin/{sort.rs,ascription.rs,hole.rs}`
- Modify: `crates/leanr_elab/src/builtin/mod.rs`, `src/dispatch.rs`, `src/elab.rs` (add `mk_fresh_expr_mvar`), `tests/fixtures/elab/{Elab0.lean,dump_elab.lean,elab-queries.jsonl}`

**Interfaces:**
- Consumes: `Store::{level_zero, level_succ, expr_sort, expr_mvar}`; `MetavarContext::declare` with `MVarDecl { user_name: None, ty, lctx, kind: MVarKind::Natural }` (read `LocalContext`'s empty constructor in `leanr_kernel::local_ctx`); the sort node's level child.
- Produces: `builtin::sort::elab_sort` / `elab_type` / `elab_prop`; `builtin::ascription::elab_ascription`; `builtin::hole::elab_hole`; `TermElabM::mk_fresh_expr_mvar(&mut self, ty: ExprId) -> Result<ExprId, ElabError>`.

**Background — sorts (verify against the fixture).** Transcribe `Lean.Elab.BuiltinTerm`'s `elabProp`/`elabType`/`elabSort` and `Lean.Elab.Level`. The author's transcription: `Prop` → `Sort 0` (`level_zero`); bare `Type` → `Sort 1` (`level_succ level_zero`); `Type n`/`Type u` → `Sort (n+1)`; `Sort e` → `Sort e` where `e` is the elaborated level. **The committed fixture is authoritative** (Global Constraint): if the oracle emits a different universe for bare `Type`, match the fixture.

**Background — ascription.** `(e : T)` is `Lean.Parser.Term.paren` wrapping a `typeAscription`, or a bare `paren` for `(e)`. Transcribe `elabParen`: for the ascription form, elaborate the type child `T` (as a term, i.e. its expected type is a sort — for slice 1 just `elab_term(T, None)`), then `elab_term_ensuring_type(e, Some(T'))`. For the plain `(e)` form, `elab_term(e, expected)`. Cite `elabParen`.

**Background — hole.** `_` → a fresh natural expr metavariable at the expected type, or a fresh type-mvar if `expected` is `None`. `mk_fresh_expr_mvar(ty)` mints a fresh `MVarId` (unique `NameId`), `declare`s it with an empty `LocalContext` and `MVarKind::Natural`, and interns `store.expr_mvar(base, Some(name))`.

- [ ] **Step 1: Write the failing gate rows**

Add to `elab-queries.jsonl` (regen or hand-write from a known oracle run). Illustrative:

```json
{"id":"sort/Prop","src":"Prop","exp":{"k":"sort","u":{"k":"zero"}}}
{"id":"sort/Type","src":"Type","exp":{"k":"sort","u":{"k":"succ","u":{"k":"zero"}}}}
{"id":"asc/nat-in-type","src":"(Nat : Type)","exp":{"k":"const","n":"Nat","us":[]}}
{"id":"hole/bare","src":"_","exp":{"k":"mvar","i":0}}
```

(Adjust `sort/Type` to the fixture if bare `Type` differs. `asc/nat-in-type` checks `(Nat : Type)` elaborates `Nat` and its type is def-eq to `Type` — no coercion needed. `hole/bare` yields a bare mvar.)

- [ ] **Step 2: Run to verify failure**

Run: `cargo test -p leanr_elab oracle_elab_gate 2>&1 | tail -10`
Expected: FAIL — `Lean.Parser.Term.prop`/`.type`/`.paren`/`.hole` unsupported.

- [ ] **Step 3: Implement the three elaborators + `mk_fresh_expr_mvar`**

Write `sort.rs`, `ascription.rs`, `hole.rs` per the Background, add `mk_fresh_expr_mvar` to `elab.rs`, extend `builtin/mod.rs`, and register the kinds in `dispatch.rs`:

```rust
    match name {
        "str" => crate::builtin::lit::elab_str(elab, node, kinds),
        "ident" => crate::builtin::ident::elab_ident(elab, node, kinds),
        "Lean.Parser.Term.prop" => crate::builtin::sort::elab_prop(elab, node, kinds),
        "Lean.Parser.Term.type" => crate::builtin::sort::elab_type(elab, node, kinds),
        "Lean.Parser.Term.sort" => crate::builtin::sort::elab_sort(elab, node, kinds),
        "Lean.Parser.Term.paren" => crate::builtin::ascription::elab_paren(elab, node, kinds, expected),
        "Lean.Parser.Term.typeAscription" => crate::builtin::ascription::elab_ascription(elab, node, kinds, expected),
        "Lean.Parser.Term.hole" => crate::builtin::hole::elab_hole(elab, node, kinds, expected),
        other => Err(ElabError::UnsupportedSyntax(other.to_string())),
    }
```

(Confirm the exact paren/ascription/hole node kind names against a real parse of `(e : T)` / `(e)` / `_`: `cargo test -p leanr_syntax`-style dump, or `grep` in `crates/leanr_syntax/src/builtin/term.rs` — the plan cites `Lean.Parser.Term.paren`, `Lean.Parser.Term.typeAscription`, `Lean.Parser.Term.hole`, but the fixture/parse is authoritative.) Update `elaborator_name_for` to list all registered kinds.

- [ ] **Step 4: Run both gates**

Run: `cargo test -p leanr_elab 2>&1 | tail -5 && mise run elab:fast 2>&1 | tail -3 && mise run meta:fast 2>&1 | tail -3`
Expected: PASS.

- [ ] **Step 5: Commit**

```bash
git add crates/leanr_elab tests/fixtures/elab
git commit -m "feat(elab): sort, ascription, and hole leaf elaborators (M4b-1 Task 6)"
```

---

### Task 7: Named-seam audit, crate doc, and full verification

Confirm the slice is complete, honest, and green end-to-end.

**Files:**
- Modify: `crates/leanr_elab/src/lib.rs` (crate-doc "what this does NOT build" list), `crates/leanr_elab/src/dispatch.rs` (a `// deferred:` comment block)

- [ ] **Step 1: Named-seam audit**

Verify every deferred form is a named `ElabError::UnsupportedSyntax` (nothing silently skipped) and add a doc-commented deferral list to `dispatch.rs` naming each and its slice:

```rust
// Deferred (each hits UnsupportedSyntax until its slice lands):
//   binders (fun/forall/let/have/show) ......... M4b-2
//   application, @, named/optional args ........ M4b-3
//   num / char literals (OfNat / Char.ofNat) ... M4b-3
//   coercions (mkCoe) .......................... M4b-3
//   elabAsElim, dot-notation, binop%, ⟨⟩ ....... M4b-4
//   macro expansion in dispatch ................ first macro-form slice
//   open / alias / export / _root_ resolution .. later slice
```

Add the corresponding "What this slice does NOT build" paragraph to the `lib.rs` crate doc, citing the spec.

- [ ] **Step 2: Full verification**

```bash
git status --short crates/leanr_kernel crates/leanr_olean   # MUST be empty (TCB untouched)
git status --short crates/leanr_meta/src                     # MUST be empty (meta src untouched)
cargo test --workspace 2>&1 | tail -5
mise run meta:fast 2>&1 | tail -3
mise run elab:fast 2>&1 | tail -3
mise run lint 2>&1 | tail -3
```

Expected: the two `git status` checks print nothing; all tests and gates green; lint clean.

- [ ] **Step 3: Commit**

```bash
git add crates/leanr_elab
git commit -m "docs(elab): named-seam deferral list + crate doc; M4b-1 verified green (M4b-1 Task 7)"
```

---

## Self-Review

**Spec coverage:**
- Crate & module layout → Task 3 (skeleton) + Tasks 4–6 (modules). ✓
- `TermElabM` state (wraps `MetaCtx`, `level_names`, expected-type as parameter, no premature scheduling fields) → Task 3. ✓
- Dispatch, no macro expansion, `UnsupportedSyntax` for unregistered kinds → Task 3 + Task 7 audit. ✓
- Leaf elaborators: string literal → Task 4; identifiers (global const, fresh universe mvars) → Task 5; sorts/ascription/hole → Task 6. ✓
- `elab_term_ensuring_type` → `is_def_eq`, error (not coerce) on mismatch → Task 3 (`TypeMismatch`), exercised by `asc/nat-in-type` in Task 6. ✓
- Name resolution: global-const-only, error on ambiguity, deferrals named → Task 5 + Task 7. ✓
- Universe mvars / `lmvar` scheme extension → Task 2, exercised by `List` in Task 5. ✓
- Oracle harness: source-text Approach A, `Elab0` fixture, `dump_elab.lean`, `parse_term`, `oracle_elab.rs`, `elab:fast` regression gate wired into `test`/`ci`, no nightly → Tasks 1, 4. ✓
- Shared scheme (single source of truth) across crates → Task 2 (`_in` helpers) + Task 4 (`#[path]` include). ✓
- `num`/`char` correctly excluded as non-leaves → Scope correction in spec + deferral in Task 7. ✓
- Testing tiers (unit per elaborator; the differential gate; never-panic via `ElabError`) → Tasks 3–6 unit tests + Task 4 gate; `parse_term` losslessness → Task 1. ✓
- Stated exception (no user-facing subcommand) → not a build task; recorded in spec. ✓

**Placeholder scan:** two intentionally-elided function bodies (`decode_string_literal`'s unescape, `replay_fixture_in`'s body "= body of `replay_fixture`") are directed to a named oracle/existing implementation, not "TODO"; every other step shows real code. The `elaborator_name_for` table and `dispatch` `match` are grown explicitly per task (shown at each). No "add error handling"/"handle edge cases"/"similar to Task N" placeholders.

**Type consistency:** `TermElabM` fields (`mctx`, `level_names`), entry signatures (`elab_term(node, kinds, expected)`, `elab_term_ensuring_type(...)`), helper names (`mk_fresh_level_mvar`, `mk_fresh_expr_mvar`), `ElabError` variants (`UnsupportedSyntax`/`UnknownIdent`/`AmbiguousIdent`/`TypeMismatch`/`Meta`), `resolve_global`, `elaborator_name_for`, and the corpus record shape (`{id,src,exp}`) are used identically across Tasks 3–6. `encode_level`/`decode_level`'s new `EncSt`/`HashMap<u64,NameId>` arity is defined in Task 2 and consumed in Task 4's gate. Remaining unknowns (`ParseResult` accessor, `MetaCtx::store`/`store_mut`, `EnvView::env`, `ConstantInfo.level_params` path, exact paren/hole kind names) are explicitly flagged for the Signature reconciliation rule at each use.
