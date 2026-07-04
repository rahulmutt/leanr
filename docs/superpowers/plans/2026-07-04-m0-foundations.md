# leanr M0 — Foundations Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Stand up the leanr repo end-to-end: pinned dev environment, CI with security gates, front-door docs, the salsa query engine demonstrably walking (memoization + invalidation + early cutoff), the oracle Lean toolchain pinned, and a `.olean` header reader wired into a `leanr olean info` CLI command.

**Architecture:** Cargo workspace with three crates: `leanr_query` (salsa-style incremental engine), `leanr_olean` (official `.olean` artifact interop), `leanr_cli` (thin frontend, no logic of its own). Correctness against the official Lean toolchain (the "oracle") via golden fixtures committed to the repo. See `docs/superpowers/specs/2026-07-04-leanr-architecture-design.md` for the full design.

**Tech Stack:** Rust (mise-pinned), salsa, clap, thiserror, proptest, assert_cmd/predicates (dev), gitleaks + cargo-deny (security gates), GitHub Actions via `jdx/mise-action`, elan for the oracle Lean toolchain.

## Global Constraints

- License: Apache-2.0 (matches the repo `LICENSE`); all crates declare `license = "Apache-2.0"`.
- Every tool is mise-pinned with `mise use --pin` — never bare `mise use`; an unpinned entry is a reproducibility bug. Verify each install by running `<tool> --version`.
- Every new cargo dependency is a liability: only the deps named in this plan may be added (`clap`, `salsa`, `thiserror`, and dev-deps `proptest`, `assert_cmd`, `predicates`). Anything else needs a plan change.
- `Cargo.lock` is committed.
- Lint gate is `cargo fmt --all --check` + `cargo clippy --workspace --all-targets -- -D warnings`; both must pass before every commit.
- The oracle toolchain is whatever `lean-toolchain` (fetched from Mathlib master in Task 5) pins; it changes only at milestone boundaries.
- Workspace crates live under `crates/`; one purpose per crate; `leanr_cli` contains no logic beyond argument parsing and printing.
- Run tasks via mise (`mise run test`, `mise run lint`, …) — CI runs the same named tasks contributors run.
- Commit messages use conventional-commit prefixes (`feat:`, `docs:`, `ci:`, `chore:`, `test:`).

---

### Task 1: Pinned toolchain + workspace skeleton + `leanr` binary

**Files:**
- Create: `mise.toml`
- Create: `Cargo.toml` (workspace root)
- Create: `crates/leanr_cli/Cargo.toml`
- Create: `crates/leanr_cli/src/main.rs`
- Test: `crates/leanr_cli/tests/cli.rs`
- Modify: `.gitignore` (append `target/`)

**Interfaces:**
- Consumes: nothing (first task).
- Produces: mise tasks `build`, `test`, `fmt`, `lint` used by every later task; a `leanr` binary with a clap `Cli` struct in `crates/leanr_cli/src/main.rs` that Task 7 extends with subcommands; workspace `Cargo.toml` whose `members` list Tasks 4 and 6 append to.

- [ ] **Step 1: Pin Rust with mise**

```bash
mise use --pin rust
mise install
rustc --version
cargo --version
```

Expected: `mise.toml` is created containing `[tools]` with an exact version, e.g. `rust = "1.88.0"` (whatever latest stable resolves to — exact, not fuzzy). `rustc --version` prints that same version. If it doesn't match, the install is not done.

- [ ] **Step 2: Add named tasks to mise.toml**

Append to `mise.toml`:

```toml
[tasks.build]
run = "cargo build --workspace"

[tasks.test]
run = "cargo test --workspace"

[tasks.fmt]
run = "cargo fmt --all"

[tasks.lint]
run = [
  "cargo fmt --all --check",
  "cargo clippy --workspace --all-targets -- -D warnings",
]
```

- [ ] **Step 3: Create the workspace and cli crate**

Create `Cargo.toml` at the repo root:

```toml
[workspace]
resolver = "2"
members = ["crates/leanr_cli"]

[workspace.package]
version = "0.1.0"
edition = "2021"
license = "Apache-2.0"
repository = "https://github.com/rahulmutt/leanr"
```

Create `crates/leanr_cli/Cargo.toml`:

```toml
[package]
name = "leanr_cli"
version.workspace = true
edition.workspace = true
license.workspace = true

[[bin]]
name = "leanr"
path = "src/main.rs"

[dependencies]
clap = { version = "4", features = ["derive"] }

[dev-dependencies]
assert_cmd = "2"
predicates = "3"
```

Create `crates/leanr_cli/src/main.rs`:

```rust
use clap::Parser;

/// A pure-Rust Lean 4 toolchain.
#[derive(Parser)]
#[command(name = "leanr", version)]
struct Cli {}

fn main() {
    let _cli = Cli::parse();
}
```

Append to `.gitignore`:

```
target/
```

- [ ] **Step 4: Write the failing CLI test**

Create `crates/leanr_cli/tests/cli.rs`:

```rust
use assert_cmd::Command;

#[test]
fn version_prints_name_and_semver() {
    Command::cargo_bin("leanr")
        .unwrap()
        .arg("--version")
        .assert()
        .success()
        .stdout(predicates::str::starts_with("leanr 0.1.0"));
}
```

- [ ] **Step 5: Run the test suite and lint**

```bash
mise run test
mise run lint
```

Expected: `version_prints_name_and_semver` PASSES (clap provides `--version` from the derive; if the test fails on the string, fix `main.rs`, not the test). Lint passes with zero warnings.

- [ ] **Step 6: Commit**

```bash
git add mise.toml Cargo.toml Cargo.lock .gitignore crates/
git commit -m "feat: cargo workspace skeleton with mise-pinned Rust and leanr binary"
```

---

### Task 2: CI + security gates (secret scanning, dependency policy)

**Files:**
- Create: `deny.toml`
- Create: `.github/workflows/ci.yml`
- Modify: `mise.toml` (new tools + tasks)

**Interfaces:**
- Consumes: mise tasks from Task 1.
- Produces: mise tasks `lint:deps`, `scan:secrets`, and the umbrella `ci` task that every later task's "Expected: `mise run ci` passes" step relies on; a GitHub Actions workflow that runs `mise run ci` on every push/PR.

- [ ] **Step 1: Pin the security tools**

Follow the mise decision flow — registry first, backend fallback:

```bash
mise registry | grep -w gitleaks
mise use --pin gitleaks
mise registry | grep -w cargo-deny
mise use --pin cargo-deny
mise install
gitleaks version
cargo deny --version
```

Expected: both tools appear in `mise.toml` `[tools]` with exact versions and both `--version` commands print those versions. If either is missing from the registry, pin via a backend instead (e.g. `mise use --pin "ubi:gitleaks/gitleaks@<version>"`, `mise use --pin "ubi:EmbarkStudios/cargo-deny@<version>"`) — still exact-pinned.

- [ ] **Step 2: Write the dependency policy**

Create `deny.toml`:

```toml
[advisories]
version = 2
yanked = "deny"

[licenses]
version = 2
allow = [
  "Apache-2.0",
  "MIT",
  "BSD-3-Clause",
  "ISC",
  "Unicode-3.0",
  "Zlib",
]

[bans]
multiple-versions = "warn"

[sources]
unknown-registry = "deny"
unknown-git = "deny"
```

- [ ] **Step 3: Add the scan tasks and the ci umbrella task**

Append to `mise.toml`:

```toml
[tasks."lint:deps"]
run = "cargo deny check"

[tasks."scan:secrets"]
run = "gitleaks detect --redact"

[tasks.ci]
depends = ["lint", "test", "lint:deps", "scan:secrets"]
```

- [ ] **Step 4: Run the gates locally**

```bash
mise run ci
```

Expected: all four dependent tasks pass. If `cargo deny check` fails on a license used by a transitive dep of clap/assert_cmd, add that specific license to the `allow` list (it will be a permissive one such as `Unicode-DFS-2016`) — never weaken `[sources]` or `[advisories]`.

- [ ] **Step 5: Create the CI workflow**

Create `.github/workflows/ci.yml`:

```yaml
name: CI
on:
  push:
    branches: [main]
  pull_request:

jobs:
  ci:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
        with:
          fetch-depth: 0 # gitleaks scans full history
      - uses: jdx/mise-action@v2
      - run: mise run ci
```

- [ ] **Step 6: Commit and verify CI**

```bash
git add mise.toml deny.toml .github/
git commit -m "ci: run lint, tests, secret scan, and dependency policy via mise tasks"
git push origin main
gh run watch --exit-status
```

Expected: the GitHub Actions run goes green. If it fails, fix forward (the failure output names the task) — do not disable a gate to get green.

---

### Task 3: Front door — README, AGENTS.md, codebase map, threat model

**Files:**
- Modify: `README.md`
- Create: `AGENTS.md`
- Create: `CLAUDE.md`
- Create: `ARCHITECTURE.md`
- Create: `docs/THREAT_MODEL.md`

**Interfaces:**
- Consumes: task names from Tasks 1–2 (referenced by name, never re-spelled as raw commands — single source of truth).
- Produces: the docs later tasks and milestone plans extend; `ARCHITECTURE.md` sections that the M1 plan will update.

- [ ] **Step 1: Write README.md** (replace the current two-liner)

```markdown
# leanr

A pure-Rust implementation of the Lean 4 toolchain, built for
declaration-level incremental compilation and aggressive, correct caching.
End goal: a drop-in replacement for `lean`/`lake` that builds Mathlib —
with sub-second edit feedback.

**Status:** M0 (foundations). Nothing usable yet. Roadmap and design:
[`docs/superpowers/specs/2026-07-04-leanr-architecture-design.md`](docs/superpowers/specs/2026-07-04-leanr-architecture-design.md).

## Quickstart

Requires [mise](https://mise.jdx.dev). Then:

    git clone https://github.com/rahulmutt/leanr && cd leanr
    mise install
    mise run test

All workflows are named mise tasks — run `mise tasks` to list them
(`build`, `test`, `lint`, `ci`, …).

## Layout

See [ARCHITECTURE.md](ARCHITECTURE.md) for the crate map and why the
boundaries fall where they do.

## License

Apache-2.0.
```

- [ ] **Step 2: Write AGENTS.md** (canonical agent-instruction file; only the non-obvious and non-derivable)

```markdown
# Agent instructions for leanr

leanr is a pure-Rust Lean 4 toolchain. Read `ARCHITECTURE.md` before
touching crate boundaries, and the design spec in
`docs/superpowers/specs/` before architectural changes.

## Rules that are not derivable from the code

- **Oracle discipline:** correctness is defined by differential testing
  against the pinned official Lean toolchain (`lean-toolchain` file =
  the version Mathlib pins). Never bump the pin outside a milestone
  boundary. Regenerate fixtures with `mise run fixtures:regen`.
- **Kernel TCB (future):** `leanr_kernel` must depend on no other
  workspace crate. Soundness bugs live there; keep it minimal.
- **Untrusted input:** `.olean` bytes and (later) remote-cache entries
  are untrusted. Parsers must never panic on arbitrary bytes — see
  `docs/THREAT_MODEL.md`.
- **Environment:** tools are mise-pinned (`mise use --pin`, never bare
  `mise use`). App deps via cargo only; every new dependency needs
  justification.
- **Workflows:** use the named mise tasks (`mise tasks` lists them); CI
  runs `mise run ci` — the same tasks you run locally.
```

Create `CLAUDE.md` containing exactly:

```markdown
See [AGENTS.md](AGENTS.md).
```

- [ ] **Step 3: Write ARCHITECTURE.md** (map the non-obvious, not the file tree)

```markdown
# Architecture

One incremental query engine is the spine; everything else is a query
implementation or a thin frontend. Full design:
`docs/superpowers/specs/2026-07-04-leanr-architecture-design.md`.

## Crates (current)

- `crates/leanr_query` — the salsa-based incremental engine. Everything
  computable is a memoized query; **early cutoff** (a recomputed query
  whose value is unchanged does not wake its dependents) is the
  mechanism the whole incrementality story rests on.
- `crates/leanr_olean` — reader for official Lean `.olean` artifacts.
  Trust boundary: input bytes are untrusted (`docs/THREAT_MODEL.md`).
- `crates/leanr_cli` — the `leanr` binary. Thin: argument parsing and
  printing only, so CLI and (future) LSP can never diverge in behavior.

## Why the boundaries fall here

- The (future) `leanr_kernel` is the trusted computing base — it will
  depend on nothing in the workspace and nothing reaches into it.
- CLI and LSP are frontends over the same query engine by design;
  logic in `leanr_cli` is a bug.

## Oracle

`lean-toolchain` pins the official Lean version Mathlib uses — our
differential-testing oracle. Golden fixtures live in `tests/fixtures/`
(regenerate: `mise run fixtures:regen`).
```

(The `leanr_query`/`leanr_olean` crates and the Oracle section describe Tasks 4–6; if executing strictly in order, mark them "(landing this milestone)" and remove the marker as those tasks land.)

- [ ] **Step 4: Write docs/THREAT_MODEL.md**

```markdown
# leanr threat model (M0)

## Assets

1. **Soundness** — leanr must never accept a proof the Lean kernel
   would reject. A soundness bug is the worst possible defect.
2. **User machines** — leanr parses and (later) executes bytes it did
   not produce.

## Trust boundaries and controls

| Boundary | Who controls the bytes | Control |
|---|---|---|
| `.olean` files | Any package author / cache | Parse defensively: no panics on arbitrary bytes (fuzz/property-tested); kernel-check imported content by default (M1+) |
| Remote cache entries (M2+) | Cache operator / network | Content-addressed hashes; kernel-check unless signed by a trusted key |
| `lakefile.lean` execution (M4+) | Package author | Arbitrary code execution **by design** (same as lake); documented, not hidden |
| Cargo dependencies | Upstream maintainers | `cargo deny` in CI (advisories, sources, licenses); minimal dependency policy |
| Committed secrets | Contributors | gitleaks in CI over full history |

## Out of scope (for now)

- Sandboxing `lakefile.lean`/tactic execution (revisit at M4).
- Signature infrastructure for caches (revisit at M2).

Revisit this document at every milestone boundary.
```

- [ ] **Step 5: Verify onboarding by running it**

Run the README quickstart verbatim in a fresh directory:

```bash
cd "$(mktemp -d)" && git clone /workspace leanr-onboard && cd leanr-onboard && mise install && mise run test
```

Expected: clean clone-to-green. If any step fails, fix the docs or the setup — first-run must actually work.

- [ ] **Step 6: Commit**

```bash
git add README.md AGENTS.md CLAUDE.md ARCHITECTURE.md docs/THREAT_MODEL.md
git commit -m "docs: front door - README quickstart, agent instructions, codebase map, threat model"
```

---

### Task 4: `leanr_query` — the engine walks (memoization, invalidation, early cutoff)

**Files:**
- Create: `crates/leanr_query/Cargo.toml`
- Create: `crates/leanr_query/src/lib.rs`
- Test: `crates/leanr_query/tests/engine_walks.rs`
- Modify: `Cargo.toml` (add workspace member)

**Interfaces:**
- Consumes: workspace from Task 1.
- Produces: the `salsa` dependency choice and the event-observation test idiom (`TestDb` with `salsa_event` capture) that all future incrementality tests copy; exports `SourceText` (salsa input with `text: String`), `trimmed_text(db, SourceText) -> String`, `line_count(db, SourceText) -> usize`.

**Why this toy:** `line_count` depends on `trimmed_text` depends on the input. A whitespace-only edit forces `trimmed_text` to re-run but produces an equal value, so salsa's early cutoff must shield `line_count` from re-running. This is the exact mechanism the spec's "firewall queries" rely on — proven working before anything is built on it.

- [ ] **Step 1: Create the crate**

Add `"crates/leanr_query"` to `members` in the root `Cargo.toml`.

Create `crates/leanr_query/Cargo.toml`:

```toml
[package]
name = "leanr_query"
version.workspace = true
edition.workspace = true
license.workspace = true

[dependencies]
salsa = "0.23"
```

Then run `cargo add salsa --package leanr_query` to resolve the current version (adjust the number above to whatever resolves; commit the lockfile either way).

Create `crates/leanr_query/src/lib.rs`:

```rust
//! The incremental query engine. Everything leanr computes is a memoized
//! salsa query; early cutoff is the mechanism firewall queries rely on.

#[salsa::input]
pub struct SourceText {
    #[return_ref]
    pub text: String,
}

#[salsa::tracked]
pub fn trimmed_text(db: &dyn salsa::Database, source: SourceText) -> String {
    source.text(db).trim_end().to_string()
}

#[salsa::tracked]
pub fn line_count(db: &dyn salsa::Database, source: SourceText) -> usize {
    trimmed_text(db, source).lines().count()
}
```

- [ ] **Step 2: Write the failing tests**

Create `crates/leanr_query/tests/engine_walks.rs`:

```rust
use std::sync::{Arc, Mutex};

use leanr_query::{line_count, trimmed_text, SourceText};
use salsa::Setter;

/// A database that records which queries actually executed, so tests can
/// assert on recomputation behavior — over-invalidation is a perf bug,
/// under-invalidation is a correctness bug, and both are tested this way.
#[salsa::db]
#[derive(Default)]
struct TestDb {
    storage: salsa::Storage<Self>,
    executed: Arc<Mutex<Vec<String>>>,
}

#[salsa::db]
impl salsa::Database for TestDb {
    fn salsa_event(&self, event: &dyn Fn() -> salsa::Event) {
        let event = event();
        if let salsa::EventKind::WillExecute { database_key } = event.kind {
            self.executed
                .lock()
                .unwrap()
                .push(format!("{database_key:?}"));
        }
    }
}

impl TestDb {
    fn executions_of(&self, query: &str) -> usize {
        self.executed
            .lock()
            .unwrap()
            .iter()
            .filter(|k| k.contains(query))
            .count()
    }
}

#[test]
fn repeated_queries_are_memoized() {
    let db = TestDb::default();
    let src = SourceText::new(&db, "a\nb\nc".to_string());

    assert_eq!(line_count(&db, src), 3);
    assert_eq!(line_count(&db, src), 3);

    assert_eq!(db.executions_of("line_count"), 1);
    assert_eq!(db.executions_of("trimmed_text"), 1);
}

#[test]
fn editing_the_input_invalidates() {
    let mut db = TestDb::default();
    let src = SourceText::new(&db, "a\nb".to_string());

    assert_eq!(line_count(&db, src), 2);
    src.set_text(&mut db).to("a\nb\nc".to_string());
    assert_eq!(line_count(&db, src), 3);

    assert_eq!(db.executions_of("line_count"), 2);
}

#[test]
fn early_cutoff_shields_downstream_queries() {
    let mut db = TestDb::default();
    let src = SourceText::new(&db, "a\nb".to_string());

    assert_eq!(line_count(&db, src), 2);

    // Whitespace-only edit: trimmed_text must re-run, but its value is
    // unchanged, so line_count must NOT re-run. This is the firewall.
    src.set_text(&mut db).to("a\nb   \n\n".to_string());
    assert_eq!(line_count(&db, src), 2);

    assert_eq!(db.executions_of("trimmed_text"), 2);
    assert_eq!(db.executions_of("line_count"), 1);
}

#[test]
fn trimmed_text_behavior() {
    let db = TestDb::default();
    let src = SourceText::new(&db, "x  \n".to_string());
    assert_eq!(trimmed_text(&db, src), "x");
}
```

- [ ] **Step 3: Run the tests**

```bash
mise run test
```

Expected: all four tests PASS. Note on salsa API churn: salsa's macro/trait surface moves between versions. If the resolved salsa version rejects these exact signatures (e.g. `Setter` import path, `salsa_event` signature, `EventKind` shape), consult the `tests/` directory of the resolved salsa version on docs.rs/GitHub for the current idiom and adapt the *mechanics only* — the four assertions (memoized; invalidated; early-cutoff shields `line_count` while `trimmed_text` re-runs; trim behavior) are the deliverable and must not be weakened. If early cutoff is not achievable with the resolved version, STOP and flag it — that undermines the spec's firewall design and needs a human decision.

- [ ] **Step 4: Lint and commit**

```bash
mise run lint
git add Cargo.toml Cargo.lock crates/leanr_query/
git commit -m "feat: leanr_query walks - memoization, invalidation, and early cutoff proven by test"
```

---

### Task 5: Oracle toolchain pin + golden fixtures

**Files:**
- Create: `lean-toolchain`
- Create: `docs/ORACLE.md`
- Create: `tests/fixtures/Sample.lean`
- Create: `tests/fixtures/Sample.olean` (generated, committed)
- Create: `tests/fixtures/oracle-githash.txt` (generated, committed)
- Modify: `mise.toml` (elan tool + `fixtures:regen` task)

**Interfaces:**
- Consumes: mise setup from Task 1.
- Produces: `tests/fixtures/Sample.olean` and `tests/fixtures/oracle-githash.txt`, consumed by Task 6's golden test and Task 7's CLI test; the `fixtures:regen` task; the `lean-toolchain` pin file.

- [ ] **Step 1: Pin elan via mise**

```bash
mise registry | grep -w elan
mise use --pin elan
mise install
elan --version
```

Expected: exact-pinned `elan` entry in `mise.toml` and a version printed. If elan is not in the registry, use `mise use --pin "ubi:leanprover/elan@<latest release tag>"` (find the tag with `gh release list -R leanprover/elan -L 1`).

- [ ] **Step 2: Pin the oracle to Mathlib's toolchain**

```bash
curl -fsSL https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
cat lean-toolchain
lean --version
lean --githash
```

Expected: `lean-toolchain` contains one line like `leanprover/lean4:v4.X.0`. elan reads it from the repo root and auto-installs that toolchain on first `lean` invocation (takes a few minutes). `lean --version` reports exactly the pinned version; `lean --githash` prints a 40-char hex hash.

- [ ] **Step 3: Create the fixture source and regen task**

Create `tests/fixtures/Sample.lean`:

```lean
def leanrFixture : Nat := 42

theorem leanrFixtureIsAnswer : leanrFixture = 42 := rfl
```

Append to `mise.toml`:

```toml
[tasks."fixtures:regen"]
description = "Regenerate oracle golden fixtures (requires the pinned Lean toolchain)"
run = [
  "lean tests/fixtures/Sample.lean -o tests/fixtures/Sample.olean",
  "sh -c 'lean --githash > tests/fixtures/oracle-githash.txt'",
]
```

- [ ] **Step 4: Generate and sanity-check the fixtures**

```bash
mise run fixtures:regen
ls -la tests/fixtures/
head -c 16 tests/fixtures/Sample.olean; echo
cat tests/fixtures/oracle-githash.txt
```

Expected: `Sample.olean` exists (KB-scale binary) and its first bytes are the ASCII string `oleanfile` followed by padding; `oracle-githash.txt` holds the 40-char hash. Fixtures are committed so tests (and CI) are hermetic — CI never needs the Lean toolchain in M0.

- [ ] **Step 5: Write docs/ORACLE.md**

```markdown
# The oracle toolchain

leanr's correctness is defined differentially: the official Lean
toolchain pinned in `lean-toolchain` (the version Mathlib pins) is the
oracle, and leanr must match its observable behavior.

- **The pin changes only at milestone boundaries** (spec: "Compatibility
  target"). Bumping it invalidates every golden fixture.
- Golden fixtures live in `tests/fixtures/`, generated from the oracle by
  `mise run fixtures:regen` and committed, so the test suite is hermetic:
  CI does not install Lean.
- After any pin bump: re-run `mise run fixtures:regen`, review the diff,
  and expect parser/format constants (e.g. in `leanr_olean`) to need
  re-verification against the new Lean source tag.
```

- [ ] **Step 6: Commit**

```bash
git add mise.toml lean-toolchain docs/ORACLE.md tests/fixtures/
git commit -m "feat: pin oracle Lean toolchain (Mathlib's pin) and commit golden fixtures"
```

---

### Task 6: `leanr_olean` — header parser, oracle-verified and panic-free

**Files:**
- Create: `crates/leanr_olean/Cargo.toml`
- Create: `crates/leanr_olean/src/lib.rs`
- Test: `crates/leanr_olean/tests/header.rs`
- Modify: `Cargo.toml` (add workspace member)

**Interfaces:**
- Consumes: `tests/fixtures/Sample.olean` and `tests/fixtures/oracle-githash.txt` from Task 5.
- Produces: `leanr_olean::OleanHeader { githash: String, base_addr: u64 }`, `leanr_olean::OleanHeader::parse(bytes: &[u8]) -> Result<OleanHeader, OleanError>`, and `leanr_olean::OleanError` (enum: `Truncated(usize)`, `BadMagic`, `BadGithash`) — consumed by Task 7's CLI command and extended in M1 for full object-graph parsing.

- [ ] **Step 1: Pin the header layout against the oracle (discovery, recorded in code comments)**

The layout hypothesis (from known `.olean` structure): `magic: [u8; 16]` = `b"oleanfile!!!!!!!"`, then `githash: [u8; 40]` (ASCII hex), then `base_addr: u64` little-endian at offset 56, header total 64 bytes. Verify it before writing code:

```bash
xxd -l 80 tests/fixtures/Sample.olean
git clone --depth 1 --branch "$(cut -d: -f2 lean-toolchain)" https://github.com/leanprover/lean4 /tmp/claude-1000/-workspace/19a14a46-50c1-4039-9b9b-beff4ec77ec9/scratchpad/lean4-src
grep -rn "oleanfile" /tmp/claude-1000/-workspace/19a14a46-50c1-4039-9b9b-beff4ec77ec9/scratchpad/lean4-src/src | head -20
```

Read the file the grep hits (the olean save/load code) at the pinned tag. If the actual layout differs from the hypothesis (newer Lean versions may add version/flags bytes after the magic, or compress the payload), record the **actual** offsets/constants from the oracle source in `lib.rs` comments citing file and line, and use them in Step 3. The golden test in Step 2 is layout-agnostic (it asserts the parsed githash equals the oracle's), so it will catch any mistake.

- [ ] **Step 2: Write the failing tests**

Add `"crates/leanr_olean"` to `members` in the root `Cargo.toml`.

Create `crates/leanr_olean/Cargo.toml`:

```toml
[package]
name = "leanr_olean"
version.workspace = true
edition.workspace = true
license.workspace = true

[dependencies]
thiserror = "2"

[dev-dependencies]
proptest = "1"
```

Create `crates/leanr_olean/tests/header.rs`:

```rust
use std::path::PathBuf;

use leanr_olean::{OleanError, OleanHeader};
use proptest::prelude::*;

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures")
        .join(name)
}

#[test]
fn parses_the_oracle_fixture() {
    let bytes = std::fs::read(fixture("Sample.olean")).unwrap();
    let header = OleanHeader::parse(&bytes).unwrap();

    let expected_githash = std::fs::read_to_string(fixture("oracle-githash.txt")).unwrap();
    assert_eq!(header.githash, expected_githash.trim());
    assert!(header.base_addr > 0, "base address should be a nonzero pointer");
}

#[test]
fn rejects_bad_magic() {
    let bytes = std::fs::read(fixture("Sample.olean")).unwrap();
    let mut corrupted = bytes.clone();
    corrupted[0] ^= 0xFF;
    assert_eq!(OleanHeader::parse(&corrupted), Err(OleanError::BadMagic));
}

#[test]
fn rejects_truncated_input() {
    let bytes = std::fs::read(fixture("Sample.olean")).unwrap();
    let truncated = &bytes[..10];
    assert_eq!(
        OleanHeader::parse(truncated),
        Err(OleanError::Truncated(10))
    );
}

#[test]
fn error_messages_are_human_readable() {
    let msg = OleanError::BadMagic.to_string();
    assert!(msg.contains("olean"), "got: {msg}");
}

proptest! {
    /// .olean bytes are untrusted input (docs/THREAT_MODEL.md): the parser
    /// must never panic, whatever the bytes.
    #[test]
    fn arbitrary_bytes_never_panic(bytes in proptest::collection::vec(any::<u8>(), 0..256)) {
        let _ = OleanHeader::parse(&bytes);
    }
}
```

- [ ] **Step 3: Run tests to verify they fail, then implement**

```bash
cargo test --package leanr_olean
```

Expected: compilation FAILS (`OleanHeader` not defined). Now create `crates/leanr_olean/src/lib.rs` (adjust the two `const`s if Step 1's discovery found different values — cite the oracle source file/line in the comment):

```rust
//! Reader for official Lean `.olean` artifacts.
//!
//! Trust boundary: input bytes are UNTRUSTED (see docs/THREAT_MODEL.md).
//! No code path may panic on arbitrary input.
//!
//! Header layout verified against the oracle toolchain source at the tag
//! pinned in `lean-toolchain` (see the grep procedure in the M0 plan):
//!   offset  0: magic, 16 bytes: b"oleanfile!!!!!!!"
//!   offset 16: githash, 40 ASCII hex bytes
//!   offset 56: base address, u64 little-endian
//!   offset 64: start of compacted object region (M1 territory)

use thiserror::Error;

const MAGIC: &[u8; 16] = b"oleanfile!!!!!!!";
const HEADER_LEN: usize = 64;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OleanHeader {
    pub githash: String,
    pub base_addr: u64,
}

#[derive(Debug, Error, PartialEq, Eq)]
pub enum OleanError {
    #[error("not an olean file: {0} bytes is smaller than the {HEADER_LEN}-byte header")]
    Truncated(usize),
    #[error("not an olean file: bad magic bytes")]
    BadMagic,
    #[error("olean header corrupt: githash is not ASCII hex")]
    BadGithash,
}

impl OleanHeader {
    pub fn parse(bytes: &[u8]) -> Result<OleanHeader, OleanError> {
        if bytes.len() < HEADER_LEN {
            return Err(OleanError::Truncated(bytes.len()));
        }
        if &bytes[..16] != MAGIC {
            return Err(OleanError::BadMagic);
        }
        let githash_bytes = &bytes[16..56];
        if !githash_bytes.iter().all(u8::is_ascii_hexdigit) {
            return Err(OleanError::BadGithash);
        }
        let githash = String::from_utf8(githash_bytes.to_vec()).expect("checked ASCII above");
        let base_addr = u64::from_le_bytes(bytes[56..64].try_into().expect("checked length above"));
        Ok(OleanHeader { githash, base_addr })
    }
}
```

- [ ] **Step 4: Run tests to verify they pass**

```bash
cargo test --package leanr_olean
```

Expected: all 5 tests PASS. If `parses_the_oracle_fixture` fails, the layout hypothesis was wrong: go back to Step 1's grep output, read the oracle's writer code, correct the offsets/constants, and update the layout comment. Do not loosen the test.

- [ ] **Step 5: Lint and commit**

```bash
mise run ci
git add Cargo.toml Cargo.lock crates/leanr_olean/
git commit -m "feat: leanr_olean header parser, golden-tested against the oracle and panic-free by property test"
```

---

### Task 7: `leanr olean info` — wire the parser into the CLI

**Files:**
- Modify: `crates/leanr_cli/Cargo.toml`
- Modify: `crates/leanr_cli/src/main.rs`
- Test: `crates/leanr_cli/tests/cli.rs` (extend)

**Interfaces:**
- Consumes: `leanr_olean::OleanHeader::parse` and `OleanError` from Task 6; fixtures from Task 5.
- Produces: the `leanr olean info <path>` subcommand — M0's demo deliverable — and the clap subcommand structure M1's `leanr check` extends.

- [ ] **Step 1: Write the failing tests**

Append to `crates/leanr_cli/tests/cli.rs`:

```rust
use std::path::PathBuf;

fn fixture(name: &str) -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../tests/fixtures")
        .join(name)
}

#[test]
fn olean_info_prints_header_fields() {
    let githash = std::fs::read_to_string(fixture("oracle-githash.txt")).unwrap();
    Command::cargo_bin("leanr")
        .unwrap()
        .args(["olean", "info"])
        .arg(fixture("Sample.olean"))
        .assert()
        .success()
        .stdout(predicates::str::contains(githash.trim()))
        .stdout(predicates::str::contains("base address"));
}

#[test]
fn olean_info_on_missing_file_fails_with_helpful_error() {
    Command::cargo_bin("leanr")
        .unwrap()
        .args(["olean", "info", "does-not-exist.olean"])
        .assert()
        .failure()
        .stderr(predicates::str::contains("does-not-exist.olean"));
}

#[test]
fn olean_info_on_garbage_fails_without_panicking() {
    let dir = std::env::temp_dir().join("leanr-cli-test");
    std::fs::create_dir_all(&dir).unwrap();
    let garbage = dir.join("garbage.olean");
    std::fs::write(&garbage, b"definitely not an olean").unwrap();

    Command::cargo_bin("leanr")
        .unwrap()
        .args(["olean", "info"])
        .arg(&garbage)
        .assert()
        .failure()
        .stderr(predicates::str::contains("not an olean file"));
}
```

- [ ] **Step 2: Run tests to verify the new ones fail**

```bash
cargo test --package leanr_cli
```

Expected: `version_prints_name_and_semver` still passes; the three new tests FAIL (unknown subcommand `olean`).

- [ ] **Step 3: Implement the subcommand**

```bash
cargo add leanr_olean --package leanr_cli --path crates/leanr_olean
```

Replace `crates/leanr_cli/src/main.rs` with:

```rust
use std::path::PathBuf;
use std::process::ExitCode;

use clap::{Parser, Subcommand};

/// A pure-Rust Lean 4 toolchain.
#[derive(Parser)]
#[command(name = "leanr", version)]
struct Cli {
    #[command(subcommand)]
    command: Command,
}

#[derive(Subcommand)]
enum Command {
    /// Inspect official Lean artifacts.
    Olean {
        #[command(subcommand)]
        command: OleanCommand,
    },
}

#[derive(Subcommand)]
enum OleanCommand {
    /// Print the header of an .olean file.
    Info { path: PathBuf },
}

fn main() -> ExitCode {
    let cli = Cli::parse();
    match cli.command {
        Command::Olean {
            command: OleanCommand::Info { path },
        } => olean_info(&path),
    }
}

fn olean_info(path: &std::path::Path) -> ExitCode {
    let bytes = match std::fs::read(path) {
        Ok(bytes) => bytes,
        Err(err) => {
            eprintln!("error: cannot read {}: {err}", path.display());
            return ExitCode::FAILURE;
        }
    };
    match leanr_olean::OleanHeader::parse(&bytes) {
        Ok(header) => {
            println!("githash:      {}", header.githash);
            println!("base address: {:#x}", header.base_addr);
            ExitCode::SUCCESS
        }
        Err(err) => {
            eprintln!("error: {}: {err}", path.display());
            ExitCode::FAILURE
        }
    }
}
```

- [ ] **Step 4: Run the full gate**

```bash
mise run ci
```

Expected: all tests pass (note: `--version` still works because clap handles it before requiring a subcommand), lint clean, deny and gitleaks green.

- [ ] **Step 5: Update ARCHITECTURE.md status markers** (if Task 3 added "(landing this milestone)" markers, remove them now that the crates exist) **and commit**

```bash
git add crates/ Cargo.toml Cargo.lock ARCHITECTURE.md
git commit -m "feat: leanr olean info subcommand - M0 demo deliverable"
git push origin main
gh run watch --exit-status
```

Expected: CI green on main. **M0 exit criteria met:** pinned env, CI + security gates, front door docs, query engine proven (early cutoff test), oracle pinned with fixtures, and `leanr olean info tests/fixtures/Sample.olean` prints the oracle's githash.

---

## What this plan deliberately defers

- **M1 (own plan, next):** kernel types, full `.olean` compacted-region/object-graph parsing (where mmap and cargo-fuzz arrive), environment reconstruction, `leanr check` over Mathlib.
- cargo-fuzz targets (needs the object-graph parser to be worth fuzzing; proptest covers the header).
- Benchmarks (criterion arrives in M1 with the first perf-relevant code).
- Any crate not named here (`leanr_kernel`, `leanr_elab`, …) — created when first needed, not as empty stubs.
