# M4b-4c P1 — eliminator substrate — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** P1 lands everything `ElabElim` (P2) stands on, with no
elaborator-visible change:

- the `auxRecExt` and `elab_as_elim` decodes
- the five `shouldElabAsElim` environment predicates
- `kabstract`
- `getElabElimInfo`

Each piece is checked against the pinned oracle.

**Architecture:** Two new typed extension decodes in `leanr_olean` feed
two name sets on `MetaCtx` through `EnvExtensions`, the same path
`coe_decls` takes. `kabstract` is a new `leanr_meta` module with its own
`HeadIndex`. `get_elab_elim_info` is a new `leanr_elab` module
(`app/elim_info.rs`). It runs on a telescope opener that is shared with
`AppElab` by a behavior-neutral extraction.

There are two new oracle artifacts:

- `elim.jsonl`: per-constant predicates and `ElabElimInfo`, written by
  `dump_elim.lean`.
- `kabstract` records appended to `meta-queries.jsonl` by
  `dump_defeq.lean`.

**Tech Stack:** Rust (workspace crates `leanr_olean`, `leanr_meta`,
`leanr_elab`), Lean 4 oracle dumpers at `leanprover/lean4:v4.33.0-rc1`,
and `mise` tasks.

**Spec:** `docs/superpowers/specs/2026-10-01-m4b4c-elab-as-elim-design.md`.
Read § Evidence, § Decisions, and every `### P1 —` section before
starting.

## Global Constraints

- Oracle pin: `leanprover/lean4:v4.33.0-rc1`. Never bump it.
- Correctness is differential against the oracle. Every expected value
  in an oracle gate is **dumped by the oracle, never hand-computed**.
  Unit tests may assert values that this plan quotes from an oracle run.
- `.olean` bytes are untrusted. Decoders return `OleanError`; they never
  panic.
- The kernel is untouched. Nothing in this plan edits
  `crates/leanr_kernel`.
- `leanr_meta` changes must be additive and behavior-neutral (the
  accessor precedent). `kabstract` is new code that no existing caller
  reaches. Every existing `oracle_fast` / `oracle_synth` record must stay
  green.
- `leanr_elab` refactors in Task 7 are behavior-neutral. The full elab
  corpus must stay green, with byte-identical regenerated fixtures.
- Build under `/workspace`, never `/tmp`. `/tmp` is a 20Gi EmptyDir.
- `lean` must run from a directory under `/workspace`: elan resolves
  the toolchain from `lean-toolchain`, and outside the repo it fails
  with "no default toolchain".
- Do **not** run `mise run fixtures:regen`. It also runs the Mathlib
  steps. Run only the individual commands this plan names.
- Before every commit, run `cargo fmt --all` and
  `cargo clippy --workspace --all-targets -- -D warnings`. CI's
  `mise run ci` gates on both.
- Comments citing oracle lines (`App.lean:NNNN`) must be checked against
  the v4.33.0-rc1 source before they are committed. Earlier citations
  have been off by 1-2 lines.

## Review Focus

1. **A pattern with a metavariable.** `kabstract` runs `isDefEq` for
   real, so the first match fixes the mvar and later candidates are
   compared against the fixed value. Oracle run (Meta0):
   - `kabstract (P.mk (N.succ two) one) (N.succ ?m)` → `P.mk #0 one`,
     `?m := two`
   - `kabstract (P.mk one two) (N.succ ?m)` → `P.mk #0 two`,
     `?m := N.zero`

   Pinned by Task 5 Step 1, `kabstract_mvar_pattern_first_match_wins`.
2. **A pattern that occurs under a binder or a `let`.** The abstracted
   occurrence must become `bvar offset`, not `bvar 0`. Pinned by the
   `kbinder` / `klet` oracle records (Task 6).
3. **A subterm that is defeq to the pattern but has a different head.**
   It must **not** be abstracted. The head filter is a semantic part of
   `kabstract`, not an optimization. Pinned by the `khead` record
   (Task 6).
4. **An aux-recursor suffix with a `_N` tail.** `casesOn_1` is
   accepted; `casesOnX` and a bare `casesOn` that is not in the tag set
   are rejected. Pinned by Task 3 Step 1,
   `aux_recursor_suffix_rules`.
5. **A tagged or recursor constant whose type needs `whnf` to expose
   its binders.** The telescope must reduce, and the motive arity check
   needs the motive's own reducing telescope. Covered by `elim.jsonl`
   over all 878 constants (Task 8). The hand-built non-sort motive in
   Task 8 Step 1 covers the error arm, which no real declaration
   reaches.

## Spec corrections found while planning

Record these under the spec's § Landed when P1 merges (Task 9):

- **The "union over the import closure" is not P1 code.** No production
  caller builds a `MetaCtx` across modules. Every caller is a test
  harness replaying one import-free fixture, and `EnvExtensions` takes
  plain slices, exactly as for `coe_decls`. The spec's mutation "skip
  the union" has nothing to mutate in P1. It belongs to whichever slice
  first builds a multi-module `MetaCtx`.
- **No dedicated malformed-bytes test.** The new decode arms go through
  `name_req`, the same checked path every name decode uses, and
  `crates/leanr_olean/fuzz/fuzz_targets/module_data.rs` already fuzzes
  `ModuleData::parse` end to end. Crafting a valid-container,
  bad-entry `.olean` by hand would test `name_req`, not the new arms.
- **The `ElabElimInfo` goldens cover every constant**, not only the six
  the spec lists: 878 records, of which 651 are oracle errors. A
  per-constant dump costs nothing extra and also pins the "not an
  eliminator" error path.
- **Measured `majors_pos`, oracle-dumped:**
  - `Eq.subst'` = `[0,2,3,4]`: `α` and `a` enter through the first-order
    rule.
  - `Nat.rec` = `[3]`
  - `Nat.casesOn` = `[1]`
  - `False.rec` = `[1]`
  - `Eq.ndrec` = `[0,1,4,5]`

## File Structure

| File | Change | Responsibility |
|---|---|---|
| `tests/fixtures/elab/Elab0.lean` | modify | add `False`, `@[elab_as_elim] Eq.subst'`, `@[elab_as_elim] natElim` |
| `tests/fixtures/elab/Elab0.olean` | regen | |
| `crates/leanr_elab/tests/seam_audit.rs` | modify | move `elab_as_elim` from the source ban to a head-name query ban |
| `crates/leanr_olean/src/module_data.rs` | modify | `aux_recs`, `elab_as_elim` fields, merge, golden test |
| `crates/leanr_olean/src/interp_id.rs` | modify | two decode arms |
| `crates/leanr_meta/src/metactx.rs` | modify | `EnvExtensions` fields, two sets, five predicates |
| `crates/leanr_meta/src/aux_recursor.rs` | create | predicate unit tests (the predicates themselves live in `metactx.rs` next to `is_coe_decl`) |
| all `EnvExtensions { … }` literal sites (21, listed in Task 3) | modify | pass the two new slices |
| `crates/leanr_meta/tests/support/mod.rs` | modify | `Replayed` carries the two new vectors |
| `tests/fixtures/elab/dump_elim.lean` | create | oracle predicates + `ElabElimInfo` per constant |
| `tests/fixtures/elab/elim.jsonl` | create | its output |
| `mise.toml` | modify | `fixtures:regen-elab` runs `dump_elim.lean` |
| `crates/leanr_meta/tests/aux_recursor_oracle.rs` | create | predicate gate against `elim.jsonl` |
| `crates/leanr_meta/src/head_index.rs` | create | `HeadIndex`, `to_head_index`, `head_num_args` |
| `crates/leanr_meta/src/kabstract.rs` | create | `MetaCtx::kabstract` + unit tests |
| `tests/fixtures/meta/dump_defeq.lean` | modify | `kabstractQueries` |
| `tests/fixtures/meta/meta-queries.jsonl` | regen | appended records only |
| `crates/leanr_meta/tests/oracle_fast.rs` | modify | `"kabstract"` query kind |
| `crates/leanr_elab/src/app/state.rs` | modify | extract `open_forall_telescope_reducing` |
| `crates/leanr_elab/src/elab.rs` | modify | `mk_const_with_fresh_mvar_levels_of(name)` |
| `crates/leanr_elab/src/synthetic/default_inst.rs` | modify | call the shared helper |
| `crates/leanr_elab/src/error.rs` | modify | `ElabError::Eliminator { reason }` |
| `crates/leanr_elab/src/app/elim_info.rs` | create | `ElabElimInfo`, `get_elab_elim_info`, `get_elab_elim_expr_info` |
| `crates/leanr_elab/tests/elim_info_oracle.rs` | create | gate against `elim.jsonl` |

---

### Task 1: Fixture declarations and the seam-audit gate

**Files:**
- Modify: `tests/fixtures/elab/Elab0.lean` (append at end of file)
- Regen: `tests/fixtures/elab/Elab0.olean`
- Modify: `crates/leanr_elab/tests/seam_audit.rs:378-418`
  (`fixture_declares_no_undecoded_elab_attributes`)

**Interfaces:**
- Produces: these constants in `Elab0`, used by every later task:
  - `False`, with `False.rec`, `False.casesOn`, `False.recOn` (no
    `brecOn`: it is a Prop inductive)
  - `Eq.subst'` and `natElim`, both tagged `elab_as_elim`

- [ ] **Step 1: Write the failing gate change.** In `seam_audit.rs`,
  replace the attribute loop and the eliminator loop of
  `fixture_declares_no_undecoded_elab_attributes` with the code below.
  `elab_as_elim` is decoded from this plan on, but P2 has not yet routed
  tagged heads, so queries that *use* them stay banned:

```rust
    let src =
        std::fs::read_to_string(format!("{dir}/Elab0.lean")).expect("committed fixture source");
    // `elab_as_elim` is decoded since M4b-4c P1 (`ModuleData::elab_as_elim`)
    // and tagged declarations exist in the fixture; P2 routes them. Only
    // the still-undecoded attribute stays banned at the source level.
    for attr in ["elab_without_expected_type"] {
        assert!(
            !src.contains(attr),
            "Elab0.lean declares `@[{attr}]`, whose extension leanr does not decode: \
             elabAppArgs' control flow would diverge silently. Decode the extension \
             before adding such a declaration."
        );
    }
    assert!(
        src.contains("@[elab_as_elim]"),
        "M4b-4c P1 fixture: Elab0.lean must declare the tagged eliminators \
         (`Eq.subst'`, `natElim`) that elim.jsonl and P2's corpus use"
    );

    // Until M4b-4c P2 lands `ElabElim`, an eliminator-HEADED query takes the
    // ordinary path and emits a term the oracle does not. Matched on the
    // dotted SUFFIX for recursors (see `isAuxRecursor`, AuxRecursor.lean:31-37)
    // and on the bare name for the two tagged fixture declarations.
    let queries = std::fs::read_to_string(format!("{dir}/elab-queries.jsonl"))
        .expect("committed elab corpus");
    for line in queries.lines().filter(|l| !l.trim().is_empty()) {
        let q: serde_json::Value = serde_json::from_str(line).expect("committed JSONL is valid");
        let (id, src) = (
            q["id"].as_str().expect("id"),
            q["src"].as_str().expect("src"),
        );
        for elim in [
            ".rec", ".recOn", ".casesOn", ".brecOn", ".ndrec", ".ndrecOn", "Eq.subst'",
            "natElim",
        ] {
            assert!(
                !src.contains(elim),
                "{id}: query {src:?} uses an eliminator head (`{elim}`). \
                 `shouldElabAsElim` (App.lean:1322-1328) diverts it to ElabElim, \
                 which leanr gains in M4b-4c P2; do not add such a query before then."
            );
        }
    }
```

  Keep the function's existing doc comment, but change its last
  paragraph to say that P1 decoded `elab_as_elim` and P2 lifts the query
  ban.

- [ ] **Step 2: Run it to verify it fails**

  Run: `cargo test -p leanr_elab --test seam_audit fixture_declares_no_undecoded_elab_attributes`
  Expected: FAIL with "Elab0.lean must declare the tagged eliminators".

- [ ] **Step 3: Append the declarations to `Elab0.lean`.** All three
  were compiled against the current `Elab0` with the pinned toolchain
  while planning.

```lean
-- === M4b-4c: eliminators (elabAsElim) ===
--
-- `False`: an EXPLICIT-motive recursor (`False.rec (motive) (t)`), the
-- only shape where `elabAsElim?`'s "positional `_` counts as missing"
-- rule (App.lean:1425-1430) is reachable — `Nat.rec`'s motive is
-- implicit, so `Nat.rec _ …` puts the `_` in the `zero` minor instead
-- (oracle-measured, spec § Evidence). A Prop inductive: `auxRecExt`
-- gets `False.casesOn`/`False.recOn` and NO `False.brecOn`.
inductive False : Prop

-- Tagged eliminators. `Eq.subst'` makes `getElabElimExprInfo`'s
-- first-order rule observable: oracle `majorsPos = [0,2,3,4]`, where `α`
-- and `a` are majors only because `h : Eq a b` is first-order and
-- mentions `b`. `natElim` has an implicit motive and is used under-
-- applied in P2. `noncomputable`: the code generator rejects `Nat.rec`.
@[elab_as_elim] theorem Eq.subst' {α : Sort u} {motive : α → Prop} {a b : α}
    (h : Eq a b) (m : motive a) : motive b :=
  @Eq.rec α a (fun x _ => motive x) m b h

@[elab_as_elim] noncomputable def natElim {motive : Nat → Sort u}
    (z : motive Nat.zero) (s : (n : Nat) → motive n → motive (Nat.succ n))
    (n : Nat) : motive n :=
  @Nat.rec motive z s n
```

- [ ] **Step 4: Rebuild the olean, re-dump, and prove the existing
  corpus did not move.**

```bash
cd /workspace/tests/fixtures/elab && lean Elab0.lean -o Elab0.olean
cd /workspace/tests/fixtures/elab && LEAN_PATH=$PWD lean --run dump_elab.lean > elab-queries.jsonl
cd /workspace/tests/fixtures/elab && LEAN_PATH=$PWD lean --run dump_structs.lean > structures.jsonl
cd /workspace && git diff --exit-code tests/fixtures/elab/elab-queries.jsonl tests/fixtures/elab/structures.jsonl
```

  Expected: `git diff --exit-code` exits 0, so both dumps are
  byte-identical. If either moved, stop: a new constant changed an
  existing answer, and that must be understood before going on.

- [ ] **Step 5: Run the elab test suite**

  Run: `cargo test -p leanr_elab`
  Expected: PASS, including `fixture_declares_no_undecoded_elab_attributes`
  and `oracle_elab_gate`.

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
git add tests/fixtures/elab/Elab0.lean tests/fixtures/elab/Elab0.olean crates/leanr_elab/tests/seam_audit.rs
git commit -m "M4b-4c P1: eliminator fixture declarations; seam_audit bans eliminator-headed queries"
```

---

### Task 2: Decode `auxRecExt` and the `elab_as_elim` tag

**Files:**
- Modify: `crates/leanr_olean/src/module_data.rs`:
  - add the struct fields next to `coe_decls`, about line 460
  - add the multi-region merge lines next to `coe_decls`, about line 620
  - add the test after `coe_decl_attribute_decodes_tagged_names`, about
    line 990
- Modify: `crates/leanr_olean/src/interp_id.rs`:
  - add the decode arms next to the `"Lean.Meta.coeDeclAttr"` arm,
    about line 1150
  - add the locals and constructor fields

**Interfaces:**
- Produces: `ModuleData::aux_recs: Vec<NameId>` and
  `ModuleData::elab_as_elim: Vec<NameId>`, in wire order, which is
  `Name.quickLt` order.

- [ ] **Step 1: Write the failing test** in `module_data.rs`'s
  `mod tests`:

```rust
    /// `Lean.auxRecExt` (`AuxRecursor.lean:26`, a `TagDeclarationExtension`,
    /// `EnvExtension.lean:92-102`) and `Lean.Elab.Term.elabAsElim`
    /// (`App.lean:1123`, a `registerTagAttribute`, `Attributes.lean:180-201`)
    /// both export a bare, `Name.quickLt`-sorted `Array Name` holding ONLY
    /// the module's own declarations. Wire names confirmed with
    /// `readModuleData` on a compiled module (M4b-4c spec § Evidence).
    #[test]
    fn aux_recursor_and_elab_as_elim_tags_decode() {
        let bytes = fixture("elab/Elab0.olean");
        let mut env = Environment::default();
        let md = ModuleData::parse(&bytes, env.store_mut()).expect("decode");
        let render = |n: NameId| env.store().to_name(None, Some(n)).to_string();

        let aux: Vec<String> = md.aux_recs.iter().map(|n| render(*n)).collect();
        for want in [
            "Nat.casesOn",
            "Nat.recOn",
            "Nat.brecOn",
            "False.casesOn",
            "False.recOn",
        ] {
            assert!(aux.iter().any(|a| a == want), "auxRecExt lacks {want}: {aux:?}");
        }
        // A Prop inductive gets no `brecOn`; `Nat.rec` is a genuine
        // recursor, not an AUX one.
        for absent in ["False.brecOn", "Nat.rec"] {
            assert!(!aux.iter().any(|a| a == absent), "auxRecExt has {absent}");
        }

        let mut tagged: Vec<String> = md.elab_as_elim.iter().map(|n| render(*n)).collect();
        tagged.sort();
        assert_eq!(tagged, vec!["Eq.subst'".to_string(), "natElim".to_string()]);

        let bytes = fixture("Sample.olean");
        let mut env = Environment::default();
        let md = ModuleData::parse(&bytes, env.store_mut()).expect("decode");
        assert!(md.elab_as_elim.is_empty(), "Sample.olean tags nothing");
    }
```

- [ ] **Step 2: Run it to verify it fails**

  Run: `cargo test -p leanr_olean aux_recursor_and_elab_as_elim_tags_decode`
  Expected: compile error, "no field `aux_recs`".

- [ ] **Step 3: Implement.**

  In `module_data.rs`, after the `coe_decls` field:

```rust
    /// Typed decode of `Lean.auxRecExt` (M4b-4c P1): the auxiliary
    /// recursors (`casesOn`, `recOn`, `brecOn`, `binductionOn`, `below`, …)
    /// this module declared. A `TagDeclarationExtension`
    /// (`EnvExtension.lean:92-102`): a bare `Name.quickLt`-sorted
    /// `Array Name`, module-local (`addImportedFn := fun _ => {}`), so a
    /// multi-module consumer unions them. All other extension entries stay
    /// opaque.
    pub aux_recs: Vec<NameId>,
    /// Typed decode of `Lean.Elab.Term.elabAsElim` (M4b-4c P1): the
    /// declarations tagged `@[elab_as_elim]`. A `registerTagAttribute`
    /// extension named after its `builtin_initialize`d constant, same wire
    /// shape as `coe_decls` above (private declarations filtered out at
    /// the exported level, `Attributes.lean:192`).
    pub elab_as_elim: Vec<NameId>,
```

  In the multi-region merge, about line 620, after `coe_decls: …`:

```rust
            aux_recs: std::mem::take(&mut base.aux_recs),
            elab_as_elim: std::mem::take(&mut base.elab_as_elim),
```

  In `interp_id.rs`:
  - declare `let mut aux_recs = Vec::new();` and
    `let mut elab_as_elim = Vec::new();` next to `coe_decls`;
  - add these arms right after the `"Lean.Meta.coeDeclAttr"` arm;
  - add `aux_recs, elab_as_elim,` to the `crate::ModuleData { … }`
    constructor.

```rust
                // TagDeclarationExtension (`mkTagDeclarationExtension`,
                // EnvExtension.lean:92-102; `auxRecExt`, AuxRecursor.lean:26):
                // a bare `Array Name`, the same wire shape as the tag
                // attribute just above.
                "Lean.auxRecExt" => {
                    for e in array(&pf[1])? {
                        aux_recs.push(self.name_req(e)?);
                    }
                }
                // TagAttribute, same posture as `Lean.Meta.coeDeclAttr`
                // above. Key = the `builtin_initialize`d constant
                // `Lean.Elab.Term.elabAsElim` (App.lean:1123), confirmed with
                // `readModuleData` (M4b-4c spec § Evidence).
                "Lean.Elab.Term.elabAsElim" => {
                    for e in array(&pf[1])? {
                        elab_as_elim.push(self.name_req(e)?);
                    }
                }
```

- [ ] **Step 4: Run the tests**

  Run: `cargo test -p leanr_olean`
  Expected: PASS. Then run `cargo build --workspace --all-targets`; it
  must compile, because nothing outside `leanr_olean` destructures
  `ModuleData` exhaustively. If a site does, add `..` there.

- [ ] **Step 5: Mutation check.** Change `"Lean.Elab.Term.elabAsElim"`
  to `"Lean.Elab.Term.elabAsElimX"`, rerun Step 4's test, watch it fail,
  and revert. Do the same for `"Lean.auxRecExt"`.

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
git add crates/leanr_olean/src/module_data.rs crates/leanr_olean/src/interp_id.rs
git commit -m "M4b-4c P1: decode auxRecExt and the elab_as_elim tag extension"
```

---

### Task 3: `MetaCtx` recursor and tag predicates

**Files:**
- Modify: `crates/leanr_meta/src/metactx.rs`:
  - `EnvExtensions` (about lines 291-315)
  - `MetaCtx` fields (next to `coe_decls`, about line 183)
  - `MetaCtx::new` (about line 351)
  - the struct literal in `MetaCtx::new`'s returned value
  - the predicates, next to `is_coe_decl` (about line 1383)
- Create: `crates/leanr_meta/src/aux_recursor.rs` (unit tests only;
  `mod aux_recursor;` under `#[cfg(test)]` in `lib.rs`)
- Modify: every `EnvExtensions { … }` literal that lists fields
  explicitly. Find them with
  `grep -rn "EnvExtensions {" crates --include=*.rs`:
  - `crates/leanr_meta/src/test_support.rs`
  - `crates/leanr_meta/src/whnf.rs`
  - `crates/leanr_meta/tests/{oracle_fast,oracle_synth,synth_sweep,structures}.rs`
  - `crates/leanr_elab/tests/{support/mod,oracle_elab,binder_smoke}.rs`
- Modify: `crates/leanr_meta/tests/support/mod.rs`: the `Replayed`
  struct and `replay_fixture_in`. Also `crates/leanr_elab/tests/support/mod.rs`,
  which destructures `Replayed`.

**Interfaces:**
- Produces, on `impl MetaCtx` (all `pub`):
  - `fn is_aux_recursor(&self, n: NameId) -> bool`
  - `fn is_cases_on_recursor(&self, n: NameId) -> bool`
  - `fn is_rec_on_recursor(&self, n: NameId) -> bool`
  - `fn is_brec_on_recursor(&self, n: NameId) -> bool`
  - `fn has_elab_as_elim_tag(&self, n: NameId) -> bool`
- Produces: `EnvExtensions::{aux_recs, elab_as_elim}: &'a [NameId]` and
  `Replayed::{aux_recs, elab_as_elim}: Vec<NameId>`.

- [ ] **Step 1: Write the failing unit tests** in `aux_recursor.rs`.
  They build names in the environment store before the `MetaCtx`
  borrows it. Use the `with_ctx`-style empty environment from
  `metactx.rs`'s tests; if that helper is private there, copy its
  4-line body.

```rust
//! M4b-4c P1: the `shouldElabAsElim` environment predicates
//! (`AuxRecursor.lean:31-51`; `App.lean:1322-1328`). Oracle-gated over the
//! whole Elab0 fixture by `tests/aux_recursor_oracle.rs`; these pin the
//! suffix rules and the `Eq.ndrec*` hard-codes on synthetic names, which
//! no fixture declares.

use leanr_kernel::bank::{NameId, Store};
use leanr_kernel::Environment;

use crate::{Config, EnvExtensions, MetaCtx};

fn name(st: &mut Store, dotted: &str) -> NameId {
    let mut parent = None;
    for part in dotted.split('.') {
        let s = st.intern_str(None, part).unwrap();
        parent = Some(st.name_str(None, parent, s).unwrap());
    }
    parent.unwrap()
}

#[test]
fn aux_recursor_suffix_rules() {
    let mut env = Environment::default();
    let names: Vec<NameId> = [
        "T.casesOn",
        "T.casesOn_1",
        "T.casesOnX",
        "T.recOn",
        "T.brecOn",
        "T.below",
        "U.casesOn",
        "Eq.ndrec",
        "Eq.ndrec_symm",
        "Eq.ndrecOn",
        "tagged",
    ]
    .iter()
    .map(|s| name(env.store_mut(), s))
    .collect();
    let [cases, cases_1, cases_x, rec_on, brec_on, below, untagged_cases, ndrec, ndrec_symm, ndrec_on, tagged] =
        names[..]
    else {
        unreachable!()
    };
    // `U.casesOn` is deliberately NOT in the tag set: the suffix alone
    // never makes an aux recursor (`isAuxRecursorWithSuffix`, :38-42).
    let aux = [cases, cases_1, cases_x, rec_on, brec_on, below];
    let view = env.view();
    let mut scratch = Store::scratch();
    let ctx = MetaCtx::new(
        view,
        &mut scratch,
        Config::default(),
        EnvExtensions {
            aux_recs: &aux,
            elab_as_elim: &[tagged],
            ..Default::default()
        },
    );
    assert!(ctx.is_cases_on_recursor(cases));
    assert!(ctx.is_cases_on_recursor(cases_1), "`casesOn_` prefix is accepted");
    assert!(!ctx.is_cases_on_recursor(cases_x), "`casesOnX` is not `casesOn_…`");
    assert!(ctx.is_aux_recursor(cases_x), "but it IS tagged");
    assert!(!ctx.is_cases_on_recursor(untagged_cases), "suffix without tag");
    assert!(ctx.is_rec_on_recursor(rec_on) && !ctx.is_rec_on_recursor(cases));
    assert!(ctx.is_brec_on_recursor(brec_on) && !ctx.is_brec_on_recursor(rec_on));
    assert!(ctx.is_aux_recursor(below) && !ctx.is_cases_on_recursor(below));
    // Hard-coded in `isAuxRecursor` (AuxRecursor.lean:35-37), untagged.
    for n in [ndrec, ndrec_symm, ndrec_on] {
        assert!(ctx.is_aux_recursor(n));
    }
    assert!(!ctx.is_rec_on_recursor(ndrec_on), "`ndrecOn` is not `recOn`");
    assert!(ctx.has_elab_as_elim_tag(tagged) && !ctx.has_elab_as_elim_tag(cases));
}
```

  `Environment::default()`'s store is a base region. If `intern_str` or
  `name_str` need `Some(base)` arguments in this crate's conventions,
  match `metactx.rs::mk_name2` (about line 270), which interns into
  `scratch` with `base`. In that case, intern the names in `scratch`
  *before* `MetaCtx::new` and pass `Some(view.store)` as the base. The
  names only need to be the same `NameId`s the predicates are asked
  about.

- [ ] **Step 2: Run it to verify it fails**

  Run: `cargo test -p leanr_meta aux_recursor_suffix_rules`
  Expected: compile error, "no field `aux_recs` on `EnvExtensions`".

- [ ] **Step 3: Implement.**

  In `EnvExtensions`, after `structures`:

```rust
    /// Decoded `Lean.auxRecExt` entries (M4b-4c P1) — the set
    /// `MetaCtx::is_aux_recursor` answers from.
    pub aux_recs: &'a [NameId],
    /// Decoded `Lean.Elab.Term.elabAsElim` entries (M4b-4c P1) — the set
    /// `MetaCtx::has_elab_as_elim_tag` answers from.
    pub elab_as_elim: &'a [NameId],
```

  Add the `MetaCtx` fields `pub(crate) aux_recs: HashSet<NameId>` and
  `pub(crate) elab_as_elim: HashSet<NameId>`, collected in `new` exactly
  the way `coe_decls` is.

  `isAuxRecursor` hard-codes `Eq.ndrec`, `Eq.ndrec_symm` and
  `Eq.ndrecOn`. Intern them once in `new` with the existing `mk_name2`
  helper (`mk_name2(scratch, base, "Eq", "ndrec")`, and so on), and
  store them as `aux_rec_builtins: [NameId; 3]`.

  Predicates, next to `is_coe_decl`:

```rust
    /// oracle: `isAuxRecursor` (`AuxRecursor.lean:31-37`) — tagged in
    /// `auxRecExt`, or one of the three `Eq.ndrec*` the oracle names
    /// outright.
    pub fn is_aux_recursor(&self, n: NameId) -> bool {
        self.aux_recs.contains(&n) || self.aux_rec_builtins.contains(&n)
    }

    /// oracle: `isAuxRecursorWithSuffix` (`AuxRecursor.lean:38-42`):
    /// `.str _ s` with `s == suffix || s.startsWith s!"{suffix}_"`, and an
    /// aux recursor.
    fn is_aux_recursor_with_suffix(&self, n: NameId, suffix: &str) -> bool {
        let base = Some(self.view.store);
        let s = match self.scratch.name_row(base, n) {
            leanr_kernel::bank::names::NameRow::Str { part, .. } => {
                self.scratch.str_at(base, *part)
            }
            leanr_kernel::bank::names::NameRow::Num { .. } => return false,
        };
        let matches = s == suffix
            || s.strip_prefix(suffix).is_some_and(|rest| rest.starts_with('_'));
        matches && self.is_aux_recursor(n)
    }

    /// oracle: `isCasesOnRecursor` (`AuxRecursor.lean:44-45`).
    pub fn is_cases_on_recursor(&self, n: NameId) -> bool {
        self.is_aux_recursor_with_suffix(n, "casesOn")
    }

    /// oracle: `isRecOnRecursor` (`AuxRecursor.lean:47-48`).
    pub fn is_rec_on_recursor(&self, n: NameId) -> bool {
        self.is_aux_recursor_with_suffix(n, "recOn")
    }

    /// oracle: `isBRecOnRecursor` (`AuxRecursor.lean:50-51`).
    pub fn is_brec_on_recursor(&self, n: NameId) -> bool {
        self.is_aux_recursor_with_suffix(n, "brecOn")
    }

    /// oracle: `elabAsElim.hasTag env declName` (`App.lean:1328`).
    pub fn has_elab_as_elim_tag(&self, n: NameId) -> bool {
        self.elab_as_elim.contains(&n)
    }
```

  `NameRow`'s module path and `name_row`'s exact signature are at
  `crates/leanr_kernel/src/bank/mod.rs:263` and `bank/names.rs:10`.
  Adjust the paths to what is exported. `name_row` takes `&self`;
  `self.scratch` is `&mut Store`, which auto-derefs.

  Thread the slices:
  - Add `aux_recs: Vec<NameId>` and `elab_as_elim: Vec<NameId>` to
    `Replayed`, filled from `md.aux_recs` / `md.elab_as_elim`.
  - At every explicit `EnvExtensions { … }` literal, add
    `aux_recs: &aux_recs, elab_as_elim: &elab_as_elim` where the site
    has a decoded `md` or `Replayed` in hand. In `test_support.rs`, take
    `let aux_recs = md.aux_recs; let elab_as_elim = md.elab_as_elim;`
    next to `coe_decls`.
  - Where a site builds an empty context, use `aux_recs: &[]` and
    `elab_as_elim: &[]`.
  - Every `let Replayed { … } = …` destructure in
    `crates/leanr_elab/tests/support/mod.rs` gains the two names and
    passes them on.

- [ ] **Step 4: Run the tests**

  Run: `cargo test -p leanr_meta aux_recursor_suffix_rules && cargo test -p leanr_meta && cargo test -p leanr_elab`
  Expected: PASS. The full suites check that the threading is
  behavior-neutral.

- [ ] **Step 5: Mutation check.** Each of these must turn
  `aux_recursor_suffix_rules` red; revert after each:
  - replace the `strip_prefix … '_'` arm with `false`;
  - drop `&& self.is_aux_recursor(n)`;
  - empty `aux_rec_builtins`.

- [ ] **Step 6: Commit**

```bash
cargo fmt --all && cargo clippy --workspace --all-targets -- -D warnings
git add -A crates/leanr_meta crates/leanr_elab/tests
git commit -m "M4b-4c P1: MetaCtx aux-recursor and elab_as_elim predicates"
```

---

### Task 4: Oracle dump `elim.jsonl` and the predicate gate

**Files:**
- Create: `tests/fixtures/elab/dump_elim.lean`
- Create: `tests/fixtures/elab/elim.jsonl` (generated)
- Modify: `mise.toml`, task `fixtures:regen-elab` (about line 217)
- Create: `crates/leanr_meta/tests/aux_recursor_oracle.rs`

**Interfaces:**
- Produces: `elim.jsonl`, one JSON object per constant of `Elab0`,
  sorted by name:

```
{"n":<name>,"rec":bool,"aux":bool,"casesOn":bool,"recOn":bool,"brecOn":bool,"tag":bool,
 "info":{"motive":N,"majors":[N,…]} | {"err":<first line of the oracle message>}}
```

  Task 8 consumes `rec` and `info`.

- [ ] **Step 1: Write the dumper.** This exact program was run against
  a scratch module during planning and produced 878 records for
  `Elab0` + the Task 1 additions.

```lean
/- M4b-4c P1: per-constant oracle answers for the `shouldElabAsElim`
predicates (`App.lean:1322-1328`, `AuxRecursor.lean:31-51`) and for
`getElabElimInfo` (`App.lean:1006-1053`), over EVERY constant of `Elab0`.
`info` is `{"err": …}` with the message's FIRST line when the oracle
throws (most constants are not eliminators: "unexpected eliminator
resulting type"). Run with LEAN_PATH set to this directory (see
`fixtures:regen-elab`). Consumers: crates/leanr_meta/tests/
aux_recursor_oracle.rs (predicates), crates/leanr_elab/tests/
elim_info_oracle.rs (`rec`, `info`). -/
import Lean
open Lean Lean.Meta Lean.Elab.Term

def nameStr (n : Name) : String := n.toString (escape := false)

unsafe def main : IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Elab0 }] {} (trustLevel := 0) (loadExts := true)
  let names := env.constants.fold (init := #[]) fun acc n _ => acc.push n
  let names := names.qsort (fun a b => nameStr a < nameStr b)
  let coreCtx : Core.Context := { fileName := "<dump_elim>", fileMap := default }
  let coreState : Core.State := { env }
  let go : MetaM Unit := do
    for n in names do
      let info ← try
          let i ← getElabElimInfo n
          pure <| Json.mkObj [("motive", i.motivePos),
            ("majors", Json.arr (i.majorsPos.map toJson))]
        catch ex =>
          let msg ← ex.toMessageData.toString
          pure <| Json.mkObj [("err", (msg.splitOn "\n").headD "")]
      let j := Json.mkObj [
        ("n", nameStr n), ("rec", isRecCore env n), ("aux", isAuxRecursor env n),
        ("casesOn", isCasesOnRecursor env n), ("recOn", isRecOnRecursor env n),
        ("brecOn", isBRecOnRecursor env n), ("tag", elabAsElim.hasTag env n),
        ("info", info)]
      IO.println j.compress
  discard <| go.toIO coreCtx coreState
```

- [ ] **Step 2: Register and run it.** Append this to
  `fixtures:regen-elab`'s `run` list in `mise.toml`:

```toml
  # M4b-4c P1: oracle shouldElabAsElim predicates + getElabElimInfo per
  # constant (crates/leanr_meta/tests/aux_recursor_oracle.rs,
  # crates/leanr_elab/tests/elim_info_oracle.rs).
  "sh -c 'cd tests/fixtures/elab && LEAN_PATH=$PWD lean --run dump_elim.lean > elim.jsonl'",
```

  Run: `cd /workspace/tests/fixtures/elab && LEAN_PATH=$PWD lean --run dump_elim.lean > elim.jsonl && wc -l elim.jsonl && grep -c '"tag":true' elim.jsonl`
  Expected: about 878 lines; `2` tagged.

- [ ] **Step 3: Write the gate**, `crates/leanr_meta/tests/aux_recursor_oracle.rs`:

```rust
//! M4b-4c P1: `MetaCtx`'s `shouldElabAsElim` environment predicates
//! against the oracle's own answers for every constant of Elab0
//! (`tests/fixtures/elab/elim.jsonl`, written by `dump_elim.lean`).
//! `isRec` is a constant-kind test leanr_elab answers from
//! `ConstantInfo::Rec`; it is compared in leanr_elab's
//! `elim_info_oracle.rs`, not here.

mod support;

use leanr_kernel::bank::Store;
use leanr_meta::{Config, EnvExtensions, MetaCtx};
use serde_json::Value;
use support::*;

#[test]
fn aux_recursor_predicates_match_the_oracle_dump() {
    let r = replay_fixture_in("elab", "Elab0.olean");
    let view = r.env.view();
    let mut scratch = Store::scratch();
    let base = Some(view.store);
    let text = std::fs::read_to_string(fixture_in("elab", "elim.jsonl")).unwrap();
    let recs: Vec<Value> = text.lines().map(|l| serde_json::from_str(l).unwrap()).collect();
    let ids: Vec<_> = recs
        .iter()
        .map(|rec| decode_name(&mut scratch, base, rec["n"].as_str().unwrap()))
        .collect();
    let ctx = MetaCtx::new(
        view,
        &mut scratch,
        Config::default(),
        EnvExtensions {
            aux_recs: &r.aux_recs,
            elab_as_elim: &r.elab_as_elim,
            ..Default::default()
        },
    );
    let mut failures = Vec::new();
    for (rec, &id) in recs.iter().zip(&ids) {
        let n = rec["n"].as_str().unwrap();
        let got = [
            ("aux", ctx.is_aux_recursor(id)),
            ("casesOn", ctx.is_cases_on_recursor(id)),
            ("recOn", ctx.is_rec_on_recursor(id)),
            ("brecOn", ctx.is_brec_on_recursor(id)),
            ("tag", ctx.has_elab_as_elim_tag(id)),
        ];
        for (k, g) in got {
            let want = rec[k].as_bool().unwrap();
            if g != want {
                failures.push(format!("{n}.{k}: leanr={g} oracle={want}"));
            }
        }
    }
    assert!(recs.len() > 800, "elim.jsonl covers all of Elab0: {}", recs.len());
    assert!(failures.is_empty(), "{} divergences:\n{}", failures.len(), failures.join("\n"));
}
```

  Use `decode_name` from `support/mod.rs:118`. If it parses `«»`-escaped
  names differently from `nameStr` (`escape := false`), check
  `Eq.subst'` specifically: its `'` is not an escape.

- [ ] **Step 4: Run it**

  Run: `cargo test -p leanr_meta --test aux_recursor_oracle`
  Expected: PASS. If it fails on `Eq.ndrec`, the hard-coded built-ins
  are wrong; Elab0 declares `Eq.ndrec`, and the oracle says
  `"aux":true`.

- [ ] **Step 5: Mutation check.** In the test, swap `r.aux_recs` for
  `&[]`, watch it fail, and revert.

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
git add tests/fixtures/elab/dump_elim.lean tests/fixtures/elab/elim.jsonl mise.toml crates/leanr_meta/tests/aux_recursor_oracle.rs
git commit -m "M4b-4c P1: oracle dump of eliminator predicates and ElabElimInfo; predicate gate"
```

---

### Task 5: `HeadIndex` and `kabstract`

**Files:**
- Create: `crates/leanr_meta/src/head_index.rs`
- Create: `crates/leanr_meta/src/kabstract.rs`
- Modify: `crates/leanr_meta/src/lib.rs` (`mod head_index; mod kabstract;`)

**Interfaces:**
- Produces:
  `pub fn MetaCtx::kabstract(&mut self, e: ExprId, p: ExprId) -> Result<ExprId, MetaError>`
  (`Occurrences.all` only).
- Produces (crate-private):
  - `pub(crate) enum HeadIndex`
  - `pub(crate) fn MetaCtx::to_head_index(&mut self, e) -> Result<HeadIndex, MetaError>`
  - `pub(crate) fn MetaCtx::head_num_args(&self, e) -> usize`

- [ ] **Step 1: Write the failing unit tests** at the bottom of
  `kabstract.rs`. Build them on the Meta0 fixture through
  `test_support.rs`. If there is no `with_meta0_ctx` helper next to
  `with_prelude0_ctx`, add one with the same body, reading
  `meta/Meta0.olean`. Every expected value below comes from an oracle
  run of `kabstract` on Meta0 during planning:

```rust
#[cfg(test)]
mod tests {
    use crate::test_support::with_meta0_ctx;
    // Helpers from `test_support` (add if absent): `c(ctx, "N.succ")` =
    // const with no levels, `app(ctx, f, a)`, `bvar(ctx, i)`.
    use crate::test_support::{app, bvar, c};

    /// oracle (Meta0): `kabstract (P.mk (N.succ two) one) (N.succ ?m)` =
    /// `P.mk #0 one`, `?m := two`. The FIRST candidate (left-to-right,
    /// `app` visits `f` before `a`) fixes `?m`; `one = N.succ N.zero` is
    /// then not defeq to `N.succ two`.
    #[test]
    fn kabstract_mvar_pattern_first_match_wins() {
        with_meta0_ctx(|ctx| {
            let n = c(ctx, "N");
            let m = ctx.mk_fresh_expr_mvar_for_test(n);
            let succ = c(ctx, "N.succ");
            let zero = c(ctx, "N.zero");
            let two = c(ctx, "two");
            let one = app(ctx, succ, zero);
            let succ_two = app(ctx, succ, two);
            let pmk = c(ctx, "P.mk");
            let e = {
                let f = app(ctx, pmk, succ_two);
                app(ctx, f, one)
            };
            let p = app(ctx, succ, m);
            let r = ctx.kabstract(e, p).unwrap();
            let b0 = bvar(ctx, 0);
            let want = {
                let f = app(ctx, pmk, b0);
                app(ctx, f, one)
            };
            assert_eq!(r, want);
            let mv = ctx.instantiate_mvars(m).unwrap();
            assert_eq!(mv, two, "?m := two");
        });
    }

    /// The fvar fast path is plain `abstract` (KAbstract.lean:31-32): it
    /// abstracts EVERY occurrence, with no defeq test.
    #[test]
    fn kabstract_fvar_pattern_is_abstract() {
        with_meta0_ctx(|ctx| {
            let n = c(ctx, "N");
            let x = ctx.push_local_decl(None, n, leanr_kernel::BinderInfo::Default).unwrap();
            let succ = c(ctx, "N.succ");
            let e = app(ctx, succ, x);
            let r = ctx.kabstract(e, x).unwrap();
            let b0 = bvar(ctx, 0);
            assert_eq!(r, app(ctx, succ, b0));
        });
    }
}
```

  `mk_fresh_expr_mvar_for_test` is a stand-in for whatever this crate's
  public fresh-mvar constructor is (`grep -n "pub fn mk_fresh_expr_mvar\|pub fn fresh_expr_mvar" crates/leanr_meta/src/*.rs`).
  Use the real name. Write `c`/`app`/`bvar` in `test_support.rs` over
  `ctx.store_mut().expr_const/expr_app/expr_bvar`, with
  `Some(view.store)` as the base, if equivalents are not there already.

- [ ] **Step 2: Run them to verify they fail**

  Run: `cargo test -p leanr_meta kabstract_`
  Expected: compile error, "no method named `kabstract`".

- [ ] **Step 3: Implement `head_index.rs`.** It ports
  `Lean/HeadIndex.lean`:

```rust
//! oracle: `Lean/HeadIndex.lean` (v4.33.0-rc1) — `HeadIndex`,
//! `Expr.headNumArgs`, `Expr.toHeadIndex`. Consumed by `kabstract.rs`.
//! leanr's existing discrimination-tree keys (`discr_path.rs`) are a
//! different oracle structure (`DiscrTree.Key`) and are not reused.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId, NatId, StrId};

use crate::{MetaCtx, MetaError};

/// oracle: `inductive HeadIndex`. `fvar`/`mvar`/`const` carry the id the
/// node does; hash-consing makes `NameId`/`NatId`/`StrId` equality
/// structural. `Proj` carries the index as `u64` so `Proj`/`ProjBig`
/// compare equal for equal indices.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum HeadIndex {
    FVar(Option<NameId>),
    MVar(Option<NameId>),
    Const(Option<NameId>),
    Proj(Option<NameId>, u64),
    LitNat(NatId),
    LitStr(StrId),
    Sort,
    Lam,
    Forall,
}

impl<'e> MetaCtx<'e> {
    /// oracle: `Expr.headNumArgs` — count `app` spines, looking through
    /// `letE` bodies and `mdata`.
    pub(crate) fn head_num_args(&self, mut e: ExprId) -> usize {
        let mut n = 0;
        loop {
            match self.node(e) {
                Node::App { f, .. } => {
                    n += 1;
                    e = f;
                }
                Node::LetE { body, .. } => e = body,
                Node::MData { expr, .. } => e = expr,
                _ => return n,
            }
        }
    }

    /// oracle: `Expr.toHeadIndex` = `toHeadIndexQuick?` falling back to
    /// `toHeadIndexSlow`. The slow path differs only at `letE`, where it
    /// instantiates the body with the value before continuing — so a
    /// single loop that does that at `letE` IS the oracle's result: the
    /// quick path returns `none` (falls back) exactly when it would reach
    /// a loose `bvar`, i.e. when a let body's head is the let-bound
    /// variable, and instantiating first is what the slow path does.
    /// A loose `bvar` reached without a binding `letE` is the oracle's
    /// `panic!` (unreachable from `kabstract`, which never asks about a
    /// term with loose bvars); here it is an error, never a panic.
    pub(crate) fn to_head_index(&mut self, mut e: ExprId) -> Result<HeadIndex, MetaError> {
        loop {
            return Ok(match self.node(e) {
                Node::MVar { id } => HeadIndex::MVar(id),
                Node::FVar { id } => HeadIndex::FVar(id),
                Node::Const { name, .. } => HeadIndex::Const(name),
                Node::Proj { type_name, idx, .. } => HeadIndex::Proj(type_name, idx as u64),
                Node::ProjBig { type_name, idx, .. } => {
                    let base = Some(self.view.store);
                    let n = self.scratch.nat_at(base, idx);
                    // Indices beyond u64 cannot occur in a well-formed
                    // proj; saturate rather than panic.
                    HeadIndex::Proj(type_name, n.to_u64().unwrap_or(u64::MAX))
                }
                Node::Sort { .. } => HeadIndex::Sort,
                Node::Lam { .. } => HeadIndex::Lam,
                Node::Forall { .. } => HeadIndex::Forall,
                Node::LitNat { v } => HeadIndex::LitNat(v),
                Node::LitStr { v } => HeadIndex::LitStr(v),
                Node::App { f, .. } => {
                    e = f;
                    continue;
                }
                Node::MData { expr, .. } => {
                    e = expr;
                    continue;
                }
                Node::LetE { value, body, .. } => {
                    e = self.instantiate1(body, value)?;
                    continue;
                }
                Node::BVar { .. } | Node::BVarBig { .. } => {
                    return Err(MetaError::Internal(
                        "toHeadIndex: loose bound variable (oracle: panic)".into(),
                    ))
                }
            });
        }
    }
}
```

  The quick path's `letE` arm (`toHeadIndexQuick? b`) on a body headed
  by a constant gives the same answer as instantiating first, since a
  constant head does not mention the bvar. So the single loop is
  exactly equivalent; the doc comment says why.

  Adapt the following to what exists:
  - `MetaError`'s internal-error variant: grep `pub enum MetaError`
    and use the existing variant for "internal invariant", or add an
    `Internal(String)` variant if there is none;
  - `nat_at`'s return type and its `to_u64`: see `transform.rs`'s
    `ProjBig` arm, which already calls `self.scratch.nat_at`.

- [ ] **Step 4: Implement `kabstract.rs`.**

```rust
//! oracle: `Lean/Meta/KAbstract.lean` (v4.33.0-rc1), `kabstract` with
//! `occs := .all` — the only form `ElabElim` (`App.lean:1167-1194`)
//! calls. Abstract every subterm of `e` that is key-matched (same
//! `HeadIndex`, same `headNumArgs`) AND `isDefEq` to `p`, replacing it
//! with the de Bruijn index of the binder depth it sits under.
//!
//! The oracle's `getMCtx`/`setMCtx` rollback (`:58-71`) runs only when a
//! match is EXCLUDED by `occs`; under `.all` every match is included, so
//! it is dead and not ported. A failed `isDefEq` leaves the mctx as
//! `isDefEq` itself leaves it, in both implementations.

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::ExprId;
use leanr_kernel::{abstract_fvars, Nat};

use crate::head_index::HeadIndex;
use crate::{MetaCtx, MetaError};

impl<'e> MetaCtx<'e> {
    /// oracle: `kabstract e p .all` (`KAbstract.lean:29-72`).
    pub fn kabstract(&mut self, e: ExprId, p: ExprId) -> Result<ExprId, MetaError> {
        let e = self.instantiate_mvars(e)?;
        if matches!(self.node(p), Node::FVar { .. }) {
            // oracle :31-32 — "Easy case".
            return Ok(abstract_fvars(
                self.scratch,
                Some(self.view.store),
                e,
                std::slice::from_ref(&p),
                &mut self.guard,
            )?);
        }
        let p_head = self.to_head_index(p)?;
        let p_num_args = self.head_num_args(p);
        self.kabstract_visit(e, 0, p, p_head, p_num_args)
    }

    /// oracle: `visit` (`:37-71`).
    fn kabstract_visit(
        &mut self,
        e: ExprId,
        offset: u32,
        p: ExprId,
        p_head: HeadIndex,
        p_num_args: usize,
    ) -> Result<ExprId, MetaError> {
        self.step()?;
        if self.data(e).loose_bvar_range() > 0
            || self.to_head_index(e)? != p_head
            || self.head_num_args(e) != p_num_args
        {
            return self.kabstract_children(e, offset, p, p_head, p_num_args);
        }
        if self.is_def_eq(e, p)? {
            let base = Some(self.view.store);
            return Ok(self.scratch.expr_bvar(base, &Nat::from(offset as u64))?);
        }
        self.kabstract_children(e, offset, p, p_head, p_num_args)
    }

    /// oracle: `visitChildren` (`:38-46`). Child order is load-bearing:
    /// `isDefEq` assigns metavariables, so the first candidate visited
    /// fixes them for the rest (`app`: `f` then `a`; `letE`: type, value,
    /// body; binders: domain, then body at `offset + 1`).
    fn kabstract_children(
        &mut self,
        e: ExprId,
        offset: u32,
        p: ExprId,
        ph: HeadIndex,
        pn: usize,
    ) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        Ok(match self.node(e) {
            Node::App { f, arg } => {
                let f2 = self.kabstract_visit(f, offset, p, ph, pn)?;
                let a2 = self.kabstract_visit(arg, offset, p, ph, pn)?;
                self.scratch.expr_app(base, f2, a2)?
            }
            Node::MData { data, expr } => {
                let b = self.kabstract_visit(expr, offset, p, ph, pn)?;
                self.scratch.expr_mdata(base, data, b)?
            }
            Node::Proj { type_name, idx, structure } => {
                let b = self.kabstract_visit(structure, offset, p, ph, pn)?;
                self.scratch.expr_proj(base, type_name, &Nat::from(idx as u64), b)?
            }
            Node::ProjBig { type_name, idx, structure } => {
                let n = self.scratch.nat_at(base, idx).clone();
                let b = self.kabstract_visit(structure, offset, p, ph, pn)?;
                self.scratch.expr_proj(base, type_name, &n, b)?
            }
            Node::LetE { decl_name, ty, value, body, non_dep } => {
                let t = self.kabstract_visit(ty, offset, p, ph, pn)?;
                let v = self.kabstract_visit(value, offset, p, ph, pn)?;
                let b = self.kabstract_visit(body, offset + 1, p, ph, pn)?;
                self.scratch.expr_let(base, decl_name, t, v, b, non_dep)?
            }
            Node::Lam { binder_name, binder_type, body, binder_info } => {
                let d = self.kabstract_visit(binder_type, offset, p, ph, pn)?;
                let b = self.kabstract_visit(body, offset + 1, p, ph, pn)?;
                self.scratch.expr_lam(base, binder_name, d, b, binder_info)?
            }
            Node::Forall { binder_name, binder_type, body, binder_info } => {
                let d = self.kabstract_visit(binder_type, offset, p, ph, pn)?;
                let b = self.kabstract_visit(body, offset + 1, p, ph, pn)?;
                self.scratch.expr_forall(base, binder_name, d, b, binder_info)?
            }
            _ => e,
        })
    }
}
```

  Store-constructor arities are in `crates/leanr_kernel/src/bank/terms.rs`
  (lines 441-579). `self.data(e)` is the same accessor `infer.rs:185`
  uses. `self.step()` is the recursion and fuel guard that
  `transform.rs` calls; keep it, because it is the crate's existing
  guard against deep terms.

  In the oracle, the `hasLooseBVars` check comes before the head-index
  check, which is why the code above tests it first. `to_head_index` is
  therefore never asked about a term with loose bvars.

- [ ] **Step 5: Run the tests**

  Run: `cargo test -p leanr_meta kabstract_`
  Expected: PASS.

- [ ] **Step 6: Mutation check.** Each of these must turn a test red;
  revert after each:
  - swap the `App` arm's two visits (visit `arg` first):
    `kabstract_mvar_pattern_first_match_wins` gives `?m := N.zero`
    against `one`;
  - make the fvar fast path fall through to the general path: the fvar
    test still passes, because an fvar matches itself by defeq. Record
    this as an equivalent mutant in § Landed; do not count it as a test
    gap.

- [ ] **Step 7: Commit**

```bash
cargo fmt --all && cargo clippy --workspace --all-targets -- -D warnings
git add crates/leanr_meta/src
git commit -m "M4b-4c P1: HeadIndex and kabstract (Occurrences.all)"
```

---

### Task 6: `kabstract` oracle corpus

**Files:**
- Modify: `tests/fixtures/meta/dump_defeq.lean`: add `kabstractQueries`
  after `approxMvarQueries` (about line 318), and the loop in `main`
  after the `approxMvarQueries` loop (about line 422)
- Regen: `tests/fixtures/meta/meta-queries.jsonl`
- Modify: `crates/leanr_meta/tests/oracle_fast.rs`: add a `"kabstract"`
  branch before the `whnf`/`infer` decode (about line 328)

**Interfaces:**
- Produces records
  `{"id":"<tag>/kabstract/<i>","q":"kabstract","tr":"default","in":<e>,"p":<p>,"out":<result>}`.
- Consumes: `MetaCtx::kabstract` (Task 5).

- [ ] **Step 1: Add the queries to the dumper.** These are the exact
  terms run during planning. The oracle's results are recorded in the
  comments, but the records are regenerated, never hand-written:

```lean
/-- M4b-4c P1: `kabstract e p` (`.all`) queries over Meta0, run at
`default` transparency only (ElabElim's ambient setting). Oracle results
when written (pp form; `#i` = loose bvar):
  kconst  `N.succ two`, p `two`                → `N.succ #0`
  khead   `N.succ (N.succ one)`, p `two`       → unchanged: `N.succ one`
          IS defeq to `two` but its head is `N.succ`, not `two`
  kdelta  `N.succ (redId N.zero)`, p `one`     → `#0` (defeq via delta)
  kbinder `fun x => N.succ one`, p `one`       → `fun x => N.succ #1`
  kloose  `fun x => N.succ x`, p `one`         → unchanged (loose bvar)
  kfn     `one`, p `N.succ`                    → `#0 N.zero`
  klet    `let y := one; N.succ one`, p `one`  → `let y := #0; N.succ #1`
  kmulti  `P.mk one one`, p `one`              → `P.mk #0 #0` -/
def kabstractQueries : List (Name × Nat × Expr × Expr) :=
  [ (`kconst, 0, mkApp (mkConst `N.succ) (mkConst `two), mkConst `two)
  , (`khead, 0, mkApp (mkConst `N.succ) (mkApp (mkConst `N.succ) one), mkConst `two)
  , (`kdelta, 0, mkApp (mkConst `N.succ) (mkApp (mkConst `redId) (mkConst `N.zero)), one)
  , (`kbinder, 0, mkLambda `x .default (mkConst `N) (mkApp (mkConst `N.succ) one), one)
  , (`kloose, 0, mkLambda `x .default (mkConst `N) (mkApp (mkConst `N.succ) (.bvar 0)), one)
  , (`kfn, 0, one, mkConst `N.succ)
  , (`klet, 0, mkLet `y (mkConst `N) one (mkApp (mkConst `N.succ) one), one)
  , (`kmulti, 0, mkApp2 (mkConst `P.mk) one one, one)
  ]
```

  The loop goes in `go`, after the `approxMvarQueries` loop:

```lean
    for (name, i, e, p) in kabstractQueries do
      let r ← kabstract e p
      let (inJ, st1) := (encExpr e).run {}
      let (pJ, st2) := (encExpr p).run st1
      let outJ := (encExpr r).run' st2
      IO.println <| (Json.mkObj
        [("id", s!"{name}/kabstract/{i}"), ("q", "kabstract"), ("tr", "default"),
         ("in", inJ), ("p", pJ), ("out", outJ)]).compress
```

  If `emit` prints with a different JSON key order or compression, use
  the same printing call `emit` uses (`dump_defeq.lean:338-340`) so the
  record format matches.

- [ ] **Step 2: Regenerate, and prove only additions.**

```bash
cd /workspace/tests/fixtures/meta && LEAN_PATH=$PWD lean --run dump_defeq.lean > meta-queries.jsonl
cd /workspace && git diff --numstat tests/fixtures/meta/meta-queries.jsonl
```

  Expected: `8	0`, i.e. 8 lines added and 0 removed. Any removed line
  means an existing record moved; stop and investigate.

- [ ] **Step 3: Write the failing gate branch.** In `oracle_fast.rs`,
  before `let mut scratch = Store::scratch();` for whnf/infer:

```rust
        // M4b-4c P1: `kabstract` records carry `in`/`p`/`out`.
        if kind == "kabstract" {
            let mut scratch = Store::scratch();
            let mut fv = HashMap::new();
            let mut mv = HashMap::new();
            let e = decode_expr(&mut scratch, base, &q["in"], &mut fv, &mut mv);
            let p = decode_expr(&mut scratch, base, &q["p"], &mut fv, &mut mv);
            let mut ctx = MetaCtx::new(
                view,
                &mut scratch,
                Config::default(),
                EnvExtensions {
                    reducibility: &reducibility,
                    matchers: &matchers,
                    instances: &instances,
                    default_instances: &default_instances,
                    projection_fns: &projection_fns,
                    classes: &classes,
                    coe_decls: &coe_decls,
                    structures: &[],
                    aux_recs: &[],
                    elab_as_elim: &[],
                },
            );
            ctx.set_transparency(transparency_of(tr));
            let got = match ctx.kabstract(e, p) {
                Ok(r) => r,
                Err(err) => {
                    failures.push(format!("{id}: leanr errored: {err:?}"));
                    continue;
                }
            };
            drop(ctx);
            let mut est = EncSt::default();
            encode_expr(&scratch, base, e, &mut est);
            encode_expr(&scratch, base, p, &mut est);
            let got_j = encode_expr(&scratch, base, got, &mut est);
            if got_j != q["out"] {
                failures.push(format!("{id}: leanr={got_j} oracle={}", q["out"]));
            }
            continue;
        }
```

  Match the local names used by the surrounding code in this function
  (`view`, `base`, the extension vectors, `failures`, `tr`, `id`).

- [ ] **Step 4: Run the gate**

  Run: `cargo test -p leanr_meta --test oracle_fast`
  Expected: PASS, with all 8 new records green and every old record
  still green.

- [ ] **Step 5: Mutation check.** Each must turn the gate red; revert
  after each:
  - delete the `to_head_index(e)? != p_head` condition: `khead` goes red;
  - use `offset` instead of `offset + 1` for `Lam` bodies: `kbinder`
    goes red;
  - use `offset` instead of `offset + 1` for `LetE` bodies: `klet` goes
    red;
  - replace `is_def_eq(e, p)?` with `e == p`: `kdelta` goes red.

- [ ] **Step 6: Commit**

```bash
cargo fmt --all
git add tests/fixtures/meta/dump_defeq.lean tests/fixtures/meta/meta-queries.jsonl crates/leanr_meta/tests/oracle_fast.rs
git commit -m "M4b-4c P1: kabstract oracle corpus"
```

---

### Task 7: Share the telescope opener and the fresh-level constant builder

These are behavior-neutral extractions in `leanr_elab`, so that Task 8
does not duplicate fidelity-critical loops.

**Files:**
- Modify: `crates/leanr_elab/src/app/state.rs:545-598` (`AppElab::forall_telescope_reducing`)
- Modify: `crates/leanr_elab/src/elab.rs` (new `TermElabM` method)
- Modify: `crates/leanr_elab/src/synthetic/default_inst.rs:310-340` (`mk_default_instance_candidate`)

**Interfaces:**
- Produces, in `app/state.rs`:
  `pub(crate) fn open_forall_telescope_reducing(elab: &mut TermElabM<'_>, ty: ExprId) -> Result<(Vec<TelescopeBinder>, ExprId), ElabError>`.
  - It pushes one local decl per binder into the ambient `lctx` and does
    **not** restore it. The caller brackets it with
    `lctx_checkpoint`/`lctx_restore`.
  - The returned `ExprId` is the telescope's body: instantiated, and
    **not** whnf'd unless reducing exposed another forall. That is the
    oracle's `k fvars type` with `whnfType := false`
    (`Basic.lean:1474-1485`).
- Produces, in `elab.rs`:
  `pub(crate) fn TermElabM::mk_const_with_fresh_mvar_levels_of(&mut self, name: NameId) -> Result<ExprId, ElabError>`.

- [ ] **Step 1: Extract the opener.** Move the loop out of
  `AppElab::forall_telescope_reducing` into the free function.
  `whnf_forall` is an `AppElab` method, so inline its 5-line body: run
  `elab.mctx.whnf(cur)`, keep the result if it is a `Forall`, else keep
  `cur`.

```rust
pub(crate) fn open_forall_telescope_reducing(
    elab: &mut TermElabM<'_>,
    ty: ExprId,
) -> Result<(Vec<TelescopeBinder>, ExprId), ElabError> {
    let mut binders: Vec<TelescopeBinder> = Vec::new();
    let mut cur = ty;
    loop {
        // (existing oracle comment about `process`, moved verbatim)
        let reduced = if matches!(lval::node(elab, cur), Node::Forall { .. }) {
            cur
        } else {
            let r = elab.mctx.whnf(cur)?;
            if matches!(lval::node(elab, r), Node::Forall { .. }) { r } else { cur }
        };
        let Node::Forall { binder_name, binder_type, body, binder_info } = lval::node(elab, reduced)
        else {
            return Ok((binders, cur));
        };
        let fvar = elab
            .mctx
            .push_local_decl(binder_name, binder_type, binder_info)
            .map_err(ElabError::from)?;
        cur = elab.mctx.instantiate_beta_rev_range(body, std::slice::from_ref(&fvar))?;
        binders.push(TelescopeBinder { name: binder_name, fvar, ty: binder_type });
    }
}
```

  `AppElab::forall_telescope_reducing` becomes:

```rust
    pub(crate) fn forall_telescope_reducing<R>(
        &mut self,
        ty: ExprId,
        k: impl FnOnce(&mut Self, &[TelescopeBinder]) -> Result<R, ElabError>,
    ) -> Result<R, ElabError> {
        let checkpoint = self.elab.mctx.lctx_checkpoint();
        let result = (|| {
            let (binders, _body) = open_forall_telescope_reducing(self.elab, ty)?;
            k(self, &binders)
        })();
        self.elab.mctx.lctx_restore(checkpoint);
        result
    }
```

  Keep the method's existing doc comment, and add one sentence saying
  that the loop now lives in `open_forall_telescope_reducing`, shared
  with `app/elim_info.rs`. `self.elab` is a `&mut TermElabM` field;
  match how other `AppElab` code passes it.

- [ ] **Step 2: Extract the constant builder.** Move
  `mk_default_instance_candidate`'s body into
  `TermElabM::mk_const_with_fresh_mvar_levels_of(name)` in `elab.rs`,
  together with its doc comment, retitled to cite
  `mkConstWithFreshMVarLevels` (`Lean/Meta/Basic.lean`; verify the line
  number). `mk_default_instance_candidate` becomes a one-line call to
  it.

- [ ] **Step 3: Prove neutrality**

  Run: `cargo test -p leanr_elab`
  Expected: PASS. This includes `oracle_elab_gate`, the full elab
  corpus, unchanged.

- [ ] **Step 4: Commit**

```bash
cargo fmt --all && cargo clippy --workspace --all-targets -- -D warnings
git add crates/leanr_elab/src
git commit -m "M4b-4c P1: share the forall-telescope opener and the fresh-level constant builder"
```

---

### Task 8: `get_elab_elim_info`

**Files:**
- Create: `crates/leanr_elab/src/app/elim_info.rs` (`pub mod elim_info;`
  in `app/mod.rs`)
- Modify: `crates/leanr_elab/src/error.rs` (new variant + reason enum)
- Create: `crates/leanr_elab/tests/elim_info_oracle.rs`

**Interfaces:**
- Consumes: `open_forall_telescope_reducing` and
  `mk_const_with_fresh_mvar_levels_of` (Task 7); `elim.jsonl` (Task 4).
- Produces (P2 relies on these exact names):

```rust
pub struct ElabElimInfo {
    pub elim_expr: ExprId,
    pub elim_type: ExprId,
    pub motive_pos: usize,
    pub majors_pos: Vec<usize>,
}
pub fn get_elab_elim_info(elab: &mut TermElabM<'_>, name: NameId) -> Result<ElabElimInfo, ElabError>;
pub fn get_elab_elim_expr_info(elab: &mut TermElabM<'_>, elim_expr: ExprId) -> Result<ElabElimInfo, ElabError>;
// error.rs
ElabError::Eliminator { reason: EliminatorErrorReason }
pub enum EliminatorErrorReason {
    UnexpectedResultingType,
    UnexpectedMotiveArity,
    MotiveResultNotSort,
    UnexpectedEliminatorType,
}
impl EliminatorErrorReason { pub fn oracle_first_line(self) -> &'static str }
```

  P2 adds the `ElabElim` reasons to the same enum.

- [ ] **Step 1: Write the failing oracle gate**, `tests/elim_info_oracle.rs`:

```rust
//! M4b-4c P1: `get_elab_elim_info` and the `isRec` disjunct against the
//! oracle for EVERY constant of Elab0 (`tests/fixtures/elab/elim.jsonl`,
//! `dump_elim.lean`). Errors compare by the oracle message's first line.

mod support;

use leanr_elab::app::elim_info::get_elab_elim_info;
use leanr_elab::error::ElabError;
use serde_json::Value;

#[test]
fn elab_elim_info_matches_the_oracle_dump() {
    let text = std::fs::read_to_string(support::fixture_in("elab", "elim.jsonl")).unwrap();
    let recs: Vec<Value> = text.lines().map(|l| serde_json::from_str(l).unwrap()).collect();
    let mut failures = Vec::new();
    for rec in &recs {
        let n = rec["n"].as_str().unwrap();
        support::with_elab_env(|elab| {
            let id = support::name_id(elab, n);
            let is_rec = matches!(elab.view.get(id), Some(leanr_kernel::ConstantInfo::Rec(_)));
            if is_rec != rec["rec"].as_bool().unwrap() {
                failures.push(format!("{n}.rec: leanr={is_rec}"));
            }
            let want = &rec["info"];
            match (get_elab_elim_info(elab, id), want.get("err")) {
                (Ok(i), None) => {
                    let wm = want["motive"].as_u64().unwrap() as usize;
                    let wj: Vec<usize> = want["majors"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|v| v.as_u64().unwrap() as usize)
                        .collect();
                    if i.motive_pos != wm || i.majors_pos != wj {
                        failures.push(format!(
                            "{n}: leanr motive={} majors={:?}; oracle motive={wm} majors={wj:?}",
                            i.motive_pos, i.majors_pos
                        ));
                    }
                }
                (Err(ElabError::Eliminator { reason }), Some(w)) => {
                    if reason.oracle_first_line() != w.as_str().unwrap() {
                        failures.push(format!("{n}: leanr err {reason:?}; oracle {w}"));
                    }
                }
                (got, _) => failures.push(format!("{n}: leanr {got:?}; oracle {want}")),
            }
        });
    }
    assert!(failures.is_empty(), "{} divergences:\n{}", failures.len(), failures.join("\n"));
}
```

  `support::with_elab_env` and `support::name_id` stand for whatever
  `crates/leanr_elab/tests/support/mod.rs` already offers. It builds a
  `TermElabM` over `Elab0.olean` near line 709, in the
  `with_elab`/`replay_fixture_in("elab", …)` helpers. Add the thinnest
  wrapper that yields `&mut TermElabM`, plus a dotted-name → `NameId`
  lookup (`decode_name` from leanr_meta's test support is the model).

  A fresh environment per record keeps mvar counters from leaking
  between records. If that is too slow (more than about 10s for 878
  records), share one `TermElabM` and wrap each call in an
  mctx/lctx checkpoint and restore. The answers do not depend on mvar
  numbering.

- [ ] **Step 2: Add the hand-built error test** at the bottom of
  `elim_info.rs`. It covers the motive-not-a-sort arm, which no real
  declaration reaches, because the attribute validator rejects such
  declarations. Build
  `elim : (m : Nat → Nat) → (n : Nat) → m n` as an fvar, with the type
  constructed from the store, and assert
  `get_elab_elim_expr_info(elab, elim)` returns
  `Eliminator { reason: MotiveResultNotSort }`. Then build
  `(m : Nat → Prop) → m` (the motive has 0 arguments) and assert
  `UnexpectedResultingType`, the oracle's `motiveArgs.size > 0` check at
  `App.lean:1013`.

- [ ] **Step 3: Run it to verify it fails**

  Run: `cargo test -p leanr_elab --test elim_info_oracle`
  Expected: compile error, "unresolved import `leanr_elab::app::elim_info`".

- [ ] **Step 4: Add the error variant.** In `error.rs`:

```rust
    /// oracle: the eliminator elaborator's throws — `getElabElimExprInfo`
    /// (`App.lean:1006-1050`) from M4b-4c P1; `ElabElim` (`:1140-1319`)
    /// from P2. Prose deferred; `oracle_first_line` is what the oracle
    /// gate compares.
    Eliminator { reason: EliminatorErrorReason },
```

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EliminatorErrorReason {
    /// `App.lean:1012-1013`.
    UnexpectedResultingType,
    /// `App.lean:1016-1017`.
    UnexpectedMotiveArity,
    /// `App.lean:1018-1019`.
    MotiveResultNotSort,
    /// `App.lean:1020-1021`. Unreachable: the motive is a telescope fvar by
    /// construction. Ported for fidelity.
    UnexpectedEliminatorType,
}

impl EliminatorErrorReason {
    /// The first line of the oracle's `throwError` text.
    pub fn oracle_first_line(self) -> &'static str {
        match self {
            Self::UnexpectedResultingType => "unexpected eliminator resulting type",
            Self::UnexpectedMotiveArity => "unexpected number of arguments at motive type",
            Self::MotiveResultNotSort => "motive result type must be a sort",
            Self::UnexpectedEliminatorType => "unexpected eliminator type",
        }
    }
}
```

  Check the four line citations against the source before committing.
  If `ElabError` has an exhaustive `match` anywhere (Display, an
  `is_oracle_error` helper in tests), add the arm.

- [ ] **Step 5: Implement `app/elim_info.rs`.**

```rust
//! oracle: `ElabElimInfo` / `getElabElimExprInfo` / `getElabElimInfo`
//! (`Lean/Elab/App.lean:976-1053`, v4.33.0-rc1) — where the motive is
//! and which parameters are "major" (elaborated eagerly because they can
//! inform motive inference). Consumed by P2's `elabAsElim?` gate and
//! `ElabElim`. Pure MetaM in the oracle; it lives here because the
//! oracle defines it in `Elab/App.lean`.

use std::collections::HashSet;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};

use crate::app::lval::node;
use crate::app::state::open_forall_telescope_reducing;
use crate::elab::TermElabM;
use crate::error::{ElabError, EliminatorErrorReason as R};

/// oracle: `structure ElabElimInfo` (`App.lean:976-1004`).
#[derive(Debug, Clone)]
pub struct ElabElimInfo {
    pub elim_expr: ExprId,
    pub elim_type: ExprId,
    pub motive_pos: usize,
    pub majors_pos: Vec<usize>,
}

/// oracle: `getElabElimInfo` (`App.lean:1052-1053`).
pub fn get_elab_elim_info(
    elab: &mut TermElabM<'_>,
    name: NameId,
) -> Result<ElabElimInfo, ElabError> {
    let e = elab.mk_const_with_fresh_mvar_levels_of(name)?;
    get_elab_elim_expr_info(elab, e)
}

/// oracle: `getElabElimExprInfo` (`App.lean:1006-1050`).
pub fn get_elab_elim_expr_info(
    elab: &mut TermElabM<'_>,
    elim_expr: ExprId,
) -> Result<ElabElimInfo, ElabError> {
    let elim_type = elab.mctx.infer_type(elim_expr)?;
    let cp = elab.mctx.lctx_checkpoint();
    let r = (|| {
        let (xs, ty) = open_forall_telescope_reducing(elab, elim_type)?;
        let motive = get_app_fn(elab, ty);
        let motive_args = get_app_args(elab, ty);
        if !matches!(node(elab, motive), Node::FVar { .. }) || motive_args.is_empty() {
            return Err(ElabError::Eliminator { reason: R::UnexpectedResultingType });
        }
        let motive_type = elab.mctx.infer_type(motive)?;
        let cp2 = elab.mctx.lctx_checkpoint();
        let shape = (|| {
            let (params, res) = open_forall_telescope_reducing(elab, motive_type)?;
            if params.len() != motive_args.len() {
                return Err(ElabError::Eliminator { reason: R::UnexpectedMotiveArity });
            }
            if !matches!(node(elab, res), Node::Sort { .. }) {
                return Err(ElabError::Eliminator { reason: R::MotiveResultNotSort });
            }
            Ok(())
        })();
        elab.mctx.lctx_restore(cp2);
        shape?;
        let Some(motive_pos) = xs.iter().position(|x| x.fvar == motive) else {
            return Err(ElabError::Eliminator { reason: R::UnexpectedEliminatorType });
        };
        // oracle :1025-1032 — fvars of the motive's arguments, closed
        // right-to-left under "x ∈ set ⇒ add fvars(type x)".
        let mut motive_fvars: HashSet<ExprId> = HashSet::new();
        for &a in &motive_args {
            collect_fvars(elab, a, &mut motive_fvars);
        }
        for x in xs.iter().rev() {
            if motive_fvars.contains(&x.fvar) {
                collect_fvars(elab, x.ty, &mut motive_fvars);
            }
        }
        // oracle :1034-1046.
        let mut majors_pos = Vec::new();
        for (i, x) in xs.iter().enumerate() {
            if i == motive_pos {
                continue;
            }
            if motive_fvars.contains(&x.fvar)
                || (is_first_order(elab, x.ty) && mentions_any(elab, x.ty, &motive_fvars))
            {
                majors_pos.push(i);
            }
        }
        Ok(ElabElimInfo { elim_expr, elim_type, motive_pos, majors_pos })
    })();
    elab.mctx.lctx_restore(cp);
    r
}
```

  Private helpers in the same file. Each is a structural walk over
  `node(elab, e)` that visits every child (app f/arg; lam/forall domain
  and body; let type, value and body; mdata; proj):
  - `get_app_fn`, `get_app_args`: copy them from `app/lval.rs` if they
    are `pub(crate)` there (`lval.rs` has `app_fn`/`app_args`, which
    the M4b-4a P1 debt notes record as duplicates of meta helpers). Use
    them; do not add a third copy.
  - `collect_fvars(elab, e, &mut HashSet<ExprId>)`: insert every
    `Node::FVar` subterm's `ExprId`. Hash-consing makes `ExprId`
    equality fvar identity. Skip subterms whose `has_fvar()` data bit is
    false (`expr_data(..).has_fvar()`, `leanr_kernel/src/expr.rs:272`).
  - `is_first_order(elab, e) -> bool`: the oracle's
    `Option.isNone <| e.find? fun e => e.isApp && !e.getAppFn.isConst`.
    It returns false if *any* subterm is an `App` whose `get_app_fn` is
    not a `Const`. That includes the head of `e` itself, and subterms
    under binders.
  - `mentions_any(elab, e, set) -> bool`: true if any `FVar` subterm is
    in `set`.

  The oracle's `xType ← x.fvarId!.getType` is the decl type, which is
  `TelescopeBinder::ty`. `inferType motive` for an fvar is likewise its
  decl type. Reading it through `infer_type` keeps the code shaped like
  the oracle's.

- [ ] **Step 6: Run the gate and the unit tests**

  Run: `cargo test -p leanr_elab --test elim_info_oracle && cargo test -p leanr_elab elim_info`
  Expected: PASS.

  If a single non-eliminator constant diverges and the cause is an
  unrelated gap, for example the M4b-4b level-normalization gap inside
  `whnf`, do not paper over it:
  - add that name to a `const KNOWN_GAPS: &[(&str, &str)]` (name,
    reason) at the top of the test;
  - assert that every listed name still diverges, so the list cannot
    rot;
  - record it in § Landed.

  Any divergence on `Nat.rec`, `Nat.casesOn`, `Nat.recOn`,
  `Nat.brecOn`, `Eq.rec`, `Eq.ndrec`, `False.rec`, `Eq.subst'` or
  `natElim` is a P1 bug, not a gap.

- [ ] **Step 7: Mutation check.** Each must turn the gate red; revert
  after each:
  - drop the `is_first_order && mentions_any` disjunct: `Eq.subst'`
    loses majors 0 and 2;
  - skip the reverse closure loop: `Eq.rec`/`Eq.ndrec` majors shrink;
  - iterate the closure forward instead of in reverse: at least one
    record changes. If none does, record it in § Landed as a surviving
    mutant with the reason;
  - remove the `motive_args.is_empty()` check: the hand-built test goes
    red.

- [ ] **Step 8: Commit**

```bash
cargo fmt --all && cargo clippy --workspace --all-targets -- -D warnings
git add crates/leanr_elab/src crates/leanr_elab/tests/elim_info_oracle.rs crates/leanr_elab/tests/support
git commit -m "M4b-4c P1: getElabElimInfo, gated against the oracle for every Elab0 constant"
```

---

### Task 9: Close out P1

**Files:**
- Modify: `docs/superpowers/specs/2026-10-01-m4b4c-elab-as-elim-design.md` (§ Landed)

- [ ] **Step 1: Run full CI locally, blocking.**

  Run: `cd /workspace && mise run ci; echo CI_EXIT=$?`
  Expected: `CI_EXIT=0`. Do not background this, and do not end the
  turn before the marker prints.

- [ ] **Step 2: Sweep citations.** For every `App.lean:`,
  `AuxRecursor.lean:`, `KAbstract.lean:`, `HeadIndex.lean:`,
  `EnvExtension.lean:`, `Attributes.lean:` and `Basic.lean:` cite this
  branch added (`git diff main --stat` lists the files), open the line
  in
  `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/Lean/`
  and fix any that are off.

- [ ] **Step 3: Write § Landed › P1** in the spec:
  - the PR number;
  - the four spec corrections from this plan's "Spec corrections"
    section;
  - every mutation run and its outcome, including survivors and
    equivalent mutants;
  - any `KNOWN_GAPS` entries;
  - confirmation that P1 changed no elaborator-visible behavior: the
    elab corpus is byte-identical and the recursor seams are unchanged.

- [ ] **Step 4: Commit, push, and open the PR.**

```bash
git add docs/superpowers/specs/2026-10-01-m4b4c-elab-as-elim-design.md
git commit -m "M4b-4c P1: spec § Landed"
git -c credential.helper= -c credential.helper="!$(which gh) auth git-credential" push -u origin HEAD
gh pr create --title "M4b-4c P1: eliminator substrate (decodes, predicates, kabstract, ElabElimInfo)" --body "<summary + § Landed excerpt>"
```

  Then follow the standing merge workflow: merge on green CI, verify
  `main`, and delete the branch.
