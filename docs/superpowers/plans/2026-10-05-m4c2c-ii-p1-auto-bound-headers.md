# M4c-2c-ii P1 — auto-bound implicits in headers — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** An unbound identifier or universe name in a def/theorem/abbrev/
opaque/example/axiom header is auto-bound as the oracle does (including
mvar binders such as `theorem t : a = a`), and `set_option autoImplicit` /
`relaxedAutoImplicit` govern it — every one of 93 oracle-probed file-corpus
rows matching.

**Architecture:** A faithful port of `withAutoBoundImplicit`'s
exception-and-retry loop in `leanr_elab` (new internal error
`AutoBoundImplicitLocal`, thrown from the unknown-identifier path, caught
only by the loop, which rewinds term state + `level_names` + lctx and
re-runs with one more implicit local). `addAutoBoundImplicits` +
`collectUnassignedMVars` prepend the autos (and the unassigned mvars in
their types) to the header telescope; `leanr_meta`'s `mk_binding` gains the
oracle's mvar arm so those mvars become implicit binders. Options live on
the command `Scope` and seed each `TermElabM`.

**Tech Stack:** Rust (cargo workspace, mise tasks), Lean 4 oracle
`leanprover/lean4:v4.33.0-rc1` (fixtures only; never in CI).

**Spec:** `docs/superpowers/specs/2026-10-05-m4c2c-ii-auto-bound-design.md`
(read **Amendment 1** at the end: it overrides the body on
`setMVarUserNamesAt`, the note line, `throwInvalidNamedArg` and the
catch-site audit).

## Global Constraints

- Oracle pin: `leanprover/lean4:v4.33.0-rc1`; never bump it.
- `leanr_kernel` is TCB: this plan changes NO file under
  `crates/leanr_kernel/`.
- `leanr_meta` changes are additive and TCB-neutral (M4b precedent): a new
  `MetaCtx` field, a new private module, and the mvar arm of
  `mk_binding`. An fvar-only telescope must take exactly today's code
  path (the kernel's `abstract_fvars`).
- No new dependencies.
- Seam labels end in ` — <slice>`; P1 leaves the `variable` binder seam
  labelled `— M4c-2c-ii` (P2 removes it). Non-whitelisted `set_option`
  names are `— later M4`.
- Before every commit: `cargo fmt --all` and
  `cargo clippy --workspace --all-targets -- -D warnings` (CI runs
  `mise run ci`, which gates on both). Never background `mise run ci` and
  end a turn: run it blocking.
- Build only under `/workspace` (never `/tmp`: a 20Gi EmptyDir).
- Every commit body records the mutations its tests kill (`Mutation:
  <what> ⇒ <which test fails>`); reviewers read bodies with
  `git log --format=%B`.
- Fixture regen needs the elan toolchain: `mise run fixtures:regen-decls`.
  It never runs in CI.

## Review Focus

1. **Lctx restore under nested binders.** An auto discovered while a
   `∀ (y : Nat)` binder is open (`auto/identNestedBinder`) must be
   declared at the OUTER level after the restore drops `y`; a reviewer
   should expect the axiom `∀ {z : Nat} (g : ∀ y, y = z), Nat`. Pinned
   in Task 4.
2. **Many autos.** 30 distinct autos in one header (`auto/identThirty`)
   means 31 attempts; the loop must be iterative (no recursion per retry)
   and the `u_N` names must sort lexicographically on the axiom path
   (`u_1, u_10, …, u_19, u_2, …`). Pinned in Task 4.
3. **The body is NOT auto-bound.** An unknown identifier in a value —
   including a theorem's async body — is a plain "Unknown identifier"
   (`auto/negBody`, `auto/negThmBody`). Pinned in Task 4.
4. **A section variable shadows a would-be auto.** `variable (α : Type)`
   then `def ai24 (x : α)` must use the section variable, not bind a new
   `α` (`auto/withSectionShadow`). Pinned in Task 4.
5. **Retry rewinds universe names.** A universe auto-bound before an
   identifier retry must not be pushed twice (`auto/levelThenIdent` ⇒
   `[u, u_1]`). Pinned in Task 5 (on the header path `with_level_names`
   inside the loop is what rewinds; the loop's own snapshot is P2's).

## File map

| File | Change |
|---|---|
| `tests/fixtures/elab/dump_decls.lean` | +93 `fileQueries` rows (Task 1) |
| `tests/fixtures/elab/file-queries.jsonl` | regenerated (Task 1) |
| `crates/leanr_elab/tests/oracle_file.rs` | `PENDING` prefix gate, floor bump; seam tests updated |
| `crates/leanr_elab/tests/oracle_decl.rs` | three auto-bound seam tests replaced |
| `crates/leanr_meta/src/abstract_vars.rs` | NEW: fvar+mvar abstraction (Task 2) |
| `crates/leanr_meta/src/metactx.rs` | `mvar_ids_to_abstract` field; `mk_binding` mvar arm (Task 2) |
| `crates/leanr_meta/src/mk_binding.rs` | `elim_app` keeps to-abstract mvars; `abstract_range` uses `abstract_vars` (Task 2) |
| `crates/leanr_meta/src/lib.rs` | `mod abstract_vars;` (Task 2) |
| `crates/leanr_elab/src/auto_bound.rs` | NEW: context, name checks, loop, `add_auto_bound_implicits` (Tasks 3-4) |
| `crates/leanr_elab/src/error.rs` | `AutoBoundImplicitLocal`, `UnknownUniverseLevel`, `InvalidNamedArg`, `SetOptionTypeMismatch` |
| `crates/leanr_elab/src/elab.rs` | `TermElabM` fields `auto_bound`, `auto_bound_forbidden`, `options` |
| `crates/leanr_elab/src/app/head.rs`, `app/mod.rs` | unknown-id throw sites (Task 3) |
| `crates/leanr_elab/src/builtin/sort.rs` | level auto-bound (Task 5) |
| `crates/leanr_elab/src/app/args.rs` | `throwInvalidNamedArg` (Task 6) |
| `crates/leanr_elab/src/command/header.rs`, `axiom.rs` | wiring; seam mappers deleted (Task 4) |
| `crates/leanr_elab/src/command/scope.rs`, `mod.rs` | `Scope.options`, `set_option` arm, seeding (Task 7) |
| `crates/leanr_elab/src/lib.rs`, spec § Landed | docs (Task 8) |

---

### Task 1: Corpus rows and the staged gate

**Files:**
- Modify: `tests/fixtures/elab/dump_decls.lean` (the `fileQueries` list, ends ~line 520)
- Regenerate: `tests/fixtures/elab/file-queries.jsonl`
- Modify: `crates/leanr_elab/tests/oracle_file.rs:13` (floor) and `:146-153` (gate)

**Interfaces:**
- Produces: `const PENDING: &[&str]` in `oracle_file.rs`; later tasks delete
  entries from it. Prefix ↔ task: `auto/ident`, `auto/mvar`, `auto/neg`,
  `auto/catch`, `auto/with` → Task 4; `auto/level` → Task 5;
  `auto/namedArg` → Task 6 (`auto/namedArgIdent`/`MvarFvar` pass at Task 4
  but stay gated under this prefix until Task 6); `opt/` → Task 7.

- [ ] **Step 1: Append the rows.** In `dump_decls.lean`, add a `,` after
  the current last `fileQueries` entry
  (`("omit/referencedAnonInst", …)`) and append these 93 rows before the
  closing `]` (every row was probed against the oracle at plan time;
  scratch `target/m4c2ciiprobe/`, expected output `expected.txt`):

```lean
  ("auto/identDef", "def ai1 (x : α) : α := x"),
  ("auto/identTwoOrder", "def ai2 (x : β) (y : α) : β := x"),
  ("auto/identRetOnly", "def ai3 : α → α := fun x => x"),
  ("auto/identThm", "theorem ai4 (x : α) : Eq x x := rfl"),
  ("auto/identAxiom", "axiom ai5 (x : α) : Eq x x"),
  ("auto/identFn", "def ai6 (f : α → β) (x : α) : β := f x"),
  ("auto/identList", "def ai7 (xs : List α) : List α := xs"),
  ("auto/identNoRetTy", "def ai12 (x : α) := x"),
  ("auto/identExample", "example (x : α) : Eq x x := rfl"),
  ("auto/identInst", "def ai11 [Wrap α] (x : α) : α := x"),
  ("auto/identAssigned", "def ai13 (x : Nat) (h : Eq x y) : Nat := y"),
  ("auto/identRepeat", "def ai14 (x : α) (y : α) : α := y"),
  ("auto/identLater", "def ai1b (x : α) : α := x\ndef ai1c : Nat := ai1b Nat.zero"),
  ("auto/namedArgIdent", "def ai1d (x : α) : α := x\ndef ai1e : Nat := ai1d (α := Nat) Nat.zero"),
  ("auto/mvarThm", "theorem am1 : Eq a a := rfl"),
  ("auto/mvarExample", "example : Eq a a := rfl"),
  ("auto/mvarTwo", "def am2 (h : Eq a b) : Eq a b := h"),
  ("auto/mvarAxiom", "axiom am4 (h : Eq a b) : Eq b a"),
  ("auto/namedArgMvar", "theorem am3 : Eq a a := rfl\nexample : Eq Nat.zero Nat.zero := am3 (α := Nat)"),
  ("auto/namedArgMvarFvar", "theorem am5 : Eq a a := rfl\nexample : Eq Nat.zero Nat.zero := am5 (a := Nat.zero)"),
  ("auto/mvarHEq", "axiom am6 (h : HEq a b) : Nat"),
  ("auto/mvarDep", "axiom am7 (h : dep a) : Nat"),
  ("auto/levelDef", "def al1 (α : Sort u) (a : α) : α := a"),
  ("auto/levelTwo", "def al2 (α : Sort v) (β : Sort u) (a : α) (b : β) : α := a"),
  ("auto/levelExplicit", "def al3.{v} (α : Sort u) (β : Sort v) (a : α) : α := a"),
  ("auto/levelType", "def al4 (α : Type u) : Type u := α"),
  ("auto/levelThm", "theorem al5 (α : Sort u) (a : α) : Eq a a := rfl"),
  ("auto/levelAxiom", "axiom al6 (α : Sort u) : α"),
  ("auto/levelScope", "universe v\ndef al7 (α : Sort u) (β : Sort v) (a : α) : α := a"),
  ("auto/levelBody", "def al8 : Nat := (fun (_ : Sort u) => Nat.zero) Nat"),
  ("auto/levelWithIdent", "def al9 (x : α) (β : Sort u) : α := x"),
  ("auto/levelExplicitArg", "def al10 (α : Sort u) (a : α) : α := a\ndef al11 : Nat := al10.{1} Nat Nat.zero"),
  ("auto/levelThmUnused", "theorem al12 (α : Sort u) : Eq Nat.zero Nat.zero := rfl"),
  ("auto/negDotted", "def an1 (x : Foo.bar) : Nat := Nat.zero"),
  ("auto/negForbidden", "def an2 (x : an2) : Nat := Nat.zero"),
  ("auto/negBody", "def an3 : Nat := zz"),
  ("auto/negFnApp", "def an4 (x : F Nat) : Nat := Nat.zero"),
  ("auto/negForbiddenNs", "namespace N\ndef an5 (x : an5) : Nat := Nat.zero"),
  ("auto/negForbiddenDotted", "def N2.an6 (x : an6) : Nat := Nat.zero"),
  ("auto/negForbiddenAxiom", "axiom an7 (x : an7) : Nat"),
  ("auto/negDependsExplicit", "def ad1 (β : Type) (h : Eq (x : β) x) : Nat := Nat.zero"),
  ("auto/negDependsExplicitAx", "axiom ad2 (β : Type) (h : Eq (x : β) x) : Nat"),
  ("auto/levelNegBody", "def an8 (α : Sort u) : Nat := (fun (_ : Sort v) => Nat.zero) Nat"),
  ("auto/catchOverload", "namespace A\ndef k (n : Nat) : Nat := n\nend A\nnamespace B\ndef k (b : Bool) : Bool := b\nend B\nopen A B\ndef ac1 (h : Eq (k x) (k x)) : Nat := Nat.zero"),
  ("auto/catchCoe", "axiom ac2 (h : Eq (takesInt x) (takesInt x)) : Nat"),
  ("auto/catchAnon", "axiom ac3 (h : Eq ⟨a, b⟩ c) : Nat"),
  ("auto/catchFun", "axiom ac4 (h : Eq (fun y => y) x) : Nat"),
  ("auto/catchInst", "axiom ac5 (h : Eq (Wrap.val (x : α)) x) : Nat"),
  ("auto/catchNum", "axiom ac6 (h : Eq 2 x) : Nat"),
  ("opt/offDef", "set_option autoImplicit false\ndef ao1 (x : α) : α := x"),
  ("opt/offIn", "set_option autoImplicit false in\ndef ao2 (x : α) : α := x"),
  ("opt/offInScoped", "set_option autoImplicit false in\ndef ao3 : Nat := Nat.zero\ndef ao4 (x : α) : α := x"),
  ("opt/offSection", "section\nset_option autoImplicit false\nend\ndef ao5 (x : α) : α := x"),
  ("opt/offNamespace", "namespace M\nset_option autoImplicit false\nend M\ndef ao5b (x : α) : α := x"),
  ("opt/offThenOn", "set_option autoImplicit false\nset_option autoImplicit true\ndef ao5c (x : α) : α := x"),
  ("opt/strictOk", "set_option relaxedAutoImplicit false\ndef ao6 (x : α₁) (y : X12) (z : β') : α₁ := x"),
  ("opt/strictBad", "set_option relaxedAutoImplicit false\ndef ao7 (x : foo) : Nat := Nat.zero"),
  ("opt/strictLevelUpper", "set_option relaxedAutoImplicit false\ndef ao8 (α : Sort U) : Nat := Nat.zero"),
  ("opt/strictLevelOk", "set_option relaxedAutoImplicit false\ndef ao8b (α : Sort u1) : Nat := Nat.zero"),
  ("opt/strictLevelLong", "set_option relaxedAutoImplicit false\ndef ao8c (α : Sort uv) : Nat := Nat.zero"),
  ("opt/offLevel", "set_option autoImplicit false\ndef ao9 (α : Sort u) : Nat := Nat.zero"),
  ("opt/offAxiom", "set_option autoImplicit false\naxiom ao10 (x : α) : Nat"),
  ("opt/offMvar", "set_option autoImplicit false\ntheorem ao11 : Eq a a := rfl"),
  ("opt/badValue", "set_option autoImplicit 1"),
  ("opt/offForbidden", "set_option autoImplicit false\ndef ao12 (x : ao12) : Nat := Nat.zero"),
  ("opt/offDotted", "set_option autoImplicit false\ndef ao13 (x : Foo.bar) : Nat := Nat.zero"),
  ("opt/strictOffBoth", "set_option autoImplicit false\nset_option relaxedAutoImplicit false\ndef ao14 (x : foo) : Nat := Nat.zero"),
  ("auto/levelThenIdent", "def al13 (α : Sort u) (x : β) (a : α) : α := a"),
  ("auto/levelThenIdentThm", "theorem al14 (α : Sort u) (x : β) (a : α) : Eq a a := rfl"),
  ("auto/identBodyUse", "def ai16 (x : α) : List α := List.cons x List.nil"),
  ("auto/identBodyLam", "def ai17 (x : α) : α := (fun (y : α) => y) x"),
  ("auto/withUnusedVar", "variable (n : Nat)\ntheorem ai19 (x : α) : Eq x x := rfl"),
  ("auto/withUsedVar", "variable {β : Type} (b : β)\ndef ai20 (x : α) : PProd α β := PProd.mk x b"),
  ("auto/withUsedVarThm", "variable {β : Type} (b : β)\ntheorem ai21 (x : α) : Eq (PProd.mk x b) (PProd.mk x b) := rfl"),
  ("auto/withScopeUniverse", "universe u\ndef ai22 (x : α) (β : Sort u) : α := x"),
  ("auto/levelSameAsScope", "universe u\ndef al15 (α : Sort u) (a : α) : α := a"),
  ("auto/mvarAndIdent", "axiom am8 (x : γ) (h : Eq a b) : Nat"),
  ("auto/mvarLevelThm", "theorem am9 (h : Eq a b) : Eq a b := h"),
  ("auto/identShadowGlobal", "def pick2 (x : pick) : Nat := Nat.zero"),
  ("auto/identInBinderDefault", "def ai23 (x : α) (y : Nat := Nat.zero) : α := x"),
  ("opt/inThenScoped", "set_option autoImplicit false in\ntheorem ao15 : Eq Nat.zero Nat.zero := rfl\ntheorem ao16 : Eq a a := rfl"),
  ("opt/sectionOffInside", "section\nset_option autoImplicit false\ndef ao17 (x : α) : α := x"),
  ("opt/strictSubscript", "set_option relaxedAutoImplicit false\ndef ao18 (x : α_1) (y : αᵢ) : α_1 := x"),
  ("opt/strictDotted", "set_option relaxedAutoImplicit false\ndef ao19 (x : A.b) : Nat := Nat.zero"),
  ("opt/offRelaxedOff", "set_option relaxedAutoImplicit false\nset_option autoImplicit false\ndef ao20 (x : α) : Nat := Nat.zero"),
  ("auto/levelAxiomOrder", "axiom al16 (α : Sort v) (β : Sort u) : α"),
  ("auto/levelThmOrder", "theorem al17 (α : Sort v) (β : Sort u) (a : α) : Eq a a := rfl"),
  ("auto/levelDefOrderUnusedVal", "def al18 (α : Sort v) (β : Sort u) : Nat := Nat.zero"),
  ("auto/levelAxiomExplicit", "axiom al19.{w} (α : Sort v) (β : Sort w) : α"),
  ("auto/identNestedBinder", "axiom ai26 (g : ∀ (y : Nat), Eq y z) : Nat"),
  ("auto/negThmBody", "theorem an9 (x : α) : Eq x x := zz"),
  ("auto/withSectionShadow", "variable (α : Type)\ndef ai24 (x : α) : α := x"),
  ("auto/identThirty", "axiom ai27 (x0 : t0) (x1 : t1) (x2 : t2) (x3 : t3) (x4 : t4) (x5 : t5) (x6 : t6) (x7 : t7) (x8 : t8) (x9 : t9) (x10 : t10) (x11 : t11) (x12 : t12) (x13 : t13) (x14 : t14) (x15 : t15) (x16 : t16) (x17 : t17) (x18 : t18) (x19 : t19) (x20 : t20) (x21 : t21) (x22 : t22) (x23 : t23) (x24 : t24) (x25 : t25) (x26 : t26) (x27 : t27) (x28 : t28) (x29 : t29) : Nat")
```

- [ ] **Step 2: Regenerate.** Run `mise run fixtures:regen-decls`.
  Expected: `wc -l tests/fixtures/elab/file-queries.jsonl` = 216 + 93 =
  **309**, and the dumper prints nothing on stderr for an `auto/` or
  `opt/` id. `git diff --stat tests/fixtures/elab/decl-queries.jsonl` must
  be empty (the decl corpus is untouched). Spot-check three records
  against `target/m4c2ciiprobe/expected.txt`:
  `grep '"auto/levelAxiomOrder"' tests/fixtures/elab/file-queries.jsonl`
  has `"levelParams":["u","v"]`; `auto/catchOverload`'s last command is
  `{"err":"Ambiguous term"}`; `opt/badValue` is
  `{"err":"set_option value type mismatch: The value"}`.

- [ ] **Step 3: Stage the gate.** In `oracle_file.rs` set
  `const CORPUS_FLOOR: usize = 309;` (update its doc: "M4c-2c-ii P1: 309")
  and replace `oracle_file_gate` with:

```rust
/// M4c-2c-ii P1 rows not yet passing: each task deletes its prefixes
/// (Task 4: `auto/ident` … `auto/with`; Task 5: `auto/level`; Task 6:
/// `auto/namedArg`; Task 7: `opt/`). Empty at the end of P1.
const PENDING: &[&str] = &[
    "auto/ident",
    "auto/mvar",
    "auto/neg",
    "auto/catch",
    "auto/with",
    "auto/level",
    "auto/namedArg",
    "opt/",
];

#[test]
fn oracle_file_gate() {
    let checked = support::run_file_corpus("file-queries.jsonl", |id| {
        !PENDING.iter().any(|p| id.starts_with(p))
    });
    let pending = std::fs::read_to_string(support::fixture_in("elab", "file-queries.jsonl"))
        .expect("corpus")
        .lines()
        .filter(|l| PENDING.iter().any(|p| l.contains(&format!("\"id\":\"{p}"))))
        .count();
    assert!(
        checked + pending >= CORPUS_FLOOR,
        "file corpus shrank: checked {checked} + pending {pending}, floor {CORPUS_FLOOR}. Check \
         `dump_decls.lean files`' stderr for a dropped record, or lower the floor deliberately."
    );
}
```

  If `support::fixture_in` is not `pub`, make it `pub` (it is the
  existing helper `run_file_corpus` calls).

- [ ] **Step 4: Verify.** `cargo test -p leanr_elab --test oracle_file`
  → PASS (216 checked + 93 pending).

- [ ] **Step 5: Commit.**
  `git add tests/fixtures/elab crates/leanr_elab/tests/oracle_file.rs crates/leanr_elab/tests/support`
  `git commit -m "M4c-2c-ii P1 Task 1: 93 oracle-probed auto-bound/option rows (staged)"`

---

### Task 2: `leanr_meta` — mvars in a `mk_binding` telescope

**Files:**
- Create: `crates/leanr_meta/src/abstract_vars.rs`
- Modify: `crates/leanr_meta/src/lib.rs` (add `mod abstract_vars;`)
- Modify: `crates/leanr_meta/src/metactx.rs` (field at the `MetaCtx` struct `:43-110`, init in `new` `~:437`, `mk_binding` `:1141-1225`)
- Modify: `crates/leanr_meta/src/mk_binding.rs` (`abstract_range` `:317-330`, `abstract_range_aux` `:352-365`, `elim_app` None arm `:612-615`)

**Interfaces:**
- Consumes: nothing new.
- Produces: `MetaCtx::mk_forall(&[ExprId], ExprId)` / `mk_lambda` now
  accept unassigned `Node::MVar` entries in the telescope (oracle
  `MkBinding.mkBinding`'s else arm, `MetavarContext.lean:1339-1347`): the
  binder is `.implicit`, its type is the mvar's `decl.ty`, head-beta'd and
  abstracted over the earlier entries; its name is `decl.user_name` or a
  fresh `_leanr_mkbinding_fresh.<n>`.
  `pub(crate) fn abstract_vars(&mut self, e: ExprId, xs: &[ExprId]) -> Result<ExprId, MetaError>`.

- [ ] **Step 1: Write the failing tests** (in `metactx.rs`'s test module,
  next to `mk_binding_rejects_an_ldecl_fvar` `~:2689`). Use the existing
  helpers in that module (`with_ctx`, `crate::test_support::{app,
  fresh_fvar}`); mint mvars with the module's existing mvar helper (the
  one `mk_aux_mvar_type_wraps_a_reverted_mvar_…` in `mk_binding.rs:1810`
  uses).

```rust
#[test]
fn mk_forall_abstracts_an_mvar_entry_as_an_implicit_binder() {
    // oracle: `mkForallFVars #[?α, x] (Eq ?α x x)` with `x : ?α`, the
    // shape `theorem t : a = a` produces (MetavarContext.lean:1339-1347).
    with_ctx(|ctx| {
        let base = Some(ctx.view.store);
        let u = ctx.scratch.level_zero(base).expect("level"); // any level
        let sort = ctx.scratch.expr_sort(base, u).expect("sort");
        let alpha = fresh_mvar(ctx, sort); // the module's mvar helper
        let x = fresh_fvar(ctx, alpha, "x");
        let body = app(ctx, "Eq", &[alpha, x, x]);
        let r = ctx.mk_forall(&[alpha, x], body).expect("mvar entry accepted");
        // ∀ {_ : Sort 0} (x : #0), Eq #1 #0 #0
        let Node::Forall { binder_type, body: b1, binder_info, binder_name } = ctx.node(r) else {
            panic!("outer forall")
        };
        assert_eq!(binder_info, BinderInfo::Implicit);
        assert_eq!(binder_type, sort);
        let name = ctx.scratch.to_name(base, binder_name).to_string();
        assert!(name.starts_with("_leanr_mkbinding_fresh"), "{name}");
        let Node::Forall { binder_type: t2, body: b2, .. } = ctx.node(b1) else {
            panic!("inner forall")
        };
        assert!(matches!(ctx.node(t2), Node::BVar { .. }), "x : #0 (the abstracted mvar)");
        assert!(!ctx.data(b2).has_expr_mvar(), "every ?α occurrence abstracted");
        assert!(!ctx.data(b2).has_fvar(), "every x occurrence abstracted");
    });
}

#[test]
fn mk_forall_keeps_a_named_mvar_user_name() {
    with_ctx(|ctx| {
        // a mvar declared with user name `β` keeps it (no fresh name)
        let base = Some(ctx.view.store);
        let u = ctx.scratch.level_zero(base).expect("level");
        let sort = ctx.scratch.expr_sort(base, u).expect("sort");
        let beta = fresh_named_mvar(ctx, sort, "β"); // set decl.user_name
        let body = beta;
        let r = ctx.mk_forall(&[beta], body).expect("ok");
        let Node::Forall { binder_name, .. } = ctx.node(r) else { panic!() };
        assert_eq!(ctx.scratch.to_name(base, binder_name).to_string(), "β");
    });
}

#[test]
fn mk_forall_over_fvars_only_is_unchanged() {
    // The fvar-only path must still be the kernel's abstract_fvars: same
    // ExprId as before this task for a fixed input.
    with_ctx(|ctx| {
        let nat = ctx.nat_ty(); // or the module's Nat helper
        let x = fresh_fvar(ctx, nat, "x");
        let y = fresh_fvar(ctx, nat, "y");
        let body = app(ctx, "Eq", &[nat, x, y]);
        let r = ctx.mk_forall(&[x, y], body).expect("ok");
        let expected = {
            let b = leanr_kernel::subst::abstract_fvars(
                ctx.scratch, Some(ctx.view.store), body, &[x, y], &mut ctx.guard,
            ).unwrap();
            let base = Some(ctx.view.store);
            let nx = ctx.lctx_decl_name(x); let ny = ctx.lctx_decl_name(y);
            let inner = ctx.scratch.expr_forall(base, ny, nat, b, BinderInfo::Default).unwrap();
            ctx.scratch.expr_forall(base, nx, nat, inner, BinderInfo::Default).unwrap()
        };
        assert_eq!(r, expected);
    });
}
```

  If a helper named above (`fresh_mvar`, `fresh_named_mvar`, `nat_ty`,
  `lctx_decl_name`) does not exist in that test module, add it to
  `crate::test_support` with that exact name, built from the same calls
  the existing `mk_aux_mvar_type_wraps_a_reverted_mvar_…` test makes
  (`mctx.declare_expr` / `push_local_decl`).

- [ ] **Step 2: Run them.** `cargo test -p leanr_meta mk_forall_` →
  the first two FAIL with `mk_binding: telescope entry is not an fvar`;
  the third PASSES (it is the regression guard).

- [ ] **Step 3: `abstract_vars.rs`.** Copy `leanr_kernel::subst::
  abstract_go` (`subst.rs:768-…`, incl. its `VisitCache` keyed by
  `(ExprId, offset)` and the `RecGuard::enter` per child) into
  `crates/leanr_meta/src/abstract_vars.rs` as `fn abstract_go`, with these
  differences only:
  - the skip test is `!(d.has_fvar() || d.has_expr_mvar())`
    (`d = st.expr_data(base, e)`), at entry and per node;
  - a `Node::MVar { id }` node is matched against the `Node::MVar`
    entries of `xs` exactly like the FVar arm matches fvars (scan `xs`
    from the end; hit ⇒ `bvar(offset + n - i - 1)`), and is no longer in
    the atoms list;
  - an `xs` entry is compared by node kind: an FVar entry only matches an
    FVar node, an MVar entry only an MVar node.

  Then:

```rust
//! oracle: `Expr.abstractRange` / C++ `abstract` (`src/kernel/abstract.cpp`),
//! which abstracts free AND meta variables. The kernel's port
//! (`leanr_kernel::subst::abstract_fvars`) handles fvars only and is TCB;
//! this module is the `leanr_meta`-local twin used only when a telescope
//! contains a metavariable (`MkBinding.mkBinding` with
//! `mvarIdsToAbstract`, `MetavarContext.lean:1364`).

impl MetaCtx<'_> {
    /// `xs` all fvars ⇒ exactly the kernel's `abstract_fvars` (today's path).
    pub(crate) fn abstract_vars(&mut self, e: ExprId, xs: &[ExprId]) -> Result<ExprId, MetaError> {
        let base = Some(self.view.store);
        if xs.iter().all(|&x| matches!(self.node(x), Node::FVar { .. })) {
            return Ok(leanr_kernel::subst::abstract_fvars(self.scratch, base, e, xs, &mut self.guard)?);
        }
        Ok(abstract_go(self.scratch, base, e, 0, xs, &mut self.guard, &mut VisitCache::new())?)
    }
}
```

- [ ] **Step 4: Route the three abstraction sites through it.** In
  `mk_binding.rs`, `abstract_range` and `abstract_range_aux` call
  `self.abstract_vars(e, &xs[..i])` instead of `abstract_fvars(…)`. In
  `metactx.rs::mk_binding`, the per-binder `abstract_fvars(…,
  slice::from_ref(&fvars[i]), …)` becomes
  `self.abstract_vars(r, std::slice::from_ref(&fvars[i]))?`.

- [ ] **Step 5: `mvarIdsToAbstract`.** Add to `MetaCtx`:

```rust
    /// oracle: `MkBinding.Context.mvarIdsToAbstract` (`MetavarContext.lean:
    /// 968`, set at `:1364`): the mvars of the current top-level
    /// `mkBinding` telescope. `elimApp` leaves them in place (`:1242-1243`)
    /// so the abstraction can turn them into binders.
    pub(crate) mvar_ids_to_abstract: Vec<MVarId>,
```

  initialised `Vec::new()` in `MetaCtx::new`. In `mk_binding`, wrap the
  existing body:

```rust
        let to_abstract: Vec<MVarId> = fvars
            .iter()
            .filter_map(|&x| match self.node(x) {
                Node::MVar { id: Some(n) } => Some(MVarId(n)),
                _ => None,
            })
            .collect();
        let outer = std::mem::replace(&mut self.mvar_ids_to_abstract, to_abstract);
        let out = self.mk_binding_telescope(is_lambda, eta_reduce, fvars, body);
        self.mvar_ids_to_abstract = outer;
        out
```

  (`mk_binding_telescope` = today's body, moved verbatim.) In
  `mk_binding.rs::elim_app`, the unassigned arm becomes:

```rust
                None if self.mvar_ids_to_abstract.contains(&mid) => {
                    // oracle `:1242-1243`: `return mkAppN f (← args.mapM (visit xs))`.
                    let mut out = f;
                    for a in args {
                        let a2 = self.elim(xs, *a, cache)?;
                        out = self.scratch.expr_app(Some(self.view.store), out, a2)?;
                    }
                    return Ok(out);
                }
                None => {
                    let (out, _) = self.elim_mvar(xs, mid, args, cache)?;
                    return Ok(out);
                }
```

- [ ] **Step 6: The mvar arm.** In `mk_binding_telescope`'s binder match,
  replace the `_ => Err("telescope entry is not an fvar")` arm:

```rust
                Node::MVar { id: Some(n) } => {
                    // oracle `MetavarContext.lean:1339-1347`.
                    let decl = self.mctx.decl(MVarId(n)).ok_or_else(|| {
                        MetaError::Infer("mk_binding: telescope mvar not declared".into())
                    })?;
                    let (user_name, ty) = (decl.user_name, decl.ty);
                    let name = match user_name {
                        Some(n) => Some(n),
                        // `mkFreshBinderName` (`:977`): a macro-scoped `x`;
                        // leanr's stand-in, recognised by `name_has_macro_scopes`.
                        None => Some(self.mk_fresh_binder_name()?),
                    };
                    // `binderInfoForMVars`, default `.implicit` (`:1363`).
                    (name, ty, leanr_kernel::BinderInfo::Implicit)
                }
                _ => {
                    return Err(MetaError::Infer(
                        "mk_binding: telescope entry is neither an fvar nor an mvar".into(),
                    ))
                }
```

  and add `mk_fresh_binder_name` beside `level.rs:888`'s
  `_leanr_lvl_fresh` generator, same idiom, prefix
  `_leanr_mkbinding_fresh`, its own counter field. The head-beta and
  `abstract_range(fvars, i, ty)` lines that follow already apply to every
  arm. `leanr_elab`'s `name_has_macro_scopes` (`unassigned.rs:166`)
  recognises only `_leanr_elab_*`; widen its prefix test to
  `s.starts_with("_leanr_")` and update its doc line, so the new names
  count as macro-scoped too.

- [ ] **Step 7: Run.** `cargo test -p leanr_meta` → all PASS (incl. the
  three new tests); `cargo test -p leanr_elab` → all PASS (no behaviour
  change for fvar-only telescopes).

- [ ] **Step 8: Mutations (run each, confirm a failure, revert):**
  (a) `.Default` instead of `.Implicit` in the mvar arm ⇒
  `mk_forall_abstracts_an_mvar_entry_as_an_implicit_binder`;
  (b) drop the `mvar_ids_to_abstract` arm in `elim_app` ⇒ the same test
  (the body's `?α` is eliminated into an aux mvar, so `has_expr_mvar`
  stays true);
  (c) make `abstract_vars` always take the new traversal ⇒ still passes
  (equivalence) — record as "not a mutation: equivalent", fine;
  (d) ignore `user_name` ⇒ `mk_forall_keeps_a_named_mvar_user_name`.

- [ ] **Step 9: Commit** (`cargo fmt --all`, clippy first).
  `git commit -m "leanr_meta: mvar entries in mk_binding telescopes (MkBinding mvar arm + mvarIdsToAbstract)"`
  with the mutation lines in the body.

---

### Task 3: The auto-bound core in `leanr_elab`

**Files:**
- Create: `crates/leanr_elab/src/auto_bound.rs`; `mod auto_bound;` in `lib.rs`
- Modify: `crates/leanr_elab/src/elab.rs` (`TermElabM` fields + `new` `:228`)
- Modify: `crates/leanr_elab/src/error.rs` (variant + `is_oracle_error` `:387`)
- Modify: `crates/leanr_elab/src/app/head.rs:405-409`, `app/mod.rs:192-194`

**Interfaces:**
- Produces (all in `auto_bound.rs`):
  - `pub(crate) struct AutoBoundCtx { pub enabled: bool, pub bound: Vec<ExprId> }`
  - `#[derive(Clone, Copy, Debug)] pub(crate) struct ElabOptions { pub auto_implicit: bool, pub relaxed_auto_implicit: bool }` with `Default` = both `true`
  - `pub(crate) fn check_valid_auto_bound_implicit_name(comps: &[String], allowed: bool, relaxed: bool) -> bool`
  - `pub(crate) fn is_valid_auto_bound_level_name(s: &str, relaxed: bool) -> bool` (used in Task 5)
  - `pub(crate) fn unknown_ident(elab: &TermElabM, comps: &[String], raw: &str) -> ElabError`
  - `impl TermElabM { pub(crate) fn with_auto_bound_implicit<R>(&mut self, k: impl FnMut(&mut Self) -> Result<R, ElabError>) -> Result<R, ElabError>; pub(crate) fn without_auto_bound_implicit<R>(&mut self, k: impl FnOnce(&mut Self) -> Result<R, ElabError>) -> Result<R, ElabError>; pub(crate) fn with_auto_bound_forbidden<R>(&mut self, names: &[NameId], k: impl FnOnce(&mut Self) -> Result<R, ElabError>) -> Result<R, ElabError> }`
  - `TermElabM` fields: `pub(crate) auto_bound: Option<AutoBoundCtx>`, `pub(crate) auto_bound_forbidden: Vec<NameId>`, `pub(crate) options: ElabOptions`
  - `ElabError::AutoBoundImplicitLocal(String)` (the atomic component)

- [ ] **Step 1: Failing unit tests** (in `auto_bound.rs`'s `#[cfg(test)]`
  module; build an elaborator the way `command/levels.rs`'s test does:
  `Environment::default()` is too empty for idents — use the existing
  `crate::test_support`/`tests/support` Elab0 helper that
  `binder_smoke.rs` uses, `with_elab0(|elab, kinds| …)`, and parse a type
  with that file's `parse_term` helper):

```rust
#[test]
fn name_checks_follow_auto_bound_lean() {
    // AutoBound.lean: checkValidAutoBoundImplicitName / isValidAutoBoundSuffix
    let c = |s: &str| vec![s.to_string()];
    assert!(check_valid_auto_bound_implicit_name(&c("α"), true, true));
    assert!(check_valid_auto_bound_implicit_name(&c("foo"), true, true));
    assert!(!check_valid_auto_bound_implicit_name(&c("foo"), true, false));
    for ok in ["α₁", "X12", "β'", "α_1", "αᵢ"] {
        assert!(check_valid_auto_bound_implicit_name(&c(ok), true, false), "{ok}");
    }
    assert!(!check_valid_auto_bound_implicit_name(&c("α"), false, true));
    assert!(!check_valid_auto_bound_implicit_name(&["A".into(), "b".into()], true, true));
    assert!(!check_valid_auto_bound_implicit_name(&c(""), true, true));
    // isValidAutoBoundLevelName: strict = lowercase head + valid suffix
    assert!(is_valid_auto_bound_level_name("u", false));
    assert!(is_valid_auto_bound_level_name("u1", false));
    assert!(!is_valid_auto_bound_level_name("U", false));
    assert!(!is_valid_auto_bound_level_name("uv", false));
    assert!(is_valid_auto_bound_level_name("uv", true));
}

#[test]
fn the_loop_binds_an_unknown_identifier_and_retries() {
    with_elab0(|elab, kinds| {
        let stx = parse_term(kinds, "List α");
        let (ty, autos) = elab
            .with_auto_bound_implicit(|elab| {
                let t = crate::builtin::binder::elab_type(elab, &stx, kinds)?;
                Ok((t, elab.auto_bound.as_ref().unwrap().bound.clone()))
            })
            .expect("auto-bound");
        assert_eq!(autos.len(), 1, "exactly one auto: α");
        let d = elab.mctx.local_decl_of(autos[0]).expect("declared"); // fvar's decl
        assert_eq!(d.binder_info, BinderInfo::Implicit);
        assert!(elab.mctx.data(ty).has_fvar(), "List α mentions the auto");
    });
}

#[test]
fn without_a_context_it_is_a_plain_unknown_identifier() {
    with_elab0(|elab, kinds| {
        let stx = parse_term(kinds, "List α");
        let e = crate::builtin::binder::elab_type(elab, &stx, kinds).unwrap_err();
        assert!(matches!(e, ElabError::UnknownIdent(ref s) if s == "α"), "{e:?}");
    });
}

#[test]
fn a_disabled_context_reports_unknown_identifier() {
    with_elab0(|elab, kinds| {
        elab.options.auto_implicit = false;
        let stx = parse_term(kinds, "List α");
        let e = elab
            .with_auto_bound_implicit(|elab| crate::builtin::binder::elab_type(elab, &stx, kinds))
            .unwrap_err();
        assert!(matches!(e, ElabError::UnknownIdent(ref s) if s == "α"), "{e:?}");
    });
}

#[test]
fn a_forbidden_name_is_not_auto_bound() {
    with_elab0(|elab, kinds| {
        let f = crate::command::header::intern_atomic(elab, "self_name").unwrap();
        let stx = parse_term(kinds, "List self_name");
        let e = elab
            .with_auto_bound_forbidden(&[f], |elab| {
                elab.with_auto_bound_implicit(|elab| crate::builtin::binder::elab_type(elab, &stx, kinds))
            })
            .unwrap_err();
        assert!(matches!(e, ElabError::UnknownIdent(ref s) if s == "self_name"), "{e:?}");
    });
}

#[test]
fn the_internal_error_escapes_observing() {
    // oracle `Term.observing` catches `.error` and postpone only.
    with_elab0(|elab, _| {
        let r = elab.observing(|_| Err(ElabError::AutoBoundImplicitLocal("x".into())));
        assert!(matches!(r, Err(ElabError::AutoBoundImplicitLocal(_))), "{r:?}");
        assert!(!ElabError::AutoBoundImplicitLocal("x".into()).is_oracle_error());
    });
}
```

  If `with_elab0` / `parse_term` / `local_decl_of` are not reachable from
  `src/` unit tests under those names, add thin `#[cfg(test)]` wrappers
  with those names in `crate::test_support` over the existing equivalents
  (`binder_smoke.rs` builds the same Elab0 elaborator; `MetaCtx` exposes
  the lctx lookup the binder module already uses).

- [ ] **Step 2: Run.** `cargo test -p leanr_elab auto_bound::` → FAIL
  (module/items missing).

- [ ] **Step 3: Implement `auto_bound.rs`.**

```rust
//! Auto-bound implicits: oracle `Elab/AutoBound.lean` and
//! `withAutoBoundImplicit` / `addAutoBoundImplicits`
//! (`Elab/Term/TermElabM.lean:1959-2090`).

/// oracle: `AutoBoundImplicitContext` (`AutoBound.lean`).
#[derive(Clone, Debug)]
pub(crate) struct AutoBoundCtx {
    /// `autoImplicitEnabled`: the `autoImplicit` option at entry.
    pub enabled: bool,
    /// `boundVariables`: the auto-bound fvars, in discovery order.
    pub bound: Vec<ExprId>,
}

/// The two options this slice ports (`AutoBound.lean`'s
/// `register_builtin_option`s, both default `true`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) struct ElabOptions {
    pub auto_implicit: bool,
    pub relaxed_auto_implicit: bool,
}

impl Default for ElabOptions {
    fn default() -> Self {
        ElabOptions { auto_implicit: true, relaxed_auto_implicit: true }
    }
}

/// oracle `isSubScriptAlnum` (`Init/Meta`): subscript digits/letters.
fn is_sub_script_alnum(c: char) -> bool {
    ('\u{2080}'..='\u{2089}').contains(&c)   // ₀-₉
        || ('\u{2090}'..='\u{209c}').contains(&c) // ₐ-ₜ
        || ('\u{1d62}'..='\u{1d6a}').contains(&c) // ᵢ-ᵪ
        || c == '\u{2c7c}' // ⱼ
}

/// `isValidAutoBoundSuffix`: every char after the first is a digit, a
/// subscript, `_` or `'`.
fn is_valid_suffix(s: &str) -> bool {
    s.chars().skip(1).all(|c| c.is_ascii_digit() || is_sub_script_alnum(c) || c == '_' || c == '\'')
}

/// `checkValidAutoBoundImplicitName` (`AutoBound.lean`), `.ok true` only;
/// its `.error` (note) arm is `false` here — the note is not modelled
/// (spec Amendment 1, item 3).
pub(crate) fn check_valid_auto_bound_implicit_name(comps: &[String], allowed: bool, relaxed: bool) -> bool {
    match comps {
        [s] if !s.is_empty() && !s.starts_with("_leanr_") => allowed && (relaxed || is_valid_suffix(s)),
        _ => false,
    }
}

/// `isValidAutoBoundLevelName` (`AutoBound.lean`).
pub(crate) fn is_valid_auto_bound_level_name(s: &str, relaxed: bool) -> bool {
    !s.is_empty()
        && (relaxed || (s.chars().next().is_some_and(char::is_lowercase) && is_valid_suffix(s)))
}

/// oracle: `throwUnknownIdWithSuggestions` (`App.lean:1960-1975`).
pub(crate) fn unknown_ident(elab: &TermElabM, comps: &[String], raw: &str) -> ElabError {
    let forbidden = match comps {
        [s] => elab.auto_bound_forbidden.iter().any(|&n| elab.name_str(n) == *s),
        _ => false,
    };
    if !forbidden && elab.auto_bound.is_some() {
        let o = elab.options;
        if check_valid_auto_bound_implicit_name(comps, o.auto_implicit, o.relaxed_auto_implicit) {
            return ElabError::AutoBoundImplicitLocal(comps[0].clone());
        }
    }
    ElabError::UnknownIdent(raw.to_string())
}

impl TermElabM<'_> {
    /// oracle: `withAutoBoundImplicit` (`TermElabM.lean:1959-1980`).
    /// Iterative: one pass per discovered name (spec Review Focus 2).
    pub(crate) fn with_auto_bound_implicit<R>(
        &mut self,
        mut k: impl FnMut(&mut Self) -> Result<R, ElabError>,
    ) -> Result<R, ElabError> {
        let outer = self.auto_bound.take();
        let enabled = self.options.auto_implicit;
        self.auto_bound = Some(AutoBoundCtx { enabled, bound: Vec::new() });
        let out = if !enabled {
            k(self)
        } else {
            loop {
                // `saveState`: Term.State (incl. `levelNames`) + the lctx.
                let saved = self.save_term_state();
                let level_names = self.level_names.clone();
                let lctx = self.mctx.lctx_checkpoint();
                match k(self) {
                    Err(ElabError::AutoBoundImplicitLocal(n)) => {
                        // `s.restore (restoreInfo := true)`
                        self.restore_term_state(saved);
                        self.level_names = level_names;
                        self.mctx.lctx_restore(lctx);
                        // `withLocalDecl n .implicit (← mkFreshTypeMVar)`
                        let ty = self.mk_fresh_type_mvar()?;
                        let name = crate::command::header::intern_atomic(self, &n)?;
                        let x = self.mctx.push_local_decl(Some(name), ty, BinderInfo::Implicit)?;
                        self.auto_bound.as_mut().expect("set above").bound.push(x);
                    }
                    other => break other,
                }
            }
        };
        self.auto_bound = outer;
        out
    }

    /// oracle: `withoutAutoBoundImplicit` (`:1982-1983`).
    pub(crate) fn without_auto_bound_implicit<R>(
        &mut self,
        k: impl FnOnce(&mut Self) -> Result<R, ElabError>,
    ) -> Result<R, ElabError> {
        let outer = self.auto_bound.take();
        let out = k(self);
        self.auto_bound = outer;
        out
    }

    /// oracle: `withAutoBoundImplicitForbiddenPred` (`:1985-1986`).
    pub(crate) fn with_auto_bound_forbidden<R>(
        &mut self,
        names: &[NameId],
        k: impl FnOnce(&mut Self) -> Result<R, ElabError>,
    ) -> Result<R, ElabError> {
        let n = self.auto_bound_forbidden.len();
        self.auto_bound_forbidden.extend_from_slice(names);
        let out = k(self);
        self.auto_bound_forbidden.truncate(n);
        out
    }
}
```

  Notes for the implementer:
  - The loop's local decls live in the lctx the CALLER brackets
    (`elab_header`'s `lctx_checkpoint`/`lctx_restore`); the per-attempt
    checkpoint is taken AFTER the previously pushed autos, so a restore
    keeps them. That is why `bound` survives the restore.
  - `crate::command::header::intern_atomic` is `pub(super)`; make it
    `pub(crate)`.
  - `name_str(NameId) -> String`: use the existing render
    (`self.mctx.store().to_name(Some(self.view.store), Some(n)).to_string()`);
    add the helper on `TermElabM` if it does not exist.
  - `save_term_state`'s doc (`synthetic/state.rs:302-345`) says
    `level_names` is never touched below `f`; append: "The auto-bound
    retry loop (`auto_bound.rs`) is the exception: it snapshots
    `level_names` itself, as the oracle's `Term.SavedState` does."

- [ ] **Step 4: Wire the throw sites and the error.** `error.rs`: add

```rust
    /// oracle: the internal `autoBoundImplicit` exception
    /// (`Exception.lean:20,31-37`): caught only by `with_auto_bound_implicit`.
    AutoBoundImplicitLocal(String),
```

  add `| ElabError::AutoBoundImplicitLocal(_)` to `is_oracle_error`'s
  exclusion list (beside `Postpone`; doc: "internal, like Postpone: every
  generic catch rethrows it — spec Amendment 1 item 4"), and
  `oracle_first_line` returns `None` for it. In `app/head.rs:405-409`:

```rust
        if cands.is_empty() {
            // `elabAppFnId`'s `throwUnknownIdWithSuggestions` (`App.lean:1957-1975`).
            return Err(crate::auto_bound::unknown_ident(elab, &comps, raw));
        }
```

  and in `app/mod.rs:192-194` the same, with
  `comps = head::ident_components(f)?`. Add the three fields to
  `TermElabM` and its `new` (`auto_bound: None, auto_bound_forbidden:
  Vec::new(), options: ElabOptions::default()`).

- [ ] **Step 5: Run.** `cargo test -p leanr_elab` → all PASS (the new
  unit tests; nothing calls the loop yet, so the corpora are unchanged).

- [ ] **Step 6: Mutations:** (a) drop the `AutoBoundImplicitLocal`
  exclusion from `is_oracle_error` ⇒ `the_internal_error_escapes_observing`;
  (b) skip `lctx_restore` in the loop ⇒
  `the_loop_binds_an_unknown_identifier_and_retries` (the failed attempt's
  locals leak; record which assertion fails — if none, add an assertion
  that `elab.mctx.lctx_checkpoint()` after the loop equals the entry
  checkpoint + 1 and re-run); (c) ignore `auto_bound_forbidden` ⇒
  `a_forbidden_name_is_not_auto_bound`; (d) use `relaxed` for `allowed` ⇒
  `name_checks_follow_auto_bound_lean`.

- [ ] **Step 7: Commit.** `git commit -m "M4c-2c-ii P1 Task 3: withAutoBoundImplicit retry loop + unknown-id throw sites"`.

---

### Task 4: `addAutoBoundImplicits` and the header/axiom wiring

**Files:**
- Modify: `crates/leanr_elab/src/auto_bound.rs` (add `add_auto_bound_implicits`)
- Modify: `crates/leanr_elab/src/command/header.rs:263-338`, `command/axiom.rs:26-60`
- Modify: `crates/leanr_elab/tests/oracle_decl.rs:57-71,110-115`; `oracle_file.rs` (`PENDING`)

**Interfaces:**
- Consumes: Task 2's `mk_forall` over mvars; Task 3's loop, fields, `unknown_ident`.
- Produces: `pub(crate) fn add_auto_bound_implicits(&mut self, xs: &[ExprId]) -> Result<Vec<ExprId>, ElabError>` on `TermElabM`; `ElabError::AutoImplicitDependsOnExplicit { auto: ExprId, x: ExprId }`.

- [ ] **Step 1: Ungate.** Delete `"auto/ident"`, `"auto/mvar"`,
  `"auto/neg"`, `"auto/catch"`, `"auto/with"` from `PENDING`. Replace the
  three seam tests in `oracle_decl.rs`:

```rust
#[test]
fn header_unknown_ident_is_auto_bound() {
    // probe: `def ab (a : α) : α := a` admits `ab.{u_1}`.
    assert!(decl_result("def ab (a : α) : α := a").is_ok());
    assert!(decl_result("axiom aa (a : α) : α").is_ok());
}
```

  (keep `header_unknown_universe_is_the_auto_bound_seam` for now — Task 5
  replaces it).

- [ ] **Step 2: Run.** `cargo test -p leanr_elab --test oracle_file
  --test oracle_decl` → FAIL (header still seams).

- [ ] **Step 3: `add_auto_bound_implicits`** in `auto_bound.rs`:

```rust
    /// oracle: `addAutoBoundImplicits xs none` (`TermElabM.lean:2071-2090`)
    /// with `collectUnassignedMVars` (`:1993-2016`). Returns `autos ++ xs`.
    pub(crate) fn add_auto_bound_implicits(&mut self, xs: &[ExprId]) -> Result<Vec<ExprId>, ElabError> {
        let todo = self.auto_bound.as_ref().map(|c| c.bound.clone()).unwrap_or_default();
        let mut autos: Vec<ExprId> = Vec::new();
        for auto in todo {
            let ty = self.mctx.infer_type(auto)?;
            self.collect_unassigned_mvars(ty, &mut autos)?;
            autos.push(auto);
        }
        for &auto in &autos {
            if !matches!(self.mctx.node(auto), Node::FVar { .. }) {
                continue;
            }
            for &x in xs {
                if self.local_decl_depends_on_fvar(auto, x)? {
                    return Err(ElabError::AutoImplicitDependsOnExplicit { auto, x });
                }
            }
        }
        autos.extend_from_slice(xs);
        Ok(autos)
    }

    /// `collectUnassignedMVars type init` (`:1993-2016`): dependency-first,
    /// each mvar once, skipping assigned ones and ones already in `result`.
    fn collect_unassigned_mvars(&mut self, ty: ExprId, result: &mut Vec<ExprId>) -> Result<(), ElabError> {
        let mut todo: Vec<MVarId> = self.get_mvars(ty)?;
        let mut visited: Vec<MVarId> = Vec::new();
        while let Some(m) = (!todo.is_empty()).then(|| todo.remove(0)) {
            visited.push(m);
            let e = self.mk_mvar_expr(m)?; // the `Expr.mvar m` node
            if self.mctx.mctx().is_assigned(m) || result.contains(&e) {
                continue;
            }
            let mty = self.mctx.mctx().decl(m).expect("declared").ty;
            let fresh: Vec<MVarId> = self.get_mvars(mty)?.into_iter().filter(|n| !visited.contains(n)).collect();
            if fresh.is_empty() {
                result.push(e);
            } else {
                // `go (mvarIdsNew.toList ++ mvarId :: mvarIds)`
                let mut next = fresh;
                next.push(m);
                next.extend(todo);
                todo = next;
            }
        }
        Ok(())
    }
```

  Notes: the oracle's `visited` is pushed BEFORE the assigned/contained
  checks and the new-mvar filter reads it — keep that order. `get_mvars`
  is `unassigned.rs:22` (instantiates, so assigned mvars are followed).
  `mk_mvar_expr` = the existing `store_mut().expr_mvar(…)` call
  `mk_fresh_expr_mvar` uses; add it if absent. `local_decl_depends_on_fvar`:
  instantiate the auto's decl type and test `collect_fvars` for `x`
  (`crate::app::elim_info::collect_fvars`); this approximates the oracle's
  `localDeclDependsOn` (which also follows mvar lctxs) and is reachable
  only by the unit test below (spec Amendment 1).
  `AutoImplicitDependsOnExplicit` renders ``invalid auto implicit argument
  `{auto}`, it depends on explicitly provided argument `{x}` `` via the
  existing fvar-name renderer `oracle_first_line` uses for
  `InvalidExplicitUniversesForLocal`.

- [ ] **Step 4: Header wiring.** `header.rs`: delete
  `unknown_ident_to_auto_bound_seam` and its doc; `elab_header` becomes:

```rust
/// oracle: `elabHeaders` (`MutualDef.lean:213`, `:257-277`):
/// `withAutoBoundImplicitForbiddenPred` (the views' short names) →
/// `withAutoBoundImplicit` → `withLevelNames`.
pub(super) fn elab_header(
    elab: &mut TermElabM,
    view: &DefView,
    id: &DeclId,
    kinds: &KindInterner,
) -> Result<Header, ElabError> {
    elab.with_auto_bound_forbidden(&[id.short_name], |elab| {
        let cp = elab.mctx.lctx_checkpoint();
        let out = elab.with_auto_bound_implicit(|elab| {
            elab.with_level_names(id.level_names.clone(), |elab| header_in_scope(elab, view, kinds))
        });
        elab.mctx.lctx_restore(cp);
        out
    })
}
```

  `with_level_names` restores the OUTER names on exit (also on `Err`,
  like the oracle's `try … finally`), while the header must RETURN the
  post-header names: `header_in_scope` copies `elab.level_names` into
  `Header.level_names` before returning, so the two compose. It also means
  that on THIS path every retry already starts from `id.level_names`; the
  loop's own `level_names` snapshot matters only where no
  `with_level_names` sits inside the loop (P2's `runTermElabM`). In `header_in_scope`, after
  `synthesize_synthetic_mvars_no_postponing`:

```rust
    // `addAutoBoundImplicits xs` (`:276`), then `mkForallFVars' xs type`
    // (`:277`; its binder-name inference is unobservable — spec Amendment 1).
    let xs = elab.add_auto_bound_implicits(&xs)?;
    let ty = elab.mctx.mk_forall(&xs, ty)?;
```

  and `num_params: xs.len()` now counts autos (the body re-opens them via
  `forallBoundedTelescope`, `def.rs:307-313`). The oracle's
  `withAutoBoundImplicit` order is `withDeclName ∘ withAutoBoundImplicit ∘
  withLevelNames`; the forbidden predicate wraps all of `elabHeaders`.

- [ ] **Step 5: Axiom wiring.** `axiom.rs` (`Declaration.lean:109-116`):
  wrap the existing closure body as
  `elab.with_auto_bound_forbidden(&[id.short_name], |elab| { let cp = …;
  let out = elab.with_auto_bound_implicit(|elab| elab.with_level_names(id.level_names.clone(), |elab| { …binders, type, synth…; let xs = elab.add_auto_bound_implicits(&xs)?; …rest unchanged… })); elab.mctx.lctx_restore(cp); out })`,
  keeping the `used_vars` / `level_mvar_to_param` tail inside. Delete the
  `.map_err(unknown_ident_to_auto_bound_seam)` and the import.
  `fix_level_params(…, &scope, &id.level_names)` stays: the axiom sorts
  against `expandDeclId`'s names (`auto/levelAxiomOrder` ⇒ `[u, v]`).
  NOTE: `level_mvar_to_param` must run inside `with_level_names` so the
  auto universe names (Task 5) are seen — it already is.

- [ ] **Step 6: Depends-on-explicit unit test** (`auto_bound.rs` tests):

```rust
#[test]
fn an_auto_depending_on_an_explicit_binder_is_rejected() {
    // Unreachable from source (spec Amendment 1); constructed directly.
    with_elab0(|elab, _| {
        let nat = elab.nat_const();
        let x = elab.mctx.push_local_decl(None, nat, BinderInfo::Default).unwrap();
        let ty = elab.mk_app_const("Eq", &[nat, x, x]); // Eq Nat x x
        let a = elab.mctx.push_local_decl(None, ty, BinderInfo::Implicit).unwrap();
        elab.auto_bound = Some(AutoBoundCtx { enabled: true, bound: vec![a] });
        let e = elab.add_auto_bound_implicits(&[x]).unwrap_err();
        assert!(matches!(e, ElabError::AutoImplicitDependsOnExplicit { .. }), "{e:?}");
        assert!(e.oracle_first_line().unwrap().starts_with("invalid auto implicit argument `"));
    });
}
```

  (`nat_const` / `mk_app_const`: add `#[cfg(test)]` helpers if absent.)

- [ ] **Step 7: Run.** `cargo test -p leanr_elab` → PASS, including every
  `auto/ident|mvar|neg|catch|with` row. If a row fails, diff against
  `target/m4c2ciiprobe/expected.txt` (`python3 target/m4c2ciiprobe/show.py
  tests/fixtures/elab/file-queries.jsonl | grep -A3 <id>`) before
  touching code; probe the oracle on a variant before calling it a leanr
  bug.

- [ ] **Step 8: Mutations:** (a) `autos.push(auto)` before
  `collect_unassigned_mvars` ⇒ `auto/mvarThm` (binder order flips);
  (b) skip `collect_unassigned_mvars` ⇒ `auto/mvarTwo` (unassigned mvar
  error); (c) drop `with_auto_bound_forbidden` in `elab_header` ⇒
  `auto/negForbidden`; (d) drop it in `elab_axiom` ⇒
  `auto/negForbiddenAxiom`; (e) reverse `bound` order ⇒
  `auto/identTwoOrder`; (f) `num_params: xs_before.len()` ⇒
  `auto/identDef` (body telescope mismatch); (g) remove the
  `is_oracle_error` exclusion again ⇒ `auto/catchOverload`.

- [ ] **Step 9: Commit.** `git commit -m "M4c-2c-ii P1 Task 4: addAutoBoundImplicits + def/theorem/axiom header wiring"`.

---

### Task 5: Universe-name auto-bound

**Files:**
- Modify: `crates/leanr_elab/src/builtin/sort.rs:200-216`
- Modify: `crates/leanr_elab/src/error.rs` (`UnknownUniverseLevel`; the `UnknownIdent` comment at `:536-540`)
- Modify: `crates/leanr_elab/tests/oracle_decl.rs:67-72`; `oracle_file.rs` (`PENDING`)

**Interfaces:**
- Consumes: `is_valid_auto_bound_level_name` (Task 3), `auto_bound`, `options`.
- Produces: `ElabError::UnknownUniverseLevel(String)`.

- [ ] **Step 1: Ungate + test.** Delete `"auto/level"` from `PENDING`.
  Replace `header_unknown_universe_is_the_auto_bound_seam` with:

```rust
#[test]
fn header_unknown_universe_is_auto_bound() {
    // probe: `def uuh (α : Sort w) : Sort w := α` admits `uuh.{w}`.
    assert!(decl_result("def uuh (α : Sort w) : Sort w := α").is_ok());
    match decl_result("def uub : Nat := (fun (_ : Sort w) => Nat.zero) Nat") {
        Err(e) => assert_eq!(e.oracle_first_line().as_deref(), Some("unknown universe level `w`")),
        Ok(ns) => panic!("body universe must not auto-bind: {ns:?}"),
    }
}
```

- [ ] **Step 2: Run** `cargo test -p leanr_elab --test oracle_file --test oracle_decl` → FAIL.

- [ ] **Step 3: Implement** (`sort.rs`, the `ident` arm; oracle
  `Level.lean:79-84`):

```rust
            if elab.level_names.contains(&name_id) {
                /* unchanged: build the level param */
            } else if elab.auto_bound.as_ref().is_some_and(|c| c.enabled)
                && parts.len() == 1
                && crate::auto_bound::is_valid_auto_bound_level_name(
                    parts[0],
                    elab.options.relaxed_auto_implicit,
                )
            {
                // `modify fun s => { s with levelNames := paramName :: s.levelNames }`
                elab.level_names.insert(0, name_id);
                Ok(/* the same level_param construction as the first branch */)
            } else {
                Err(ElabError::UnknownUniverseLevel(raw.to_string()))
            }
```

  (factor the `level_param(Some(base), Some(name_id))` call into a local
  closure used by both branches). `error.rs`: add
  `UnknownUniverseLevel(String)` with first line
  ``unknown universe level `{s}` ``, and rewrite the `UnknownIdent`
  comment (`:536-540`): the universe case is now its own variant.
  `elab.auto_bound.is_some_and(enabled)` is the oracle's
  `(← read).autoBoundImplicit` (`TermElabM.lean:818`).

- [ ] **Step 4: Run.** `cargo test -p leanr_elab` → PASS incl. all
  `auto/level*` rows (19).

- [ ] **Step 5: Mutations:** (a) drop `self.level_names = level_names` in
  the Task 3 loop ⇒ EQUIVALENT on every P1 path (Task 4 Step 4 note:
  `with_level_names` inside the loop already rewinds); record it as
  "killed in P2 by a `variable (α : Sort u) (x : β)` row". Instead run:
  (a') move `with_level_names` OUTSIDE `with_auto_bound_implicit` in
  `elab_header` AND drop the loop's restore ⇒ `auto/levelThenIdent`
  (`u` pushed twice); (b) `push` instead of `insert(0, …)` ⇒ `auto/levelTwo`
  (`[u, v]`); (c) ignore `relaxed` ⇒ (fails at Task 7: note it in the
  commit as "killed by opt/strictLevelUpper once ungated");
  (d) pass the post-header names to the axiom's `fix_level_params` ⇒
  `auto/levelAxiomOrder`.

- [ ] **Step 6: Commit.** `git commit -m "M4c-2c-ii P1 Task 5: universe-name auto-bound (Level.lean ident arm)"`.

---

### Task 6: `throwInvalidNamedArg` (first line)

**Files:**
- Modify: `crates/leanr_elab/src/app/args.rs:115-152`
- Modify: `crates/leanr_elab/src/error.rs` (`InvalidNamedArg`)
- Modify: `oracle_file.rs` (`PENDING`)

**Interfaces:**
- Produces: `ElabError::InvalidNamedArg { name: String, func: Option<String> }`.

- [ ] **Step 1: Ungate + unit test.** Delete `"auto/namedArg"` from
  `PENDING`. Add to `crates/leanr_elab/tests/app_smoke.rs` (it has an
  Elab0 term helper):

```rust
#[test]
fn an_unmatched_named_argument_is_invalid_argument_name() {
    // oracle App.lean:400-403 (probe: `pick (zz := Nat.zero) Nat.zero Nat.zero`)
    let e = elab_err("pick (zz := Nat.zero)");
    assert_eq!(
        e.oracle_first_line().as_deref(),
        Some("Invalid argument name `zz` for function `pick`")
    );
}
```

  Probe this term before relying on it: add
  `("named/invalid", "def nai : Nat := pick (zz := Nat.zero)")` to the
  scratch `target/m4c2ciiprobe/rows.py`, run the probe, and confirm the
  first line; if it differs, use the oracle's line in the assertion.

- [ ] **Step 2: Run** → FAIL (leanr says "Function expected at").

- [ ] **Step 3: Implement.** In `args.rs`, after the `coerce_to_function`
  match and before `FunctionExpected`:

```rust
    // `synthesizePendingAndNormalizeFunType` (`App.lean:380-403`): a
    // leftover named argument is reported before "Function expected".
    // The deprecated-argument linter branch (`:386-399`) is not ported
    // (no `Elab0` constant carries `deprecated_arg`).
    if let Some(na) = app.st.named_args.first() {
        let head = app.elab.mctx.get_app_fn(app.st.f);
        let func = match app.elab.mctx.node(head) {
            Node::Const { name, .. } => Some(app.elab.name_str(name)),
            _ => None,
        };
        return Err(ElabError::InvalidNamedArg { name: na.name.clone(), func });
    }
```

  Rendering: ``Invalid argument name `{name}` for function `{f}` `` when
  `func` is `Some`, else ``Invalid argument name `{name}` for function``
  (`App.lean:51-52`; `.ofConstName` prints the plain name for these).
  Update the comment above (`:137-140`) — `throwInvalidNamedArg` is now
  ported.

- [ ] **Step 4: Run** `cargo test -p leanr_elab` → PASS incl. the three
  `auto/namedArg*` rows. `auto/namedArgMvar` is the row pinning that the
  mvar binder's name is inaccessible (spec Amendment 1, item 1).

- [ ] **Step 5: Mutations:** (a) give the Task 2 mvar arm the name `α`
  (hard-code `intern("α")` in place of the fresh name, temporarily) ⇒
  `auto/namedArgMvar` (leanr then accepts the named arg); (b) report the
  LAST named arg ⇒ none (single-arg rows) — record "equivalent on the
  corpus"; (c) drop the `func` suffix ⇒ the smoke test.

- [ ] **Step 6: Commit.** `git commit -m "M4c-2c-ii P1 Task 6: throwInvalidNamedArg first line"`.

---

### Task 7: `set_option autoImplicit` / `relaxedAutoImplicit`

**Files:**
- Modify: `crates/leanr_elab/src/command/scope.rs` (`Scope` `:26-61`, `root`, a new `elab_set_option`)
- Modify: `crates/leanr_elab/src/command/mod.rs:184-194` (dispatch), `:260` (seed)
- Modify: `crates/leanr_elab/src/error.rs` (`SetOptionTypeMismatch`)
- Modify: `crates/leanr_elab/tests/oracle_file.rs` (`PENDING` → empty; new seam test)

**Interfaces:**
- Consumes: `ElabOptions` (Task 3).
- Produces: `Scope.options: ElabOptions`; `CommandElab::elab_set_option(&mut self, cmd: &SyntaxNode, kinds: &KindInterner) -> Result<(), ElabError>`.

- [ ] **Step 1: Ungate + tests.** Delete `"opt/"` from `PENDING` (it is
  now empty; keep the constant with an empty slice and its doc updated to
  "P1 complete"). Add to `oracle_file.rs`:

```rust
#[test]
fn set_option_other_names_are_later_m4_seams() {
    let (at, m) = stop_seam("set_option pp.all true");
    assert_eq!(at, 0);
    assert!(m.contains("set_option") && m.ends_with(" — later M4"), "{m}");
}
```

- [ ] **Step 2: Run** → FAIL (`set_option` is a command seam today).

- [ ] **Step 3: Implement.** `Scope` gains
  `pub options: crate::auto_bound::ElabOptions` (doc: "oracle
  `Scope.opts`, restricted to the two options M4c-2c-ii ports; cloned into
  nested scopes, dropped at `end`"), `root()` sets
  `ElabOptions::default()`. Dispatch arm in `mod.rs`:
  `"Lean.Parser.Command.set_option" => none(self.elab_set_option(cmd, kinds)),`.
  In `scope.rs`:

```rust
    /// oracle: `elabSetOption` (`BuiltinCommand.lean:516`,
    /// `SetOption.lean:58`), for `autoImplicit` / `relaxedAutoImplicit`.
    pub(crate) fn elab_set_option(&mut self, cmd: &SyntaxNode, _kinds: &KindInterner) -> Result<(), ElabError> {
        let ch = non_trivia_children(cmd);
        let name = ch.get(1).map(|e| e.text().trim().to_string()).unwrap_or_default();
        let val = ch.get(2).map(|e| e.text().trim().to_string()).unwrap_or_default();
        let field: fn(&mut ElabOptions) -> &mut bool = match name.as_str() {
            "autoImplicit" => |o| &mut o.auto_implicit,
            "relaxedAutoImplicit" => |o| &mut o.relaxed_auto_implicit,
            other => {
                return Err(ElabError::UnsupportedSyntax(format!(
                    "set_option `{other}` (only autoImplicit/relaxedAutoImplicit are modelled) — later M4"
                )))
            }
        };
        let b = match val.as_str() {
            "true" => true,
            "false" => false,
            // probe `opt/badValue`: a numeral (or string) for a Bool option.
            _ => return Err(ElabError::SetOptionTypeMismatch),
        };
        *field(&mut self.head_mut().options) = b;
        Ok(())
    }
```

  `SetOptionTypeMismatch` renders
  `"set_option value type mismatch: The value"`. Use the scope accessor
  the other commands use for the innermost scope (`head_mut()` or
  `scopes.last_mut()`). In `with_term_elab` (`mod.rs:260`), add
  `elab.options = head.options;` beside the `level_names` seed.
  `set_option … in` needs nothing: `elab_in` already opens and drops a
  scope around both commands (`opt/offIn`, `opt/offInScoped`).

- [ ] **Step 4: Run.** `cargo test -p leanr_elab` → PASS, all 309 file
  rows checked, `PENDING` empty.

- [ ] **Step 5: Mutations:** (a) don't seed `elab.options` ⇒ `opt/offDef`;
  (b) store options on the root scope instead of the head ⇒
  `opt/offSection`; (c) swap the two field mappings ⇒ `opt/strictBad`;
  (d) the Task 5 relaxed-ignored mutation ⇒ `opt/strictLevelUpper`.

- [ ] **Step 6: Commit.** `git commit -m "M4c-2c-ii P1 Task 7: set_option autoImplicit / relaxedAutoImplicit (scoped)"`.

---

### Task 8: Close-out

**Files:**
- Modify: `crates/leanr_elab/src/lib.rs:~234` (slice/seam docs)
- Modify: `crates/leanr_elab/src/command/vars.rs:1-20` (module doc)
- Modify: `docs/superpowers/specs/2026-10-05-m4c2c-ii-auto-bound-design.md` (§ Landed › P1)

- [ ] **Step 1: Seam sweep.** `grep -rn "M4c-2c-ii" crates/` → only the
  `variable` binder seam (`vars.rs:165-170`) and its test
  (`oracle_file.rs` `variable_seams_carry_their_slice`) remain. Update
  `lib.rs`'s seam list and `vars.rs`'s module doc: header auto-bound is
  landed; the `variable` seam and the `runTermElabM` mvar-rebuild branch
  are P2.
- [ ] **Step 2: Cite sweep.** Open every oracle `file:line` this branch
  added in comments (`git diff main --stat`, then grep the diff for
  `\.lean:[0-9]`) and fix any off-by-1-2 (standing rule: plan cites are
  unverified).
- [ ] **Step 3: § Landed › P1** in the spec: rows (309 file / unchanged
  decl), the mutation list per task, open seams (P2 `variable`;
  `setMVarUserNamesAt`, the note line, the deprecated-arg linter
  unmodelled), any surviving mutation with the reason.
- [ ] **Step 4: Full CI, blocking.**
  `mise run ci > target/ci-p1.log 2>&1; echo CI_EXIT=$?` → `CI_EXIT=0`.
- [ ] **Step 5: Commit.** `git commit -m "M4c-2c-ii P1 Task 8: close-out (seams, cites, spec § Landed)"`.
- [ ] **Step 6: Final whole-branch review** on the most capable model,
  with oracle probing allowed (the M4c-1 lesson: per-task reviews missed
  three wrong-Ok paths). Then PR → green CI → merge → delete branch
  (standing instruction).
