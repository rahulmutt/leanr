# M4c-2c-ii P2 — `variable` auto-bound + `runTermElabM` rebuild — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Unbound identifiers and universe names in `variable` binders are
auto-bound as the oracle does, both in `variable`'s sanity run and in every
later re-elaboration (`runTermElabM`), including the mvar-rebuild branch
and its stale `sectionFVars`. All 65 `varAuto/*` rows, each probed against
the oracle, must match, and no `— M4c-2c-ii` seam label may remain.

**Architecture:** `vars::elab_section_vars` becomes the port of
`runTermElabM` up to `elabFn`. Section binders are elaborated under P1's
`with_auto_bound_implicit`, then `synthesize_synthetic_mvars_no_postponing`.
Next a `section_fvars` (uid ↦ fvar) map is built from the binders' fvars,
then `add_auto_bound_implicits` runs. If an mvar is left in the telescope,
the context is rebuilt: `mk_forall` over `Prop`, an empty lctx, and
`forall_bounded_telescope`. `SecVars` carries the run's variables and the
uid map separately, so on the rebuild branch the map goes stale exactly as
the oracle's does. `include`/`omit`/instance lookups go through the map, and
a matched `omit` with no uid gets the new error `OmitUndeclared`.

**Tech Stack:** Rust (cargo workspace, mise tasks), Lean 4 oracle
`leanprover/lean4:v4.33.0-rc1` (fixtures only; never in CI).

**Spec:** `docs/superpowers/specs/2026-10-05-m4c2c-ii-auto-bound-design.md`.
Read § "`variable` binders (P2)", then **Amendment 1** and **Amendment 2**,
which override the body. Amendment 2 is this plan's: the stale map is
observable, `OmitUndeclared` is new, and two `leanr_meta` accessors are
added.

## Global Constraints

- Oracle pin: `leanprover/lean4:v4.33.0-rc1`; never bump it.
- `leanr_kernel` is TCB: this plan changes NO file under `crates/leanr_kernel/`.
- `leanr_meta` changes are additive and TCB-neutral (M4b precedent).
  Exactly two are allowed: `forall_bounded_telescope` `pub(crate)` → `pub`,
  and a new `MetaCtx::install_empty_lctx`.
- No new dependencies.
- After P2, `grep -rn "— M4c-2c-ii" crates` must print nothing.
- Before every commit run `cargo fmt --all` and
  `cargo clippy --workspace --all-targets -- -D warnings`; CI's
  `mise run ci` gates on both. Never background `mise run ci` and then end a
  turn: run it blocking and wait for its exit status.
- Build only under `/workspace`, never `/tmp` (a 20Gi EmptyDir).
- Every cargo run during mutation testing is wrapped:
  `ulimit -v 16000000; timeout 900 cargo test …`. A mutated retry loop has
  OOMKilled the pod twice. After each mutation, `git diff` must show the
  mutation reverted before you continue.
- Every commit body records the mutations its tests kill, as
  `Mutation: <what> ⇒ <which test fails>`. Reviewers read the bodies with
  `git log --format=%B`.
- Fixture regen needs the elan toolchain: `mise run fixtures:regen-decls`.
  It never runs in CI.
- Oracle `file:line` cites have been off by 1-2 before. Open the line in
  `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/Lean`
  before writing a cite.
- A row that diverges is a bug until shown otherwise. It may go into
  `KNOWN_GAPS` only with a reason naming an oracle-probed variant WITHOUT
  any auto-bound that diverges in leanr the same way. To probe a variant,
  run `target/m4c2ciip2probe/probe.sh <rows-file>` (see Task 1); the
  scratch directory is not committed.

## Review Focus

1. **The stale map must survive the rebuild.** After a rebuild,
   `include n` must NOT add `(n : Nat)` to a theorem
   (`varAuto/rebuildInclude` ⇒ `va42 : True`), and an `omit`ted instance
   must come back (`varAuto/rebuildOmitInstIgnored` ⇒
   `∀ [Wrap Nat], True`). An implementation that "helpfully" rebuilds the
   uid map from the new fvars gives a wrong-Ok on both. Pinned in Task 3
   (mutation (a)).
2. **The old fvars must not be reachable after a rebuild.** If the
   telescope is opened in the old lctx, the old `h` is still in scope once
   the theorem regime erases the new one. The body `h` in
   `varAuto/rebuildBodyUnknown` must be "Unknown identifier `h`", not a
   reference to a stale fvar. Pinned in Task 3 (mutation (b)).
3. **Options are read at every re-elaboration, not when `variable` runs.**
   `variable (x : α)` then `set_option autoImplicit false` makes the next
   declaration fail with "Unknown identifier `α`" (`varAuto/offAfter`).
   Pinned in Task 2.
4. **Thirty autos in one `variable`** run the retry loop 31 times in the
   sanity run and again in every later declaration (`varAuto/thirty`). The
   P1 loop is iterative; this row guards the `variable` path's use of it.
   Pinned in Task 2.
5. **An `omit [T]` that matches a binder with no uid must still error.**
   The case is an mvar binder or an anonymous instance on the rebuild
   branch. The oracle's message carries a hygienic hash name that the gate
   cannot pin, so leanr's text is allowed to differ, but the result must
   be an error and never `Ok`. Pinned by the
   `omit_type_pattern_without_uid_errors` test in Task 3.

## File map

| File | Change |
|---|---|
| `tests/fixtures/elab/dump_decls.lean` | +65 `fileQueries` rows (Task 1) |
| `tests/fixtures/elab/file-queries.jsonl` | regenerated (Task 1) |
| `crates/leanr_elab/tests/oracle_file.rs` | floor 376, `PENDING`, seam test replaced (Tasks 1-3) |
| `crates/leanr_elab/src/command/vars.rs` | `SecVars` reshape, `elab_section_vars` port, `elab_binders`, omit "not declared" arm, seam deleted (Tasks 2-3) |
| `crates/leanr_elab/src/command/mod.rs` | `with_term_elab` and `elab_variable` wiring (Task 2) |
| `crates/leanr_elab/src/error.rs` | `OmitUndeclared` (Task 2) |
| `crates/leanr_meta/src/assign.rs` | `forall_bounded_telescope` → `pub` (Task 3) |
| `crates/leanr_meta/src/metactx.rs` | `install_empty_lctx` + test (Task 3) |
| `crates/leanr_elab/src/lib.rs`, `command/vars.rs` module doc, spec § Landed | docs (Task 4) |

---

### Task 1: Corpus rows and the staged gate

**Files:**
- Modify: `tests/fixtures/elab/dump_decls.lean` (the `fileQueries` list; its
  last entry is `("auto/levelOverloadMismatchLeak", …)` just before the
  closing `]`, ~line 617)
- Regenerate: `tests/fixtures/elab/file-queries.jsonl`
- Modify: `crates/leanr_elab/tests/oracle_file.rs:10-13` (floor) and
  `:163-166` (`PENDING`)

**Interfaces:**
- Produces: `PENDING = ["varAuto/"]`. Task 2 narrows it to
  `["varAuto/rebuild"]` and Task 3 empties it.

- [ ] **Step 1: Recreate the probe scratch** (it is not committed; Tasks
  2-3 use it to probe KNOWN_GAPS variants). Run:

```bash
mkdir -p target/m4c2ciip2probe && cd /workspace && python3 - <<'PY'
src=open('tests/fixtures/elab/dump_decls.lean').read()
i=src.index('def fileQueries : List (String × String) := [')
j=src.index('\n]\n',i)
open('target/m4c2ciip2probe/template.lean','w').write(src[:i]+'def fileQueries : List (String × String) := (ROWS)'+src[j+3:])
PY
cat > target/m4c2ciip2probe/probe.sh <<'SH'
#!/bin/sh
# usage: probe.sh rows.txt — rows.txt holds Lean tuple lines `("id", "src"),` (last without comma)
P=/workspace/target/m4c2ciip2probe
python3 -c "
import sys
rows=open(sys.argv[1]).read().strip().rstrip(',')
t=open('$P/template.lean').read().replace('(ROWS)','[\n'+rows+'\n]')
open('$P/probe.lean','w').write(t)" "$1"
cd /workspace/tests/fixtures/elab && LEAN_PATH=$PWD timeout 600 lean --run $P/probe.lean files
SH
chmod +x target/m4c2ciip2probe/probe.sh
```

  Run this step BEFORE Step 2: the template must be built from the
  unmodified row list.

- [ ] **Step 2: Append the rows.** In `dump_decls.lean`, put a `,` after
  `("auto/levelOverloadMismatchLeak", …)` and append these 65 rows before
  the closing `]`. Each row was probed against the oracle at plan time;
  the expected results table follows the block.

```lean
  ("varAuto/def", "variable (x : α)\ndef va1 : α := x"),
  ("varAuto/afterExplicit", "variable (n : Nat) (x : α)\ndef va2 : PProd Nat α := PProd.mk n x"),
  ("varAuto/twoCmds", "variable (x : α)\nvariable (y : β)\ndef va3 : PProd α β := PProd.mk x y"),
  ("varAuto/interleave", "variable (x : α)\nvariable (n : Nat) (y : β)\ndef va4 : PProd α β := PProd.mk x y"),
  ("varAuto/interleaveN", "variable (x : α)\nvariable (n : Nat) (y : β)\ndef va5 : PProd Nat β := PProd.mk n y"),
  ("varAuto/share", "variable (x : α)\nvariable (y : α)\ndef va6 : PProd α α := PProd.mk x y"),
  ("varAuto/unused", "variable (x : α)\ndef va7 : Nat := Nat.zero"),
  ("varAuto/thmUnused", "variable (x : α)\ntheorem va8 : True := True.intro"),
  ("varAuto/thmViaDep", "variable (x : α)\ntheorem va9 : Eq x x := rfl"),
  ("varAuto/headerAutoAfter", "variable (x : α)\ndef va10 (y : β) : PProd α β := PProd.mk x y"),
  ("varAuto/headerSameName", "variable (x : α)\ndef va11 (y : α) : α := y"),
  ("varAuto/headerSameNameNew", "variable (x : α)\ndef va12 (y : α) (z : β) : β := z"),
  ("varAuto/thmHeaderAuto", "variable (x : α)\ntheorem va13 (y : γ) : Eq x x := rfl"),
  ("varAuto/inst", "variable [Wrap α] (x : α)\ndef va14 : α := x"),
  ("varAuto/sectionEnd", "section\nvariable (x : α)\nend\ndef va15 : Nat := Nat.zero"),
  ("varAuto/secShadow", "variable (α : Type)\nvariable (x : α)\ndef va16 : α := x"),
  ("varAuto/notClass", "variable [Foo α]"),
  ("varAuto/thirty", "variable (x0 : t0) (x1 : t1) (x2 : t2) (x3 : t3) (x4 : t4) (x5 : t5) (x6 : t6) (x7 : t7) (x8 : t8) (x9 : t9) (x10 : t10) (x11 : t11) (x12 : t12) (x13 : t13) (x14 : t14) (x15 : t15) (x16 : t16) (x17 : t17) (x18 : t18) (x19 : t19) (x20 : t20) (x21 : t21) (x22 : t22) (x23 : t23) (x24 : t24) (x25 : t25) (x26 : t26) (x27 : t27) (x28 : t28) (x29 : t29)\ndef va18 : Nat := Nat.zero"),
  ("varAuto/includeAuto", "variable (x : α)\ninclude α"),
  ("varAuto/includeX", "variable (x : α)\ninclude x\ntheorem va19 : True := True.intro"),
  ("varAuto/omitAuto", "variable (x : α)\nomit α"),
  ("varAuto/omitReferenced", "variable (x : α)\nomit x\ntheorem va21 : Eq x x := rfl"),
  ("varAuto/omitInstKept", "variable [inst : Wrap Nat]\nomit inst\nvariable (x : α)\ntheorem va22 : True := True.intro"),
  ("varAuto/omitTypeAuto", "variable [Wrap α] (x : α)\nomit [Wrap α]\ntheorem va60 (y : α) : True := True.intro"),
  ("varAuto/omitTypeUnknown", "variable (x : α)\nomit [Wrap β]"),
  ("varAuto/level", "variable (α : Sort u) (a : α)\ndef va23 : α := a"),
  ("varAuto/levelScope", "universe v\nvariable (α : Sort u) (β : Sort v) (a : α) (b : β)\ndef va24 : PProd α β := PProd.mk a b"),
  ("varAuto/levelThm", "variable (α : Sort u) (a : α)\ntheorem va25 : Eq a a := rfl"),
  ("varAuto/levelUnused", "variable (α : Sort u)\ndef va26 : Nat := Nat.zero"),
  ("varAuto/levelHeader", "variable (α : Sort u)\ndef va27 (β : Sort v) (a : α) (b : β) : α := a"),
  ("varAuto/levelAxiom", "variable (α : Sort u) (a : α)\naxiom va28 : Eq a a"),
  ("varAuto/off", "set_option autoImplicit false\nvariable (x : α)"),
  ("varAuto/offLevel", "set_option autoImplicit false\nvariable (α : Sort u)"),
  ("varAuto/strict", "set_option relaxedAutoImplicit false\nvariable (x : foo)"),
  ("varAuto/strictOk", "set_option relaxedAutoImplicit false\nvariable (x : α₁)\ndef va32 : α₁ := x"),
  ("varAuto/offAfter", "variable (x : α)\nset_option autoImplicit false\ndef va33 : α := x"),
  ("varAuto/offIn", "set_option autoImplicit false in\nvariable (x : α)"),
  ("varAuto/offInThenOn", "set_option autoImplicit false in\nvariable (n : Nat)\nvariable (x : α)\ndef va35 : α := x"),
  ("varAuto/dotted", "variable (x : Foo.bar)"),
  ("varAuto/rebuildBodyUnknown", "variable (h : Eq a a)\ntheorem va37 : Eq a a := h"),
  ("varAuto/rebuildHeaderUse", "variable (h : Eq a a)\ntheorem va38 (k : Eq h h) : True := True.intro"),
  ("varAuto/rebuildDef", "variable (h : Eq a a)\ndef va39 : Eq a a := h"),
  ("varAuto/rebuildDefUse", "variable (h : Eq a a)\ndef va40 (k : Eq h h) : Nat := Nat.zero"),
  ("varAuto/rebuildDefBody", "variable (h : Eq a a)\ndef va41 : Nat := (fun (_ : Eq a a) => Nat.zero) h"),
  ("varAuto/rebuildInclude", "variable (h : Eq a a) (n : Nat)\ninclude n\ntheorem va42 : True := True.intro"),
  ("varAuto/rebuildIncludeH", "variable (h : Eq a a)\ninclude h\ntheorem va43 : True := True.intro"),
  ("varAuto/rebuildOmitName", "variable (h : Eq a a) (n : Nat)\nomit n"),
  ("varAuto/rebuildOmitAutoName", "variable (h : Eq a a)\nomit a"),
  ("varAuto/rebuildOmitMvarName", "variable (h : Eq a a)\nomit α"),
  ("varAuto/rebuildOmitType", "variable (h : Eq a a) (n : Nat)\nomit [Wrap Nat]"),
  ("varAuto/rebuildOmitRefH", "variable (h : Eq a a) (n : Nat)\ninclude n\nomit h"),
  ("varAuto/rebuildOmitInstIgnored", "variable [inst : Wrap Nat]\nomit inst\nvariable (h : Eq a a)\ntheorem va49 : True := True.intro"),
  ("varAuto/rebuildInst", "variable (h : Eq a a) [Wrap Nat]\ntheorem va50 (k : Wrap Nat) : True := True.intro"),
  ("varAuto/rebuildInstAuto", "variable {β : Type} (h : Eq a a) [Wrap β] (y : β)\ntheorem va51 : Eq y y := rfl"),
  ("varAuto/rebuildTwoCmds", "variable (h : Eq a a)\nvariable (n : Nat)\ndef va52 : Nat := n"),
  ("varAuto/rebuildBadLater", "variable (h : Eq a a)\nvariable (n : zz.yy)"),
  ("varAuto/rebuildHEq", "variable (h : HEq a b)\ntheorem va54 (k : Eq h h) : True := True.intro"),
  ("varAuto/rebuildExample", "variable (h : Eq a a)\nexample : Nat := Nat.zero"),
  ("varAuto/rebuildAxiom", "variable (h : Eq a a)\naxiom va56 (k : Eq h h) : Nat"),
  ("varAuto/rebuildInstMvar", "variable (h : Eq a a) [Wrap α]"),
  ("varAuto/rebuildNamedMvar", "variable (h : Eq a a)\ntheorem va58 (k : Eq h h) : True := True.intro\nexample : True := va58 (α := Nat)"),
  ("varAuto/rebuildNamedAuto", "variable (h : Eq a a)\ntheorem va59 (k : Eq h h) : True := True.intro\nexample : True := va59 (a := Nat.zero) rfl rfl"),
  ("varAuto/rebuildSectionEnd", "section\nvariable (h : Eq a a)\nend\nvariable (n : Nat)\ninclude n\ntheorem va61 : True := True.intro"),
  ("varAuto/rebuildHeaderAlpha", "variable (h : Eq a a)\ndef va62 (x : α) : α := x"),
  ("varAuto/rebuildHeaderAlphaThm", "variable (h : Eq a a)\ntheorem va63 (x : α) (k : Eq h h) : Eq x x := rfl")
```

  Expected results (binder names are erased by the dumper; `{}` implicit,
  `()` explicit, `[]` instance; `Sort` levels elided; errors show the first
  line with backticks rendered as `'`):

| id | oracle, last command |
|---|---|
| `varAuto/def` | `va1.{u_1} : ∀{x0:Sort}, ∀(x1:x0), x0` |
| `varAuto/afterExplicit` | `va2.{u_1} : ∀{x0:Sort}, ∀(x1:Nat), ∀(x2:x0), ((PProd Nat) x0)` |
| `varAuto/twoCmds` | `va3.{u_1,u_2} : ∀{x0:Sort}, ∀{x1:Sort}, ∀(x2:x0), ∀(x3:x1), ((PProd x0) x1)` |
| `varAuto/interleave` | `va4.{u_1,u_2} : ∀{x0:Sort}, ∀{x1:Sort}, ∀(x2:x0), ∀(x3:x1), ((PProd x0) x1)` |
| `varAuto/interleaveN` | `va5.{u_1} : ∀{x0:Sort}, ∀(x1:Nat), ∀(x2:x0), ((PProd Nat) x0)` |
| `varAuto/share` | `va6.{u_1} : ∀{x0:Sort}, ∀(x1:x0), ∀(x2:x0), ((PProd x0) x0)` |
| `varAuto/unused` | `va7.{} : Nat` |
| `varAuto/thmUnused` | `va8.{} : True` |
| `varAuto/thmViaDep` | `va9.{u_1} : ∀{x0:Sort}, ∀(x1:x0), (((Eq x0) x1) x1)` |
| `varAuto/headerAutoAfter` | `va10.{u_1,u_2} : ∀{x0:Sort}, ∀(x1:x0), ∀{x2:Sort}, ∀(x3:x2), ((PProd x0) x2)` |
| `varAuto/headerSameName` | `va11.{u_1} : ∀{x0:Sort}, ∀(x1:x0), x0` |
| `varAuto/headerSameNameNew` | `va12.{u_1,u_2} : ∀{x0:Sort}, ∀{x1:Sort}, ∀(x2:x0), ∀(x3:x1), x1` |
| `varAuto/thmHeaderAuto` | `va13.{u_1,u_2} : ∀{x0:Sort}, ∀(x1:x0), ∀{x2:Sort}, ∀(x3:x2), (((Eq x0) x1) x1)` |
| `varAuto/inst` | `va14.{} : ∀{x0:Sort}, ∀(x1:x0), x0` |
| `varAuto/sectionEnd` | `va15.{} : Nat` |
| `varAuto/secShadow` | `va16.{} : ∀(x0:Sort), ∀(x1:x0), x0` |
| `varAuto/notClass` | err `invalid binder annotation, type is not a class instance` |
| `varAuto/thirty` | `va18.{} : Nat` |
| `varAuto/includeAuto` | err `invalid 'include', variable 'α' has not been declared in the current scope` |
| `varAuto/includeX` | `va19.{u_1} : ∀{x0:Sort}, ∀(x1:x0), True` |
| `varAuto/omitAuto` | err `invalid 'omit', 'α' has not been declared in the current scope` |
| `varAuto/omitReferenced` | err `cannot omit referenced section variable 'x'` |
| `varAuto/omitInstKept` | `va22.{} : True` |
| `varAuto/omitTypeAuto` | `va60.{} : ∀{x0:Sort}, ∀(x1:x0), True` |
| `varAuto/omitTypeUnknown` | err `Unknown identifier 'β'` |
| `varAuto/level` | `va23.{u} : ∀(x0:Sort), ∀(x1:x0), x0` |
| `varAuto/levelScope` | `va24.{v,u} : ∀(x0:Sort), ∀(x1:Sort), ∀(x2:x0), ∀(x3:x1), ((PProd x0) x1)` |
| `varAuto/levelThm` | `va25.{u} : ∀(x0:Sort), ∀(x1:x0), (((Eq x0) x1) x1)` |
| `varAuto/levelUnused` | `va26.{} : Nat` |
| `varAuto/levelHeader` | `va27.{u,v} : ∀(x0:Sort), ∀(x1:Sort), ∀(x2:x0), ∀(x3:x1), x0` |
| `varAuto/levelAxiom` | `va28.{u} : ∀(x0:Sort), ∀(x1:x0), (((Eq x0) x1) x1)` |
| `varAuto/off` | err `Unknown identifier 'α'` |
| `varAuto/offLevel` | err `unknown universe level 'u'` |
| `varAuto/strict` | err `Unknown identifier 'foo'` |
| `varAuto/strictOk` | `va32.{u_1} : ∀{x0:Sort}, ∀(x1:x0), x0` |
| `varAuto/offAfter` | err `Unknown identifier 'α'` |
| `varAuto/offIn` | err `Unknown identifier 'α'` |
| `varAuto/offInThenOn` | `va35.{u_1} : ∀{x0:Sort}, ∀(x1:x0), x0` |
| `varAuto/dotted` | err `Unknown identifier 'Foo.bar'` |
| `varAuto/rebuildBodyUnknown` | err `Unknown identifier 'h'` |
| `varAuto/rebuildHeaderUse` | `va38.{u_1} : ∀{x0:Sort}, ∀{x1:x0}, ∀(x2:(((Eq x0) x1) x1)), ∀(x3:(((Eq (((Eq x0) x1) x1)) x2) x2)), True` |
| `varAuto/rebuildDef` | `va39.{u_1} : ∀{x0:Sort}, ∀{x1:x0}, ∀(x2:(((Eq x0) x1) x1)), (((Eq x0) x1) x1)` |
| `varAuto/rebuildDefUse` | `va40.{u_1} : ∀{x0:Sort}, ∀{x1:x0}, ∀(x2:(((Eq x0) x1) x1)), ∀(x3:(((Eq (((Eq x0) x1) x1)) x2) x2)), Nat` |
| `varAuto/rebuildDefBody` | `va41.{u_1} : ∀{x0:Sort}, ∀{x1:x0}, ∀(x2:(((Eq x0) x1) x1)), Nat` |
| `varAuto/rebuildInclude` | `va42.{} : True` |
| `varAuto/rebuildIncludeH` | `va43.{} : True` |
| `varAuto/rebuildOmitName` | err `invalid 'omit', 'n' has not been declared in the current scope` |
| `varAuto/rebuildOmitAutoName` | err `invalid 'omit', 'a' has not been declared in the current scope` |
| `varAuto/rebuildOmitMvarName` | err `'α' did not match any variables in the current scope` |
| `varAuto/rebuildOmitType` | err `'[Wrap Nat]' did not match any variables in the current scope` |
| `varAuto/rebuildOmitRefH` | err `invalid 'omit', 'h' has not been declared in the current scope` |
| `varAuto/rebuildOmitInstIgnored` | `va49.{} : ∀[x0:(Wrap Nat)], True` |
| `varAuto/rebuildInst` | `va50.{} : ∀[x0:(Wrap Nat)], ∀(x1:(Wrap Nat)), True` |
| `varAuto/rebuildInstAuto` | `va51.{} : ∀{x0:Sort}, ∀[x1:(Wrap x0)], ∀(x2:x0), (((Eq x0) x2) x2)` |
| `varAuto/rebuildTwoCmds` | `va52.{} : ∀(x0:Nat), Nat` |
| `varAuto/rebuildBadLater` | err `Unknown identifier 'zz.yy'` |
| `varAuto/rebuildHEq` | `va54.{u_1} : ∀{x0:Sort}, ∀{x1:x0}, ∀{x2:Sort}, ∀{x3:x2}, ∀(x4:((((HEq x0) x1) x2) x3)), ∀(x5:(((Eq ((((HEq x0) x1) x2) x3)) x4) x4)), True` |
| `varAuto/rebuildExample` | ok, no constants |
| `varAuto/rebuildAxiom` | `va56.{u_1} : ∀{x0:Sort}, ∀{x1:x0}, ∀(x2:(((Eq x0) x1) x1)), ∀(x3:(((Eq (((Eq x0) x1) x1)) x2) x2)), Nat` |
| `varAuto/rebuildInstMvar` | ok, no constants |
| `varAuto/rebuildNamedMvar` | err `Invalid argument name 'α' for function 'va58'` |
| `varAuto/rebuildNamedAuto` | ok, no constants |
| `varAuto/rebuildSectionEnd` | `va61.{} : ∀(x0:Nat), True` |
| `varAuto/rebuildHeaderAlpha` | `va62.{u_1} : ∀{x0:Sort}, ∀(x1:x0), x0` |
| `varAuto/rebuildHeaderAlphaThm` | `va63.{u_1,u_2} : ∀{x0:Sort}, ∀{x1:x0}, ∀(x2:(((Eq x0) x1) x1)), ∀{x3:Sort}, ∀(x4:x3), ∀(x5:(((Eq (((Eq x0) x1) x1)) x2) x2)), (((Eq x3) x4) x4)` |

- [ ] **Step 3: Regenerate.** Run `mise run fixtures:regen-decls`.
  Expected: `wc -l tests/fixtures/elab/file-queries.jsonl` = 311 + 65 =
  **376**, and the dumper prints nothing on stderr for a `varAuto/` id.
  `git diff --stat tests/fixtures/elab/decl-queries.jsonl` must be empty.
  Spot-check: `grep '"varAuto/rebuildInclude"'` has a `va42` whose type is
  `{"k":"const","n":"True","us":[]}`; `varAuto/omitAuto`'s last command is
  ``{"err":"invalid 'omit', `α` has not been declared in the current scope"}``
  (JSON may escape `α` as `α`).

- [ ] **Step 4: Stage the gate.** In `oracle_file.rs` set
  `const CORPUS_FLOOR: usize = 376;` and change its doc's
  `(M4c-2c-ii P1: 308)` to `(M4c-2c-ii P2: 376)`. Replace the `PENDING`
  doc and value:

```rust
/// M4c-2c-ii P2 rows not yet passing: Task 2 narrows `varAuto/` to
/// `varAuto/rebuild`, Task 3 empties the list.
const PENDING: &[&str] = &["varAuto/"];
```

  In `KNOWN_GAPS`' doc comment, change "Survives P1" to "Survives P1 and
  P2".

- [ ] **Step 5: Verify.** Run
  `cargo test -p leanr_elab --test oracle_file oracle_file_gate file_corpus_sources`.
  Expected: PASS (311 checked or known, 65 pending; all 376 sources parse
  into the oracle's command count). If a `varAuto` source fails the parse
  test, stop and report it: it is a parser gap, and P1 dropped
  `auto/identInBinderDefault` the same way.

- [ ] **Step 6: Commit.**

```bash
git add tests/fixtures/elab crates/leanr_elab/tests/oracle_file.rs
git commit -m "M4c-2c-ii P2 Task 1: 65 oracle-probed varAuto rows (staged)"
```

---

### Task 2: `runTermElabM`'s all-fvar branch, `variable`'s sanity run, `OmitUndeclared`

**Files:**
- Modify: `crates/leanr_elab/src/command/vars.rs`. Replace `SecVars`
  (`:40-50`), `elab_section_vars` + `variable_auto_bound_seam`
  (`:145-176`), the uid lookups in `header_sec_vars` (`:242-266`), and
  `elab_omit`'s loop (`:510-535`).
- Modify: `crates/leanr_elab/src/command/mod.rs`, in `with_term_elab`
  (`:243-278`) and `elab_variable`'s sanity run (`:320-323`).
- Modify: `crates/leanr_elab/src/error.rs`: a variant beside
  `OmitUnmatched` (`:347`), its `oracle_first_line` arm (`:648`), and an
  assertion in the first-line test (`:851`).
- Test: `crates/leanr_elab/tests/oracle_file.rs`
  (`variable_seams_carry_their_slice`, `PENDING`).

**Interfaces:**
- Consumes (P1, `auto_bound.rs`): `TermElabM::with_auto_bound_implicit(k)`
  (iterative retry loop; resets the context to the outer one on exit; the
  autos' local decls stay in the lctx) and
  `TermElabM::add_auto_bound_implicits(&[ExprId]) -> Result<Vec<ExprId>, ElabError>`
  (autos with their type mvars, then `xs`).
- Produces (used by Task 3):

```rust
pub(super) struct SecVars {
    pub fvars: Vec<ExprId>,
    pub section_fvars: Vec<(u32, ExprId)>,
    pub included: Vec<u32>,
    pub omitted: Vec<u32>,
}
impl SecVars { pub fn uid_of(&self, x: ExprId) -> Option<u32> }
/// Returns (`elabFn`'s xs, `sectionFVars`).
pub(super) fn elab_section_vars(
    elab: &mut TermElabM, var_decls: &[SyntaxNode], var_uids: &[u32], kinds: &KindInterner,
) -> Result<(Vec<ExprId>, Vec<(u32, ExprId)>), ElabError>
ElabError::OmitUndeclared(String)
```

  Task 3 replaces only the body of `elab_section_vars`' "mvars present"
  arm.

- [ ] **Step 1: Write the failing tests.**

  (a) In `oracle_file.rs`, cut `PENDING` down to the rebuild rows:

```rust
/// M4c-2c-ii P2 rows not yet passing: Task 3 (the rebuild branch)
/// empties the list.
const PENDING: &[&str] = &["varAuto/rebuild"];
```

  (b) In `variable_seams_carry_their_slice`, delete the last two blocks
  (`variable (x : β)` and `variable (α : Sort w)`, together with their
  comments). After the function, add:

```rust
#[test]
fn variable_binders_auto_bind() {
    // Oracle: `elabVariable`'s sanity run is `withAutoBoundImplicit`
    // (`BuiltinCommand.lean:419-425`), for identifiers and universes.
    for src in ["variable (x : β)", "variable (α : Sort w)"] {
        let (done, stopped, _) = outcome(src);
        assert!(stopped.is_none(), "{src:?}: {stopped:?}");
        assert_eq!(done.len(), 1, "{src:?}");
    }
}
```

  (c) In `error.rs`'s first-line test, after the `OmitUnmatched`
  assertion, add:

```rust
        assert_eq!(
            ElabError::OmitUndeclared("a".into())
                .oracle_first_line()
                .as_deref(),
            Some("invalid 'omit', `a` has not been declared in the current scope") // varAuto/omitAuto
        );
```

- [ ] **Step 2: Run them and confirm they fail.**
  `cargo test -p leanr_elab --test oracle_file` should fail to compile
  (`OmitUndeclared` does not exist yet). If you temporarily comment out
  (c), `variable_binders_auto_bind` and `oracle_file_gate` should FAIL:
  the binders stop at the `— M4c-2c-ii` seam, and the gate fails on
  `varAuto/def` and the other non-rebuild rows.

- [ ] **Step 3: Add the error.** In `error.rs`, after `OmitUnmatched(String),`:

```rust
    /// oracle: `elabOmit` (`Elab/BuiltinCommand.lean:598-599`): an `omit`
    /// item matched a run variable that has no section-variable uid (an
    /// auto-bound implicit, or any variable on `runTermElabM`'s rebuild
    /// branch, whose `sectionFVars` is stale). Carries the binder's user
    /// name. For an mvar binder or an anonymous instance the oracle prints
    /// a hygienic name with a hash in it, which the gate cannot pin; leanr
    /// prints its own binder name there.
    OmitUndeclared(String),
```

  and in `oracle_first_line`, after the `OmitUnmatched` arm:

```rust
            Self::OmitUndeclared(x) => Some(format!(
                "invalid 'omit', `{x}` has not been declared in the current scope"
            )),
```

  If `error.rs` has an exhaustive `match` elsewhere (for example a
  `Display` or a list of oracle classes), add `OmitUndeclared` next to
  `OmitUnmatched` there as well. `cargo build` will name each one.

- [ ] **Step 4: Reshape `SecVars`.** In `vars.rs`, replace the struct
  (`:40-50`) with:

```rust
/// One run of the head scope's section variables (oracle `runTermElabM`,
/// `Command.lean:774-798`): what `elabFn` receives plus `sectionFVars`.
pub(super) struct SecVars {
    /// `elabFn`'s `xs`: the auto-bound implicits (each preceded by the
    /// unassigned mvars of its type, `addAutoBoundImplicits`), then one
    /// fvar per binder id. On the rebuild branch these are the fresh
    /// telescope's fvars.
    pub fvars: Vec<ExprId>,
    /// oracle `sectionFVars` (`Command.lean:782-784`): binder-id uid ↦
    /// the fvar elaborated for it, built BEFORE `addAutoBoundImplicits`
    /// and the rebuild. Autos never have a uid, and on the rebuild branch
    /// no member of `fvars` has one (the oracle's stale map, observable:
    /// `varAuto/rebuildInclude`, spec Amendment 2).
    pub section_fvars: Vec<(u32, ExprId)>,
    /// `Scope::included_vars` / `omitted_vars`.
    pub included: Vec<u32>,
    pub omitted: Vec<u32>,
}

impl SecVars {
    /// `revSectionFVars[x]?` (`MutualDef.lean:457-459`,
    /// `BuiltinCommand.lean:585-587`).
    pub fn uid_of(&self, x: ExprId) -> Option<u32> {
        self.section_fvars
            .iter()
            .find(|&&(_, f)| f == x)
            .map(|&(u, _)| u)
    }
}
```

- [ ] **Step 5: Port `runTermElabM`.** Replace `elab_section_vars` and
  `variable_auto_bound_seam` (and its doc) with:

```rust
/// oracle `elabBinders` over bracketed binder syntax: one fvar per binder
/// id, in order, left in the local context.
pub(super) fn elab_binders(
    elab: &mut TermElabM,
    binders: &[SyntaxNode],
    kinds: &KindInterner,
) -> Result<Vec<ExprId>, ElabError> {
    let mut xs = Vec::new();
    for b in binders {
        let g = extract_binder_group(elab, b, kinds)?;
        xs.extend(push_binder_group(elab, &g, kinds)?);
    }
    Ok(xs)
}

/// oracle `runTermElabM` up to `elabFn` (`Command.lean:776-798`):
/// `withAutoBoundImplicit (elabBinders varDecls …)`,
/// `synthesizeSyntheticMVarsNoPostponing`, `sectionFVars` from the
/// binders' fvars, then `addAutoBoundImplicits`. The loop leaves the
/// autos in the local context and resets the auto-bound context on exit,
/// which is the oracle's `withoutAutoBoundImplicit (elabFn xs)` for the
/// caller. Returns (`elabFn`'s xs, `sectionFVars`).
pub(super) fn elab_section_vars(
    elab: &mut TermElabM,
    var_decls: &[SyntaxNode],
    var_uids: &[u32],
    kinds: &KindInterner,
) -> Result<(Vec<ExprId>, Vec<(u32, ExprId)>), ElabError> {
    let (xs, section_fvars) = elab.with_auto_bound_implicit(|elab| {
        let xs = elab_binders(elab, var_decls, kinds)?;
        elab.synthesize_synthetic_mvars_no_postponing(kinds)?;
        if xs.len() != var_uids.len() {
            return Err(ElabError::Internal(
                "section variables: one uid per binder id".into(),
            ));
        }
        let section_fvars: Vec<(u32, ExprId)> =
            var_uids.iter().copied().zip(xs.iter().copied()).collect();
        let xs = elab.add_auto_bound_implicits(&xs)?;
        Ok((xs, section_fvars))
    })?;
    let all_fvars = xs.iter().all(|&x| {
        matches!(
            elab.mctx.store().expr_node(Some(elab.view.store), x),
            Node::FVar { .. }
        )
    });
    if all_fvars {
        return Ok((xs, section_fvars));
    }
    // `:791-797`, the rebuild branch.
    Err(ElabError::UnsupportedSyntax(
        "auto-bound mvar in a section variable's type (`runTermElabM` rebuild) — \
         M4c-2c-ii P2 Task 3"
            .into(),
    ))
}
```

  The temporary seam above lives only between Task 2 and Task 3, and the
  `varAuto/rebuild` rows stay pending while it exists.

- [ ] **Step 6: Route the uid lookups through `section_fvars`.** In
  `header_sec_vars`:

```rust
    // included by `include`
    for &x in &sv.fvars {
        if sv.uid_of(x).is_some_and(|u| sv.included.contains(&u)) {
            used.add(x);
        }
    }
```

```rust
    if check {
        for &x in &used.ids {
            if sv.uid_of(x).is_some_and(|u| sv.omitted.contains(&u)) {
                let d = local_decl(elab, x)?;
                return Err(ElabError::OmitReferenced(fvar_message_name(elab, &d)));
            }
        }
    }
    // instances whose type's fvars are all kept, in variable order
    for &x in &sv.fvars {
        if sv.uid_of(x).is_some_and(|u| sv.omitted.contains(&u)) {
            continue;
        }
```

  The rest of the instance loop is unchanged. In `elab_omit`, change the
  loop head `for (&x, &uid) in sv.fvars.iter().zip(&sv.uids) {` to
  `for &x in &sv.fvars {`, and replace the `if let Some(i) = hit { … }`
  block, together with its "Every run variable is a section variable"
  comment, with:

```rust
                if let Some(i) = hit {
                    match sv.uid_of(x) {
                        Some(uid) => {
                            omitted.push(uid);
                            used[i] = true;
                        }
                        // `:598-599`: an auto, or any variable after a
                        // rebuild (stale `sectionFVars`).
                        None => {
                            return Err(ElabError::OmitUndeclared(crate::names::render(
                                elab.mctx.store(),
                                Some(elab.view.store),
                                d.binder_name,
                            )))
                        }
                    }
                }
```

- [ ] **Step 7: Wire the callers.** In `mod.rs`'s `with_term_elab`,
  replace everything from `let fvars = vars::elab_section_vars(…)` through
  the end of the `SecVars { … }` literal with:

```rust
            let (fvars, section_fvars) =
                vars::elab_section_vars(&mut elab, &head.var_decls, &head.var_uids, kinds)?;
            let sv = SecVars {
                fvars,
                section_fvars,
                included: head.included_vars.clone(),
                omitted: head.omitted_vars.clone(),
            };
```

  The uid-count check moves into `elab_section_vars`. In `elab_variable`,
  replace the sanity run (`:320-323`) with:

```rust
        // The sanity elaboration (`:419-425`): under the scope's variables,
        // `withSynthesize (withAutoBoundImplicit (elabBinders binders
        // (addAutoBoundImplicits ·)))`, result discarded.
        self.with_term_elab(kinds, |elab, _| {
            elab.with_synthesize(PostponeBehavior::No, kinds, |elab| {
                elab.with_auto_bound_implicit(|elab| {
                    let xs = vars::elab_binders(elab, &binders, kinds)?;
                    elab.add_auto_bound_implicits(&xs).map(|_| ())
                })
            })
        })?;
```

  Add `use crate::synthetic::PostponeBehavior;` to `mod.rs` if it is not
  already imported. In `vars.rs`, the `ElabError` import stays. Remove any
  import that clippy reports as unused.

- [ ] **Step 8: Run the tests.**
  `ulimit -v 16000000; timeout 1200 cargo test -p leanr_elab --test oracle_file`.
  Expected: PASS, with every non-rebuild `varAuto` row checked. Then run
  `cargo test -p leanr_elab` (unit tests and the decl corpus): PASS.
  For each `varAuto` row that fails, compare leanr's output with the
  table in Task 1. Before calling the row a KNOWN_GAP, probe an
  auto-free variant (Global Constraints). The suspects are rows whose
  shape matches P1's gaps: `varAuto/thmHeaderAuto` (theorem header level
  order, like `auto/withUsedVarThm`) and `varAuto/notClass` (the
  instance-binder error text).

- [ ] **Step 9: Mutations.** Run each one under `ulimit`, confirm that
  the named test fails, then revert:
  (a) build `section_fvars` AFTER `add_auto_bound_implicits` (zip the
  uids with the autos-first `xs`) ⇒ `varAuto/includeX` (its
  `include x` would hit the auto `α`) and `varAuto/omitAuto` fail;
  (b) in `elab_omit`, `None => continue` instead of the error ⇒
  `varAuto/omitAuto` and `varAuto/omitTypeAuto` fail;
  (c) drop the inner `with_auto_bound_implicit` in `elab_variable` ⇒
  `variable_binders_auto_bind` and `varAuto/def` fail;
  (d) return `xs` with the autos last (`xs` before the
  `add_auto_bound_implicits` result) ⇒ `varAuto/afterExplicit` fails;
  (e) seed `elab.options` AFTER `elab_section_vars` in `with_term_elab`
  ⇒ `varAuto/offAfter` fails;
  (f) `uid_of` always `None` ⇒ `include/*` and `omit/*` rows from
  M4c-2c-i fail.
  If a mutation survives, add a row or a unit test that kills it, or
  record why it is equivalent.

- [ ] **Step 10: Commit.** Run `cargo fmt --all` and
  `cargo clippy --workspace --all-targets -- -D warnings` first.

```bash
git add crates/leanr_elab
git commit -m "M4c-2c-ii P2 Task 2: variable auto-bound, sectionFVars map, OmitUndeclared

<one Mutation: line per Step 9 item>"
```

---

### Task 3: The rebuild branch (`mkForallFVars'` → empty lctx → `forallBoundedTelescope`)

**Files:**
- Modify: `crates/leanr_meta/src/assign.rs:742` (`pub(crate) fn
  forall_bounded_telescope` → `pub fn`)
- Modify: `crates/leanr_meta/src/metactx.rs`: add `install_empty_lctx`
  after `erase_locals` (`~:688`), and a test beside
  `erase_locals_drops_the_decl_and_its_instance_and_reinstalls`
  (`~:2662`)
- Modify: `crates/leanr_elab/src/command/vars.rs` (`elab_section_vars`'
  rebuild arm)
- Test: `crates/leanr_elab/tests/oracle_file.rs` (`PENDING` emptied, plus
  a new test)

**Interfaces:**
- Consumes: Task 2's `elab_section_vars` / `SecVars`; P1's
  `MetaCtx::mk_forall`, whose mvar arm abstracts unassigned mvars in the
  telescope into implicit binders with inaccessible names;
  `crate::builtin::sort::mk_prop(elab) -> Result<ExprId, ElabError>`.
- Produces: `MetaCtx::install_empty_lctx(&mut self) -> Arc<LocalCtxSnapshot>`;
  `MetaCtx::forall_bounded_telescope(&mut self, ty: ExprId, num_args: usize) -> Result<Vec<ExprId>, MetaError>`
  (now `pub`).

- [ ] **Step 1: Write the failing `leanr_meta` test**, beside the
  `erase_locals` test (same `with_class_ctx` harness):

```rust
    /// `withLCtx {} {}` (`Elab/Command.lean:796`): the installed context
    /// has no decls and no local instances; the returned snapshot puts
    /// the old one back.
    #[test]
    fn install_empty_lctx_clears_decls_and_instances_and_reinstalls() {
        with_class_ctx(|ctx, add| {
            let add_n = class_app(ctx, add);
            let n = const_named(ctx, "N");
            let base = Some(ctx.view.store);
            let s = ctx.scratch.intern_str(base, "a").expect("intern");
            let na = ctx.scratch.name_str(base, None, s).expect("name");
            let a = ctx
                .push_local_decl(Some(na), n, BinderInfo::Default)
                .expect("a");
            ctx.push_local_decl(None, add_n, BinderInfo::InstImplicit)
                .expect("i");
            assert_eq!(ctx.local_instances.entries().len(), 1);

            let prev = ctx.install_empty_lctx();
            assert_eq!(ctx.lctx_checkpoint(), 0, "no decls");
            assert!(ctx.local_instances.entries().is_empty(), "no instances");
            assert_eq!(ctx.lctx_lookup_by_name(na), None);

            ctx.install_lctx(prev);
            assert_eq!(ctx.lctx_lookup_by_name(na), Some(a));
            assert_eq!(ctx.local_instances.entries().len(), 1);
        });
    }
```

- [ ] **Step 2: Run it and confirm it fails.**
  `cargo test -p leanr_meta install_empty_lctx` should fail to compile
  (no such method).

- [ ] **Step 3: Implement.** In `metactx.rs`, after `erase_locals`:

```rust
    /// oracle `withLCtx {} {}` (`Elab/Command.lean:796`, `runTermElabM`'s
    /// rebuild branch): install an empty local context with no local
    /// instances, returning the one it replaced (reinstall it with
    /// `install_lctx`). Additive: only that branch calls it.
    pub fn install_empty_lctx(&mut self) -> Arc<LocalCtxSnapshot> {
        let empty = Arc::new(LocalCtxSnapshot::new(LocalContext::default(), Vec::new(), Vec::new()));
        self.install_lctx(empty)
    }
```

  (`LocalContext` is already imported, `metactx.rs:16`.) In `assign.rs:742`, change `pub(crate) fn
  forall_bounded_telescope` to `pub fn`, and add a sentence to its doc:
  "`pub` for `leanr_elab`'s `runTermElabM` rebuild (M4c-2c-ii P2)."
  Run `cargo test -p leanr_meta`: PASS.

- [ ] **Step 4: Write the failing `leanr_elab` tests.** Empty `PENDING`:

```rust
/// Empty: M4c-2c-ii P2 complete.
const PENDING: &[&str] = &[];
```

  and add, after `variable_binders_auto_bind`:

```rust
#[test]
fn omit_type_pattern_without_uid_errors() {
    // Rebuild branch: `[Wrap Nat]` matches the anonymous instance, which
    // has no uid (stale `sectionFVars`). The oracle prints a hygienic
    // hash name (`inst._@.…`) the gate cannot pin; leanr must still
    // error, never `Ok` (spec Amendment 2).
    let (_, stopped, _) = outcome("variable (h : Eq a a) [Wrap Nat]\nomit [Wrap Nat]");
    assert!(
        matches!(stopped, Some((1, leanr_elab::ElabError::OmitUndeclared(_)))),
        "{stopped:?}"
    );
}
```

  If `Wrap` is not in the `outcome` harness's environment, use a class
  that is (check `support::with_file_elab`'s env, which is the corpus's
  `Elab0`).

- [ ] **Step 5: Run them and confirm they fail.**
  `cargo test -p leanr_elab --test oracle_file`: every `varAuto/rebuild*`
  row and the new test FAIL on the Task 2 seam ("… rebuild) — M4c-2c-ii P2
  Task 3").

- [ ] **Step 6: Implement the rebuild arm.** In `elab_section_vars`,
  replace the temporary `Err(UnsupportedSyntax(…))` (and its
  `// :791-797` comment) with:

```rust
    // `:791-797`: abstract the mvars (and fvars) of `xs` over a
    // placeholder `Sort 0` (`mkForallFVars'`; leanr's mvar arm names mvar
    // binders inaccessibly, spec Amendment 1), then reopen the telescope
    // in an EMPTY context (`withLCtx {} {}`), so the old fvars cannot be
    // reached. `section_fvars` keeps the OLD fvars: the oracle's stale
    // map (spec Amendment 2). The replaced context is never reinstalled:
    // `elabFn` runs to the end of this scratch run inside it, as the
    // oracle's `withLCtx` scope does.
    let prop = crate::builtin::sort::mk_prop(elab)?;
    let ctx_ty = elab.mctx.mk_forall(&xs, prop)?;
    let _outer = elab.mctx.install_empty_lctx();
    let ys = elab.mctx.forall_bounded_telescope(ctx_ty, xs.len())?;
    if ys.len() != xs.len() {
        return Err(ElabError::Internal(
            "runTermElabM rebuild: telescope shorter than xs".into(),
        ));
    }
    Ok((ys, section_fvars))
```

- [ ] **Step 7: Run the tests.**
  `ulimit -v 16000000; timeout 1200 cargo test -p leanr_elab --test oracle_file`
  → PASS; `cargo test -p leanr_elab` → PASS; `cargo test -p leanr_meta` →
  PASS. Handle a failing row as in Task 2 Step 8.

- [ ] **Step 8: Mutations** (under `ulimit`; revert each one):
  (a) build `section_fvars` from `ys` (zip `var_uids` with the LAST
  `var_uids.len()` entries of `ys`) ⇒ `varAuto/rebuildInclude`,
  `varAuto/rebuildOmitInstIgnored` and `varAuto/rebuildOmitName` fail;
  (b) skip `install_empty_lctx` ⇒ `varAuto/rebuildBodyUnknown` fails
  (the old `h` stays reachable);
  (c) always take the rebuild branch (`all_fvars = false`) ⇒
  `varAuto/includeX` and the M4c-2c-i `include/*` rows fail;
  (d) `forall_bounded_telescope(ctx_ty, xs.len() - 1)` ⇒ every
  `varAuto/rebuild*` row fails (the Internal error);
  (e) make `install_empty_lctx` return `self.current_lctx()` without
  installing anything ⇒
  `install_empty_lctx_clears_decls_and_instances_and_reinstalls` fails.
  Record survivors as in Task 2.

- [ ] **Step 9: Commit** (fmt + clippy first).

```bash
git add crates/leanr_meta crates/leanr_elab
git commit -m "M4c-2c-ii P2 Task 3: runTermElabM rebuild branch (stale sectionFVars)

<one Mutation: line per Step 8 item>"
```

---

### Task 4: Close-out

**Files:**
- Modify: `crates/leanr_elab/src/lib.rs:225-245` (module doc)
- Modify: `crates/leanr_elab/src/command/vars.rs:1-21` (module doc)
- Modify: `docs/superpowers/specs/2026-10-05-m4c2c-ii-auto-bound-design.md`
  (§ Landed gets a `### P2 (variable binders)` subsection)

- [ ] **Step 1: Seam sweep.** `grep -rn "— M4c-2c-ii" crates` must print
  nothing. `grep -rn "M4c-2c-ii P2 Task" crates` must print nothing (the
  temporary seam is gone).

- [ ] **Step 2: Docs.**
  - In `lib.rs`, replace "Open seams: auto-bound implicits in `variable`
    binders and unknown universes there (`— M4c-2c-ii`, P2); the" with
    "Auto-bound implicits in `variable` binders and `runTermElabM`'s
    mvar-rebuild branch (stale `sectionFVars`, faithfully) landed in P2
    (corpus 376). Open seams: the". Also add a line to the "Known
    rendering limits": "`OmitUndeclared` for an mvar binder or an
    anonymous instance prints leanr's binder name, not the oracle's
    hygienic hash name."
  - In `vars.rs`'s module doc, delete "auto-bound implicits in
    `variable` binders (… is P2), the mvar-rebuild branch of
    `runTermElabM` (auto-bound only; P2)," from the "Not modelled" list,
    and add a sentence: "Auto-bound implicits and the mvar-rebuild
    branch (M4c-2c-ii P2) are modelled; `SecVars::section_fvars` is the
    oracle's pre-rebuild `sectionFVars`."
  - In the spec's § Landed, add `### P2 (variable binders)` with: commit
    list; corpus floor 376 (65 rows); `KNOWN_GAPS` added (if any, each
    with its auto-free variant); the mutations from the Task 2/3 commit
    bodies; survivors; deviations (the inaccessible-name rendering in
    `OmitUndeclared`; the rebuild never reinstalls the outer lctx). Mark
    the P1 "Open seams" line "P2 `variable` auto-bound and the
    `runTermElabM` mvar-rebuild branch" as closed.

- [ ] **Step 3: Full gate.** Run `mise run ci` BLOCKING (foreground), and
  wait for the exit code. Expected: exit 0.

- [ ] **Step 4: Commit.**

```bash
git add crates/leanr_elab/src/lib.rs crates/leanr_elab/src/command/vars.rs docs/superpowers/specs
git commit -m "M4c-2c-ii P2 Task 4: close-out (docs, spec § Landed)"
```

- [ ] **Step 5: Final review.** Dispatch one fresh reviewer (most capable
  model) over the whole branch diff, with oracle probing allowed through
  `target/m4c2ciip2probe/probe.sh`. Ask it explicitly to (1) try to build
  a wrong-Ok reproducer for every KNOWN_GAPS entry and every deferred
  ruling, and (2) probe the stale-map behaviour across a `section … end`
  boundary, under `set_option … in`, and with `omit`/`include` issued
  BEFORE the rebuild-triggering `variable`. On the last two P1-era
  slices, this final review is where the wrong-Ok was found.
