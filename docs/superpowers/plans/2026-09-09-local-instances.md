# Local instances (`LocalInstances`) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Model the oracle's `LocalInstances` context in `leanr_meta` — installed at every fvar-pushing scope, carried on metavariable declarations, and consumed by `get_instances` — so that M4b-3 P5's instance-implicit binders have a consumer instead of shipping decorative.

**Architecture:** A sparse `local_instances: Vec<LocalInstance>` on `MetaCtx`, written only by the two fvar-pushing chokepoints (`push_local_decl`, `push_let_decl`) — which every in-crate telescope already routes through — and truncated by `lctx_restore`. It travels with `LocalCtxSnapshot` so a metavariable's own context reinstalls its instances. `get_instances` computes the goal's class name up front — before the instance table is taken — and appends matching locals after the priority sort and before the reverse, so locals are tried first, exactly as the oracle's back-to-front consumption does.

**Tech Stack:** Rust (workspace crates `leanr_meta`, `leanr_kernel`), Lean 4 fixture dumper (`tests/fixtures/meta/dump_synth.lean`), `mise` task runner, `serde_json` in the test harness.

**Spec:** `docs/superpowers/specs/2026-09-09-local-instances-design.md`

**Branch:** `local-instances` (already created; the design doc and Amendment 8 are committed there as `fa2f657`).

## Global Constraints

- **Oracle pin:** `leanprover/lean4:v4.33.0-rc1` — the `lean-toolchain` version, which is what Mathlib pins. Every citation in this plan is against that source tree. Never bump the pin.
- **Kernel TCB is strictly untouched.** `leanr_kernel` gains no field, no variant, no behavior change. In particular `LocalDecl` (`crates/leanr_kernel/src/local_ctx.rs:37-43`) does **not** grow a kind/implementation-detail field — see Task 4.
- **`leanr_elab/src` is untouched by this slice.** The producer wiring is M4b-3 P5's. The one exception the spec pre-authorizes (§ One prediction, written down in advance) is an additive fix to a seam that a *measured* regression names, following Amendment 7's precedent — and taking it requires saying so in the commit message with the measurement that forced it.
- **`leanr_meta/src` change is non-additive** (`get_instances`' result changes) and is flagged as such per the M4b accessor precedent, with the rejected alternative recorded in the spec (§ Where it lives) and the neutrality gate in Task 9.
- **Untrusted input discipline unchanged:** no new `.olean` decoder is added. Local instances never touch `instanceExtension` and are never serialized.
- **Every discriminator is measured.** For each test, apply the named mutation, watch it go red, revert. **A brief that names a mutation is not a brief that has run it** — on a recent slice, four of five task briefs named mutations their tests did not kill, including one permanently vacuous assertion. If a mutation survives, the test is wrong: strengthen it and say so in the commit message. Never mark a step done on the strength of this document's claim alone.
- **`mise run ci` before every commit and push.** It gates `cargo fmt --check` and clippy, not only tests; the test tasks do not cover formatting.
- **No workflow changes.** Neither Mathlib sweep, nor the typeclass-synthesis nightly, nor any file under `.github/workflows/` is touched.
- **Fixture regeneration** is `mise run fixtures:regen`. `Synth0.olean` is regenerated in Tasks 1 and 8, and only after the dumper or `Synth0.lean` changes.

## File Structure

**Created:**

| File | Responsibility |
|---|---|
| `crates/leanr_meta/src/local_instance.rs` | The `LocalInstance` record and the sparse stack's push/truncate logic. One responsibility: *what is in scope*. Kept out of `metactx.rs` (already 1300+ lines) so the scoping rules are readable in one screen. |

**Modified:**

| File | Change |
|---|---|
| `crates/leanr_meta/src/metactx.rs` | the `local_instances` field, its truncation in `lctx_restore`, installation in `push_local_decl`/`push_let_decl`, `install_lctx`/`with_mvar_context` carrying instances, `is_class` |
| `crates/leanr_meta/src/local_snapshot.rs` | `LocalCtxSnapshot` grows a third component; `parts`, `new`, `empty`, `reduced` all carry it |
| `crates/leanr_meta/src/instances.rs` | `ClassTable::is_class_name`; the `get_instances` append; the `global_name: None` module-doc rewrite |
| `crates/leanr_meta/src/assign.rs` | **test only.** `forall_bounded_telescope` already mints its fvars through `push_local_decl` (`:645`), so it needs no edit; Task 4 pins that with a test rather than assuming it |
| `crates/leanr_meta/src/synth.rs` | a pin (test + comment) that a local's fvar `val` passes through `mk_const_with_fresh_mvar_levels` unchanged |
| `crates/leanr_meta/src/lib.rs` | `mod local_instance;` |
| `tests/fixtures/meta/dump_synth.lean` | the `fvars` record field and the local-context query builders |
| `tests/fixtures/meta/Synth0.lean` | declarations the new records need |
| `tests/fixtures/meta/synth-queries.jsonl` | new records (regenerated, never hand-edited) |
| `crates/leanr_meta/tests/oracle_synth.rs` | replay of the `fvars` field |

---

### Task 1: The `fvars` record field — the verification channel

**Why first:** the synth record shape has no way to express a goal under a non-empty local context (`goal` / `mvars` / `assigns` / `val` / `ok`, `dump_synth.lean:23-32`). With no local context there is no class-typed fvar, so there is no local instance to verify at all — every later task's differential coverage depends on this one. The elaborator tier cannot substitute: its only producer of a class-typed binder is M4b-3 P5, which comes *after* this slice.

This task adds the channel and proves it round-trips using a record that needs **no local-instance code at all** — an fvar in scope whose presence must not change the answer. That ordering is deliberate: if this record is green before Task 2, then any later red is attributable to local-instance behavior and not to the harness.

**Files:**
- Modify: `tests/fixtures/meta/dump_synth.lean` (record-shape header at `:23-32`; the query list)
- Modify: `crates/leanr_meta/tests/oracle_synth.rs` (replay, around the `mvars` decode at `:142-196`)
- Modify: `tests/fixtures/meta/synth-queries.jsonl` (regenerated)

**Interfaces:**
- Produces: the record field `"fvars": [ {"i":<N>, "t":<E>, "bi":"default"|"implicit"|"strictImplicit"|"instImplicit", "v":<E>?} ]`, ordered by `i` ascending, where an entry's type may reference any *earlier* entry's fvar, and `"v"` present means a let-declaration. Replay binds index `i` to the fvar that `push_local_decl`/`push_let_decl` returns, so the record's `goal` decodes against declarations that really exist.
- Consumes: nothing from earlier tasks.

- [ ] **Step 1: Extend the record-shape documentation in the dumper**

In `tests/fixtures/meta/dump_synth.lean`, the header block at `:23-32` currently reads:

```
Record shape (one per curated query):
  { "id"   : "<tag>/synth/<i>"
  , "q"    : "synth"
  , "goal" : <E>                     -- the synthesis goal type
  , "mvars": [ {"i":<N>, "t":<E>} ]  -- goal mvars: canonical index + TYPE
  , "ok"   : true|false              -- oracle verdict
  , "val"  : <E>                     -- present iff ok; the instance TERM
  , "assigns": [ {"i":<N>, "e":<E>} ]  -- post-synthesis assignments
  , "near_budget": true|false        -- see below
  }
```

Add the `fvars` line and its explanation immediately after `mvars`:

```
  , "fvars": [ {"i":<N>, "t":<E>, "bi":<S>, "v":<E>} ]
                                     -- the LOCAL CONTEXT the goal is
                                     -- asked in: canonical index, TYPE,
                                     -- binder info, and (let-decls only)
                                     -- the VALUE. Ascending by `i`;
                                     -- entry `i`'s type may mention any
                                     -- fvar `j < i`. Absent/empty means
                                     -- the goal is asked at top level,
                                     -- which is every record committed
                                     -- before the local-instances slice.
```

and, below the existing `mvars` rationale, this paragraph:

```
`fvars` exists for the same reason `mvars` does — the canonical expr
scheme numbers free variables but carries no way to declare them, so a
replayed `{"k":"fvar","i":0}` would otherwise denote a variable in no
local context. It is ALSO the local-instances slice's only differential
channel: a local instance is an fvar whose type is a class, so without a
declarable local context the mechanism has no source producer at this
tier (the elaborator's is M4b-3 P5, which lands after). `bi` is carried
because a local instance's `synthOrder` is read off the INSTANCE-IMPLICIT
binders of its own type (`SynthInstance.lean:231-238`); a round trip that
dropped binder info could not reconstruct it.
```

- [ ] **Step 2: Emit the field from the dumper**

The dumper's query builders run in `MetaM` (`dump_synth.lean:180-182`), so a query can open a scope. Add this helper next to the existing encode helpers, and a `fvars` emission in the record writer.

The builder type becomes a pair of "declarations to open" and "the goal, in that scope". Add above the query list:

```lean
/-- One local declaration a query asks its goal under. `value?` present
means a let-declaration (`withLetDecl`), absent means a cdecl
(`withLocalDecl`). Both install local instances in the oracle
(`Basic.lean:1791`, `:1905-1911`, both via `withNewFVar`), which is
exactly what the local-instances records need to observe. -/
structure FVarSpec where
  userName : Name
  bi       : BinderInfo
  type     : MetaM Expr
  value?   : Option (MetaM Expr) := none

/-- Open `specs` in order — each type is elaborated INSIDE the scope of
the ones before it, so entry `i`'s type may mention entry `j < i` — then
run `k` with the opened fvars. -/
private partial def withFVarSpecs (specs : List FVarSpec) (acc : Array Expr)
    (k : Array Expr → MetaM α) : MetaM α := do
  match specs with
  | [] => k acc
  | s :: rest =>
    let ty ← s.type
    match s.value? with
    | none =>
      withLocalDecl s.userName s.bi ty fun x =>
        withFVarSpecs rest (acc.push x) k
    | some mkVal =>
      let v ← mkVal
      withLetDecl s.userName ty v fun x =>
        withFVarSpecs rest (acc.push x) k
```

In the record writer, encode the opened fvars **before** `goal`, so the
canonical numbering assigns them indices `0..n-1` in declaration order
and `goal`'s own references resolve to those indices:

```lean
      -- `fvars` is encoded FIRST, before `goal`, so declaration order
      -- and canonical fvar numbering agree: entry `i` is fvar `i`. The
      -- numbering state `st` is threaded exactly the way the existing
      -- `goal` -> `mvars[].t` -> `val` chain threads it.
      let (fvarsJ, st0) ← fvarSpecs.foldlM (fun (acc, st) (x, bi, val?) => do
        let ty ← inferType x
        let (tJ, st') := encodeExpr (← instantiateMVars ty) st
        let (xJ, st'') := encodeExpr x st'
        let i := match xJ.getObjVal? "i" with
          | some v => v
          | none   => panic! "encodeExpr of an fvar did not produce an index"
        let (vJ, st''') ← match val? with
          | none   => pure (none, st'')
          | some v => do
            let (vJ, stv) := encodeExpr (← instantiateMVars v) st''
            pure (some vJ, stv)
        let entry := Json.mkObj <|
          [("i", i), ("t", tJ), ("bi", Json.str (binderInfoName bi))]
          ++ (match vJ with | some vJ => [("v", vJ)] | none => [])
        pure (acc.push entry, st'''))
        (#[], {})
```

with the binder-info spelling matching the four `BinderInfo`
constructors:

```lean
private def binderInfoName : BinderInfo → String
  | .default        => "default"
  | .implicit       => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit   => "instImplicit"
```

and `("fvars", Json.arr fvarsJ)` added to the emitted object, threading
`st0` into the existing `goal` encode in place of the empty state.

- [ ] **Step 3: Add the one channel record**

Add to the curated query list a record that puts a **non-class** fvar in
scope and asks a goal that a global instance already answers. Its whole
job is to prove the channel round-trips; it must be green *before* any
local-instance code exists, and must stay green after.

```lean
  * `fvarCtx`     — `Add N` asked with `(x : N)` in scope. `N` is not a
                    class, so no local instance exists either before or
                    after the local-instances slice, and the answer is
                    `instAddN` both ways. The record's job is the
                    CHANNEL: it pins that a declared local context round
                    trips through `fvars` and that a goal decoded against
                    it resolves its fvar references to real declarations.
```

with the query entry:

```lean
  ( "fvarCtx"
  , [ { userName := `x, bi := .default, type := pure (mkConst ``N) } ]
  , fun _ => pure (mkApp (mkConst ``Add [levelZero]) (mkConst ``N)) )
```

- [ ] **Step 4: Replay the field**

In `crates/leanr_meta/tests/oracle_synth.rs`, the goal is decoded at
`:142` with `fv` as the fvar-index map. Local declarations must be pushed
**before** that decode, seeding `fv` so `{"k":"fvar","i":0}` resolves to
the declaration rather than minting a dangling name.

Insert immediately before the `let goal = decode_expr(...)` line:

```rust
        // The local context the goal is asked in (local-instances
        // slice). Pushed BEFORE `goal` is decoded, and seeded into `fv`,
        // so the goal's own `{"k":"fvar","i":N}` references resolve to
        // declarations that really exist rather than to freshly interned
        // dangling names. Ascending by `i`, because entry `i`'s type may
        // mention any earlier entry.
        //
        // These go through `push_local_decl`/`push_let_decl` — the very
        // chokepoints that install local instances — so the fixture's
        // local context IS the producer under test. There is no
        // test-only path that could install an instance a real run
        // would not.
        let empty_fvars = Vec::new();
        let fvar_specs = q
            .get("fvars")
            .and_then(|v| v.as_array())
            .unwrap_or(&empty_fvars);
        let lctx_cp = ctx.lctx_checkpoint();
        for spec in fvar_specs {
            let idx = spec["i"].as_u64().expect("fvars[].i field");
            let ty = decode_expr(&mut scratch, base, &spec["t"], &mut fv, &mut mv);
            let bi = match spec["bi"].as_str().expect("fvars[].bi field") {
                "default" => BinderInfo::Default,
                "implicit" => BinderInfo::Implicit,
                "strictImplicit" => BinderInfo::StrictImplicit,
                "instImplicit" => BinderInfo::InstImplicit,
                other => panic!("{id}: unknown binder info {other:?}"),
            };
            let name = synth_name(&mut scratch, base, "#f", idx);
            let fvar = match spec.get("v") {
                None => ctx
                    .push_local_decl(Some(name), ty, bi)
                    .unwrap_or_else(|e| panic!("{id}: push_local_decl: {e:?}")),
                Some(v) => {
                    let value = decode_expr(&mut scratch, base, v, &mut fv, &mut mv);
                    ctx.push_let_decl(Some(name), ty, value)
                        .unwrap_or_else(|e| panic!("{id}: push_let_decl: {e:?}"))
                }
            };
            let nid = match ctx.node(fvar) {
                Node::FVar { id: Some(id) } => id,
                other => panic!("{id}: push returned a non-fvar {other:?}"),
            };
            // Seed the decode map so `goal` resolves index -> this decl.
            let previous = fv.insert(idx, nid);
            assert!(
                previous.is_none(),
                "{id}: fvars[].i={idx} is declared twice, or `goal` was \
                 decoded before the context was pushed"
            );
        }
```

and, after the record's assertions complete, restore:

```rust
        ctx.lctx_restore(lctx_cp);
```

`synth_name` is the helper `decode_expr` itself uses for fvar names
(`crates/leanr_meta/tests/support/mod.rs:379-382`); export it from
`support` if it is not already `pub(crate)`.

`BinderInfo` and `Node` come from `leanr_kernel`:

```rust
use leanr_kernel::bank::terms::Node;
use leanr_kernel::BinderInfo;
```

- [ ] **Step 5: Regenerate the fixture and run**

```bash
mise run fixtures:regen
cargo test -p leanr_meta --test oracle_synth
```

Expected: PASS, with the corpus at **27** records (26 committed + the new
`fvarCtx/synth/0`). Every pre-existing record must be **byte-identical** —
the `fvars` field is emitted as an empty array (or omitted) for all of
them, and adding a field to records that had none would show up as a
whole-file diff.

Verify that explicitly rather than trusting it:

```bash
git diff --stat tests/fixtures/meta/synth-queries.jsonl
```

Expected: exactly one line added, no lines modified. **If existing lines
changed, stop** — the encoder is emitting `fvars` unconditionally, and
the fix is to omit the key when the list is empty, not to re-baseline.

- [ ] **Step 6: Measure the discriminator**

Mutation: in `oracle_synth.rs`, skip the `fv.insert(idx, nid)` seeding
(so the goal's fvar reference decodes to a fresh dangling name instead of
the pushed declaration).

```bash
cargo test -p leanr_meta --test oracle_synth 2>&1 | tail -20
```

Expected: `fvarCtx/synth/0` goes **RED**. Revert the mutation.

If it stays green, the record is not exercising the channel — the most
likely cause is that the goal does not actually mention the fvar. Fix the
record so the goal mentions it (see Task 9's `noInstLocal`, which does),
and say so in the commit message.

- [ ] **Step 7: Commit**

```bash
mise run ci
git add tests/fixtures/meta/dump_synth.lean tests/fixtures/meta/synth-queries.jsonl crates/leanr_meta/tests/oracle_synth.rs crates/leanr_meta/tests/support/mod.rs
git commit -m "$(cat <<'MSG'
synth fixture: declare a local context per record (`fvars`)

The synth record could express a goal and its metavariables but not the
local context the goal is asked in, so a class-typed fvar — and therefore
a local instance — had no source producer at this tier. The elaborator
tier cannot substitute: its only producer is M4b-3 P5, which lands after
this slice.

Replay pushes the declared context through `push_local_decl` /
`push_let_decl`, the same chokepoints that will install local instances,
so the fixture's local context is the producer under test rather than a
test-only path.

`fvarCtx/synth/0` is the channel record: a non-class fvar in scope, whose
presence must not change the answer. Green before any local-instance code
exists, so a later red is attributable to behavior and not to harness.

Claude-Session: https://claude.ai/code/session_01MdUSj32wrx862QVNCypLnh
MSG
)"
```

---
### Task 2: `LocalInstance` and the sparse scope stack

**Files:**
- Create: `crates/leanr_meta/src/local_instance.rs`
- Modify: `crates/leanr_meta/src/lib.rs` (add `mod local_instance;`)
- Modify: `crates/leanr_meta/src/metactx.rs` (the field; `lctx_restore` at `:600-610`)

**Interfaces:**
- Produces: `LocalInstance { class_name: NameId, fvar: ExprId, at_depth: usize }` and `LocalInstanceStack` with `push(class_name, fvar, at_depth)`, `truncate_to(depth)`, `entries() -> &[LocalInstance]`, `replace(Vec<LocalInstance>)`, and `to_vec()`. `MetaCtx` gains `pub(crate) local_instances: LocalInstanceStack`.
- Consumes: nothing.

**The one subtlety.** `MetaCtx::local_names` (`metactx.rs:80`) is in **lockstep** with `lctx.decls` — one entry per push — so `lctx_restore` truncates it by the same index and a `debug_assert` guards it. `local_instances` is **sparse**: only class-typed declarations produce an entry. Index-truncation would therefore drop the wrong entries. Each entry records the `lctx` depth it was pushed at (which is the declaration's own index), and truncation pops while that depth is `>= checkpoint`. This keeps `lctx_checkpoint`'s `usize` return type unchanged, so no call site churns.

- [ ] **Step 1: Write the failing test**

Create `crates/leanr_meta/src/local_instance.rs` with the module doc and the test, but **no** implementation yet:

```rust
#[cfg(test)]
mod tests {
    use super::*;
    use leanr_kernel::bank::NameId;

    fn nid(i: u32) -> NameId {
        NameId::from_index(i, false).expect("a small index is a valid NameId")
    }
    fn eid(i: u32) -> ExprId {
        ExprId::from_index(i).expect("a small index is a valid ExprId")
    }

    /// Truncation is by RECORDED DEPTH, not by index. The stack is
    /// sparse — only class-typed declarations produce an entry — so an
    /// index-based `truncate(checkpoint)` drops the wrong entries
    /// whenever a non-class declaration sits between two instances,
    /// which is the ordinary case (`fun (n : Nat) [inst : C n] => …`).
    #[test]
    fn truncate_to_pops_by_recorded_depth_not_by_index() {
        let mut s = LocalInstanceStack::default();
        // lctx depths 0..5, with instances only at 1 and 4 — depths 0,
        // 2, 3 are ordinary non-class binders that push nothing here.
        s.push(nid(10), eid(1), 1);
        s.push(nid(11), eid(4), 4);
        assert_eq!(s.entries().len(), 2);

        // Restoring to depth 5 keeps both: neither was pushed at or
        // after 5.
        s.truncate_to(5);
        assert_eq!(s.entries().len(), 2, "nothing was pushed at depth >= 5");

        // Restoring to depth 4 drops exactly the one pushed AT depth 4.
        s.truncate_to(4);
        assert_eq!(
            s.entries().iter().map(|e| e.fvar).collect::<Vec<_>>(),
            vec![eid(1)],
            "the entry pushed at depth 4 is out of scope once lctx is \
             restored to 4; the one at depth 1 is still in scope. An \
             index-based truncate(4) would have kept BOTH, because \
             there are only 2 entries."
        );

        s.truncate_to(0);
        assert!(s.entries().is_empty(), "restoring to top level clears the stack");
    }

    /// `truncate_to` must pop EVERY entry at or above the depth, not
    /// just the last one.
    #[test]
    fn truncate_to_pops_all_entries_at_or_above_the_depth() {
        let mut s = LocalInstanceStack::default();
        s.push(nid(10), eid(1), 1);
        s.push(nid(11), eid(2), 2);
        s.push(nid(12), eid(3), 3);
        s.truncate_to(2);
        assert_eq!(
            s.entries().iter().map(|e| e.fvar).collect::<Vec<_>>(),
            vec![eid(1)],
            "both the depth-2 and depth-3 entries are out of scope"
        );
    }
}
```

- [ ] **Step 2: Run the test to verify it fails**

```bash
cargo test -p leanr_meta local_instance
```

Expected: FAIL to compile — `LocalInstanceStack` is not defined.

- [ ] **Step 3: Write the implementation**

Above the test module in `crates/leanr_meta/src/local_instance.rs`:

```rust
//! Which local instances are in scope.
//!
//! oracle: `LocalInstance` (`MetavarContext.lean:268-273`) — a
//! `className` and an `fvar`, nothing else. The oracle keeps them in a
//! `LocalInstances := Array LocalInstance` threaded through
//! `Meta.Context` and stored on every `MetavarDecl` (`:320`), and it is
//! deliberately NOT part of the `LocalContext` itself: the kernel does
//! not care about instances (`:265-267`), so they live one layer up.
//!
//! # Why this is a separate module
//!
//! `metactx.rs` is already long, and the scoping rule here is the whole
//! subtlety of the slice: this stack is SPARSE where every other
//! parallel index on `MetaCtx` is in lockstep with `lctx.decls`. Keeping
//! the rule in one screen is worth a file.
//!
//! # The scoping rule
//!
//! `MetaCtx::local_names` (`metactx.rs:80`) has exactly one entry per
//! `push_local_decl`/`push_let_decl` call, so `lctx_restore(cp)`
//! truncates it to `cp` and a `debug_assert` keeps the two honest. This
//! stack cannot do that: only a CLASS-TYPED declaration produces an
//! entry, so `entries.len()` bears no relation to `lctx.save()`. Each
//! entry therefore records the `lctx` depth it was pushed at — which is
//! the declaration's own index in `lctx.decls` — and `truncate_to` pops
//! while that depth is `>= checkpoint`. Entries are pushed in
//! increasing depth order (declarations only ever append), so popping
//! from the back terminates at the first survivor.
//!
//! Doing it this way keeps `lctx_checkpoint`'s `usize` return type, so
//! no caller of the checkpoint/restore pair changes.
//!
//! # Dedup is vacuous here
//!
//! `withLocalInstancesImp` (`Basic.lean:1937-1949`) guards against
//! adding the same local instance twice, keyed on `fvarId`. That guard
//! exists for `withLocalInstances`, which RE-registers already-declared
//! decls. leanr's producers are the push chokepoints, which mint a fresh
//! `fvar_gen` id every time, so no fvar can be registered twice and the
//! guard has nothing to guard. Named rather than silently omitted; a
//! future port of `withExistingLocalDecls` (`Basic.lean:1955-1959`)
//! would need it.

use leanr_kernel::bank::{ExprId, NameId};

/// oracle: `LocalInstance` (`MetavarContext.lean:268-273`), plus the
/// scope bookkeeping leanr needs because its local context is a
/// mutate-in-place stack rather than a persistent structure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct LocalInstance {
    pub class_name: NameId,
    pub fvar: ExprId,
    /// The `lctx` depth this entry was pushed at — i.e. the index of its
    /// own declaration in `lctx.decls`. Read only by `truncate_to`. Not
    /// part of the oracle's record: the oracle's `LocalInstances` is a
    /// persistent array captured by `withReader`, so scope exit restores
    /// it for free.
    pub at_depth: usize,
}

/// The in-scope local instances, innermost last.
#[derive(Clone, Debug, Default)]
pub(crate) struct LocalInstanceStack {
    entries: Vec<LocalInstance>,
}

impl LocalInstanceStack {
    pub(crate) fn push(&mut self, class_name: NameId, fvar: ExprId, at_depth: usize) {
        debug_assert!(
            self.entries.last().is_none_or(|e| e.at_depth <= at_depth),
            "local instances must be pushed in non-decreasing depth order; \
             `truncate_to` pops from the back and relies on it"
        );
        self.entries.push(LocalInstance {
            class_name,
            fvar,
            at_depth,
        });
    }

    /// Drop every entry whose declaration is at or above `depth` — the
    /// counterpart of `LocalContext::restore(depth)`.
    pub(crate) fn truncate_to(&mut self, depth: usize) {
        while self.entries.last().is_some_and(|e| e.at_depth >= depth) {
            self.entries.pop();
        }
    }

    pub(crate) fn entries(&self) -> &[LocalInstance] {
        &self.entries
    }

    /// Install a saved set wholesale — `MetaCtx::install_lctx`'s half of
    /// the snapshot swap (Task 5).
    pub(crate) fn replace(&mut self, entries: Vec<LocalInstance>) {
        self.entries = entries;
    }

    pub(crate) fn to_vec(&self) -> Vec<LocalInstance> {
        self.entries.clone()
    }
}
```

Add to `crates/leanr_meta/src/lib.rs`, in the existing `mod` block in alphabetical position:

```rust
mod local_instance;
```

- [ ] **Step 4: Run the test to verify it passes**

```bash
cargo test -p leanr_meta local_instance
```

Expected: PASS, both tests.

- [ ] **Step 5: Wire the field and its truncation**

In `crates/leanr_meta/src/metactx.rs`, add the import:

```rust
use crate::local_instance::{LocalInstance, LocalInstanceStack};
```

Add the field to `struct MetaCtx`, immediately after `local_names`:

```rust
    /// The local instances in scope — oracle: `Meta.Context.localInstances`
    /// (`Basic.lean`), stored per metavariable as
    /// `MetavarDecl.localInstances` (`MetavarContext.lean:320`).
    ///
    /// SPARSE, unlike `local_names` above: only a class-typed
    /// declaration produces an entry, so this length is unrelated to
    /// `lctx.save()` and there is no lockstep invariant to assert. See
    /// `local_instance.rs` for the truncation rule.
    pub(crate) local_instances: LocalInstanceStack,
```

Initialize it in `MetaCtx::new` beside `local_names: Vec::new()`:

```rust
            local_instances: LocalInstanceStack::default(),
```

In `lctx_restore`, add the truncation after the `local_names` truncation:

```rust
        self.lctx.restore(checkpoint);
        self.local_names.truncate(checkpoint);
        // Sparse, so truncated by RECORDED DEPTH rather than by index —
        // see `local_instance.rs`'s module doc.
        self.local_instances.truncate_to(checkpoint);
        self.lctx_snapshot = None;
```

- [ ] **Step 6: Verify the crate still builds and the suite is green**

```bash
cargo test -p leanr_meta
```

Expected: PASS. Nothing reads `local_instances` yet, so behavior is
unchanged; this step is checking that the field and its initializer
compile everywhere `MetaCtx` is constructed.

- [ ] **Step 7: Measure the discriminator**

Mutation: change `truncate_to` to `self.entries.truncate(depth)` (the
index-based version).

```bash
cargo test -p leanr_meta local_instance
```

Expected: `truncate_to_pops_by_recorded_depth_not_by_index` goes **RED**.
Revert.

Second mutation: change the `while` loop's `>=` to `>`.

Expected: the same test goes **RED** (the depth-4 entry survives a
restore to 4). Revert.

- [ ] **Step 8: Commit**

```bash
mise run ci
git add crates/leanr_meta/src/local_instance.rs crates/leanr_meta/src/lib.rs crates/leanr_meta/src/metactx.rs
git commit -m "$(cat <<'MSG'
local instances: the sparse scope stack

`LocalInstance` (oracle: `MetavarContext.lean:268-273`) plus the stack
that tracks which are in scope. No producer and no consumer yet, so
behavior is unchanged.

The stack is SPARSE where `MetaCtx::local_names` is in lockstep with
`lctx.decls`: only a class-typed declaration produces an entry. So it
cannot be truncated by index. Each entry records the `lctx` depth it was
pushed at, and `truncate_to` pops while that depth is >= the checkpoint,
which keeps `lctx_checkpoint`'s `usize` and churns no call site.

Claude-Session: https://claude.ai/code/session_01MdUSj32wrx862QVNCypLnh
MSG
)"
```

---

### Task 3: `is_class`

**Files:**
- Modify: `crates/leanr_meta/src/instances.rs` (`ClassTable`, near `out_params` at `:580`)
- Modify: `crates/leanr_meta/src/metactx.rs` (the `is_class` entry point)

**Interfaces:**
- Consumes: `ClassTable` (already present, built by `MetaCtx::new` at `metactx.rs:328`), `LOption<T>` (`synth.rs:1662-1666`).
- Produces: `ClassTable::is_class_name(&self, NameId) -> bool` and `MetaCtx::is_class(&mut self, ExprId) -> Result<Option<NameId>, MetaError>`.

**Oracle shape.** `isClass?` (`Basic.lean:1542-1543`) is `isClassImp?` with every exception swallowed. `isClassImp?` (`:1524-1528`) runs `isClassQuick?` (`:1358-1381`) — a pure structural walk with **no whnf** — and falls back to `isClassExpensive?` (`:1520-1522`) only on its three `.undef` arms. Getting the cheap path right matters for more than speed: `isClassExpensive?` runs whnf, and whnf must stay off the paths described in Task 6.

- [ ] **Step 1: Write the failing tests**

Append to the `#[cfg(test)] mod tests` in `crates/leanr_meta/src/instances.rs`:

```rust
    /// `isClassQuick?`'s `.forallE` arm recurses into the BODY
    /// (`Basic.lean:1366`): `{a : Type} → [Add a] → Add (Prod a a)` is a
    /// class, because its conclusion is. This is the shape a
    /// parametrized local instance has, so getting it wrong makes every
    /// such binder invisible.
    #[test]
    fn is_class_looks_through_forall_binders() {
        with_class_ctx(|ctx, add| {
            let ty = arrow_to_class(ctx, add);
            assert_eq!(
                ctx.is_class(ty).expect("is_class"),
                Some(add),
                "a forall whose conclusion is a class IS a class"
            );
        });
    }

    /// A non-class head constant is NOT a class, however class-shaped it
    /// looks. Kills a `is_class` that reports the head constant of any
    /// application without consulting the class table.
    #[test]
    fn is_class_rejects_a_non_class_head() {
        with_class_ctx(|ctx, _add| {
            let n = const_named(ctx, "N");
            assert_eq!(
                ctx.is_class(n).expect("is_class"),
                None,
                "`N` is a type, not a class — a constant-true is_class \
                 would register every binder as a local instance"
            );
        });
    }

    /// `isClassQuick?`'s `.sort`/`.lam`/`.lit`/`.fvar`/`.bvar` arms
    /// return `.none` OUTRIGHT (`Basic.lean:1359-1363`) — they never
    /// reach the expensive path. A port that fell through to
    /// `isClassExpensive?` here would run whnf on shapes the oracle
    /// never whnfs.
    #[test]
    fn is_class_rejects_a_sort_without_reducing() {
        with_class_ctx(|ctx, _add| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");
            assert_eq!(ctx.is_class(sort0).expect("is_class"), None);
        });
    }
```

Write the two helpers `with_class_ctx` (a `with_ctx` that builds a
`ClassTable` containing one entry, `Add`) and `arrow_to_class` (interning
`N → Add N`) alongside, following the existing `with_instances_ctx` /
`const_named` helpers in the same test module — read
`crates/leanr_meta/src/instances.rs:790-830` for the pattern before
writing them.

- [ ] **Step 2: Run to verify failure**

```bash
cargo test -p leanr_meta is_class
```

Expected: FAIL to compile — `MetaCtx::is_class` does not exist.

- [ ] **Step 3: Implement `ClassTable::is_class_name`**

In `crates/leanr_meta/src/instances.rs`, beside `out_params` (`:580`):

```rust
    /// Is `class_name` a registered type class? oracle:
    /// `isClass env declName` (`Basic.lean:1512`), reading the same
    /// `classExtension` this table is built from.
    ///
    /// Membership is `out_params(..).is_some()`, not "has output
    /// parameters": every class gets a `classExtension` entry whether or
    /// not it declares any, and a class with none has an entry with an
    /// EMPTY slice. Reading emptiness as absence would make every
    /// ordinary class invisible.
    pub(crate) fn is_class_name(&self, class_name: NameId) -> bool {
        self.out_params(class_name).is_some()
    }
```

- [ ] **Step 4: Implement `MetaCtx::is_class`**

In `crates/leanr_meta/src/metactx.rs`:

```rust
    /// oracle: `isClass?` (`Basic.lean:1542-1543`) — `isClassImp?` with
    /// every exception swallowed (`try … catch _ => return none`). The
    /// swallow is modelled as error → `None` rather than propagated: a
    /// failure to decide makes something not-a-class, never a hard
    /// error, and diverging here would turn an ordinary binder into an
    /// elaboration failure.
    pub(crate) fn is_class(&mut self, ty: ExprId) -> Result<Option<NameId>, MetaError> {
        match self.is_class_quick(ty) {
            LOption::Some(c) => Ok(Some(c)),
            LOption::None => Ok(None),
            LOption::Undef => Ok(self.is_class_expensive(ty).unwrap_or(None)),
        }
    }

    /// oracle: `isClassQuick?` (`Basic.lean:1358-1381`) — a purely
    /// structural walk that NEVER reduces. Keeping it whnf-free is not
    /// only a speed matter: `get_instances` calls `is_class` while its
    /// instance table is `mem::take`n (`instances.rs:468-479`), so a
    /// reduction on the common path would re-enter instance lookup
    /// against an empty table.
    fn is_class_quick(&mut self, ty: ExprId) -> LOption<NameId> {
        match self.node(ty) {
            // `:1359-1363` — outright `.none`, never the expensive path.
            Node::BVar { .. }
            | Node::BVarBig { .. }
            | Node::Lit { .. }
            | Node::FVar { .. }
            | Node::Sort { .. }
            | Node::Lam { .. } => LOption::None,
            // `:1364-1365` — `.undef`: deciding needs reduction.
            Node::LetE { .. } | Node::Proj { .. } => LOption::Undef,
            // `:1366` — look THROUGH the binder at the conclusion.
            Node::Forall { body, .. } => self.is_class_quick(body),
            Node::MData { expr, .. } => self.is_class_quick(expr),
            Node::Const { name, .. } => self.is_class_quick_const(name),
            // `:1369-1372` — an assigned mvar is its value; unassigned
            // is `.none`.
            Node::MVar { id } => match id.and_then(|n| self.mctx.assignment(MVarId(n))) {
                Some(v) => self.is_class_quick(v),
                None => LOption::None,
            },
            // `:1374-1381` — the head of the application decides.
            Node::App { .. } => match self.node(self.app_fn(ty)) {
                Node::Const { name, .. } => self.is_class_quick_const(name),
                Node::Lam { .. } => LOption::Undef,
                Node::MVar { id } => match id.and_then(|n| self.mctx.assignment(MVarId(n))) {
                    Some(v) => match self.node(self.app_fn(v)) {
                        Node::Const { name, .. } => self.is_class_quick_const(name),
                        _ => LOption::Undef,
                    },
                    None => LOption::None,
                },
                _ => LOption::None,
            },
        }
    }

    fn is_class_quick_const(&self, name: Option<NameId>) -> LOption<NameId> {
        match name {
            Some(n) if self.classes.is_class_name(n) => LOption::Some(n),
            // oracle: `isClassQuickConst?` returns `.undef` for a
            // constant that is not a class but COULD unfold to one; the
            // expensive path is what decides. Returning `.none` here
            // would skip reducible definitions that abbreviate a class.
            Some(_) => LOption::Undef,
            None => LOption::None,
        }
    }

    /// oracle: `isClassExpensive?` (`Basic.lean:1520-1522`) —
    /// `withReducible`, telescope the foralls to the conclusion with
    /// `whnfType := true`, then `isClassApp?` (`:1509-1518`): the head
    /// constant, if the environment says it is a class.
    fn is_class_expensive(&mut self, ty: ExprId) -> Result<Option<NameId>, MetaError> {
        self.with_transparency(TransparencyMode::Reducible, |ctx| {
            let cp = ctx.lctx_checkpoint();
            let mut cur = ctx.whnf(ty)?;
            while let Node::Forall { body, .. } = ctx.node(cur) {
                cur = ctx.whnf(body)?;
            }
            ctx.lctx_restore(cp);
            Ok(match ctx.node(ctx.app_fn(cur)) {
                Node::Const { name: Some(n), .. } if ctx.classes.is_class_name(n) => Some(n),
                _ => None,
            })
        })
    }
```

Add the imports `use crate::local_instance::…` (already added in Task 2),
`use crate::synth::LOption;` and `use crate::MVarId;` if not present.

**Read before writing:** `app_fn` may be spelled differently in
`leanr_meta` than in `leanr_elab` (`app/args.rs` has its own). Grep for
the spine-head helper in `crates/leanr_meta/src/` and use the existing
one rather than adding a second.

**Note on `isClassQuickConst?`:** the exact oracle body is at
`Basic.lean` just above `isClassQuick?`. Read it and transcribe its arms
literally rather than trusting the sketch above — it distinguishes "not a
class, cannot unfold" from "not a class, might unfold", and collapsing
the two changes which shapes reach the expensive path.

- [ ] **Step 5: Run to verify the tests pass**

```bash
cargo test -p leanr_meta is_class
cargo test -p leanr_meta
```

Expected: PASS, and the whole crate still green — nothing consumes
`is_class` yet.

- [ ] **Step 6: Measure the discriminators**

| Mutation | Expected red |
|---|---|
| `is_class_name` returns `self.out_params(n).is_some_and(\|p\| !p.is_empty())` | `is_class_looks_through_forall_binders` (Add has no outParams) |
| `is_class_quick`'s `Forall` arm returns `LOption::None` | `is_class_looks_through_forall_binders` |
| `is_class_quick_const` returns `LOption::Some(n)` for any `Some(n)` | `is_class_rejects_a_non_class_head` |
| `is_class_quick`'s `Sort` arm returns `LOption::Undef` | `is_class_rejects_a_sort_without_reducing` — **only if** the expensive path would answer differently; if this one survives, the test is not discriminating and must be rewritten to assert no reduction occurred (e.g. by asserting a step-counter delta), not merely the `None` result |

Run each, confirm red, revert. The fourth row is flagged because it is
exactly the shape that has produced non-discriminating tests in this repo
before: `None` is the right answer on **both** paths, so the result alone
cannot tell them apart.

- [ ] **Step 7: Commit**

```bash
mise run ci
git add crates/leanr_meta/src/instances.rs crates/leanr_meta/src/metactx.rs
git commit -m "$(cat <<'MSG'
local instances: `is_class`

oracle: `isClass?` (`Basic.lean:1542-1543`) — `isClassQuick?`'s
structural walk with `isClassExpensive?` behind its three `.undef` arms,
and every exception swallowed to `None`.

Keeping the quick path whnf-free is load-bearing beyond speed:
`get_instances` will call `is_class` while its instance table is
`mem::take`n (`instances.rs:468-479`), so reducing on the common path
would re-enter instance lookup against an empty table.

Membership is `out_params(..).is_some()`, not "has output parameters" —
every class has a `classExtension` entry, and one with no outParams has
an entry with an empty slice.

Claude-Session: https://claude.ai/code/session_01MdUSj32wrx862QVNCypLnh
MSG
)"
```

---

### Task 4: Install at the push chokepoints

**Files:**
- Modify: `crates/leanr_meta/src/metactx.rs` (`push_local_decl` at `:619`, `push_let_decl` at `:653`)

**Interfaces:**
- Consumes: `MetaCtx::is_class` (Task 3), `LocalInstanceStack::push` (Task 2).
- Produces: the invariant that after any `push_local_decl`/`push_let_decl` of a class-typed declaration, `self.local_instances.entries()` has a matching entry.

**Why this covers the telescopes for free.** The oracle installs at three places — `withLocalDeclImp` (`Basic.lean:1791`), `withLetDeclImp` (`:1905-1911`), both via `withNewFVar` (`:1785-1789`), and `forallTelescopeReducingAux` via `withNewLocalInstancesImp` (`:1472`, `:1477`). leanr's `assign.rs::forall_bounded_telescope` (`:614-647`) already mints its fvars **through `push_local_decl`** (`:645`), and the metavariable-local-contexts slice made that true of every in-crate telescope (`metactx.rs:60-75` documents the change and why). So installing at the two push functions covers the third site with no separate edit — but that is a claim about current call sites, so Step 4 below **measures** it instead of asserting it.

- [ ] **Step 1: Write the failing tests**

In `crates/leanr_meta/src/metactx.rs`'s test module:

```rust
    /// A class-typed binder becomes a local instance; a non-class binder
    /// does not. oracle: `withNewFVar` (`Basic.lean:1785-1789`).
    #[test]
    fn pushing_a_class_typed_decl_installs_a_local_instance() {
        with_class_ctx(|ctx, add| {
            let add_n = class_app(ctx, add);
            let n = const_named(ctx, "N");

            let cp = ctx.lctx_checkpoint();
            let _plain = ctx.push_local_decl(None, n, BinderInfo::Default).expect("push");
            assert!(
                ctx.local_instances.entries().is_empty(),
                "`(x : N)` is not a class-typed binder"
            );

            let inst = ctx
                .push_local_decl(None, add_n, BinderInfo::InstImplicit)
                .expect("push");
            assert_eq!(ctx.local_instances.entries().len(), 1);
            assert_eq!(ctx.local_instances.entries()[0].class_name, add);
            assert_eq!(ctx.local_instances.entries()[0].fvar, inst);

            ctx.lctx_restore(cp);
            assert!(
                ctx.local_instances.entries().is_empty(),
                "restoring the local context takes the instance out of scope"
            );
        });
    }

    /// Binder info does NOT gate installation: the oracle's
    /// `withNewFVar` consults `isClass?` on the TYPE and nothing else,
    /// so a class-typed EXPLICIT binder is a local instance too
    /// (`fun (inst : Add N) => …`). A port that gated on
    /// `BinderInfo::InstImplicit` would silently lose those.
    #[test]
    fn a_class_typed_explicit_binder_is_also_a_local_instance() {
        with_class_ctx(|ctx, add| {
            let add_n = class_app(ctx, add);
            let cp = ctx.lctx_checkpoint();
            ctx.push_local_decl(None, add_n, BinderInfo::Default).expect("push");
            assert_eq!(
                ctx.local_instances.entries().len(),
                1,
                "installation keys on the TYPE, never on the binder info"
            );
            ctx.lctx_restore(cp);
        });
    }

    /// oracle: `withLetDeclImp` (`Basic.lean:1905-1911`) routes through
    /// the same `withNewFVar`, so a let-bound instance counts.
    #[test]
    fn pushing_a_class_typed_let_decl_installs_a_local_instance() {
        with_class_ctx(|ctx, add| {
            let add_n = class_app(ctx, add);
            let val = const_named(ctx, "instAddN");
            let cp = ctx.lctx_checkpoint();
            ctx.push_let_decl(None, add_n, val).expect("push");
            assert_eq!(ctx.local_instances.entries().len(), 1);
            ctx.lctx_restore(cp);
        });
    }
```

- [ ] **Step 2: Run to verify failure**

```bash
cargo test -p leanr_meta local_instance
```

Expected: all three FAIL — no entry is installed.

- [ ] **Step 3: Implement**

In `push_local_decl`, after `self.local_names.push((name, fvar));` and
before `self.lctx_snapshot = None;`:

```rust
        // oracle: `withLocalDeclImp` → `withNewFVar`
        // (`Basic.lean:1791`, `:1785-1789`) — a class-typed declaration
        // becomes a local instance. Keyed on the TYPE only; binder info
        // plays no part, so `fun (inst : Add N) => …` counts exactly as
        // `[inst : Add N]` does.
        //
        // `depth` is read BEFORE the push above, so it is this
        // declaration's own index in `lctx.decls` — see
        // `local_instance.rs` for why the stack truncates by depth.
        self.install_local_instance_for(fvar, ty, depth)?;
```

with `let depth = self.lctx.save();` captured at the top of the function,
before `mk_local_decl` runs, and the shared helper:

```rust
    /// Install `fvar` as a local instance if its type is a class.
    ///
    /// oracle: `withNewFVar` (`Basic.lean:1785-1789`). The oracle's
    /// implementation-detail filter (`withNewLocalInstanceImp`,
    /// `:1383-1388`) is **vacuously satisfied** here: leanr's
    /// `LocalDecl` (`leanr_kernel/src/local_ctx.rs:37-43`) carries no
    /// kind field, and nothing in leanr mints an implementation-detail
    /// declaration, so there is nothing to filter. Adding a field to a
    /// kernel struct for a producer that does not exist would widen the
    /// TCB for nothing. SEAM — trigger for revisiting: the slice that
    /// builds the tactic framework or the match compiler is the first to
    /// mint one, and it must add the filter in the same change.
    fn install_local_instance_for(
        &mut self,
        fvar: ExprId,
        ty: ExprId,
        depth: usize,
    ) -> Result<(), MetaError> {
        if let Some(class_name) = self.is_class(ty)? {
            self.local_instances.push(class_name, fvar, depth);
        }
        Ok(())
    }
```

Make the same call in `push_let_decl`, with its own pre-push `depth`.

**Ordering caution:** `is_class` can run `whnf` on its expensive path,
and whnf reads the ambient local context. Call it **after** the
declaration is in `lctx` (as written above), matching the oracle, whose
`withNewFVar` runs inside the `withReader` that already installed the
decl (`Basic.lean:1791-1796`, `:1905-1911`).

- [ ] **Step 4: Run, and measure the telescope claim**

```bash
cargo test -p leanr_meta
```

Expected: PASS.

Now **measure** the "telescopes are covered for free" claim rather than
trusting it. Add this test:

```rust
    /// `forall_bounded_telescope` mints its fvars through
    /// `push_local_decl` (`assign.rs:645`), so it installs local
    /// instances with no separate wiring — the counterpart of the
    /// oracle's `withNewLocalInstancesImp` at
    /// `forallTelescopeReducingAux` (`Basic.lean:1472`, `:1477`). This
    /// test exists because that is a claim about CURRENT call sites: if
    /// a future change makes a telescope bypass the chokepoint, the
    /// instances silently stop being installed and nothing else would
    /// notice.
    #[test]
    fn a_telescope_installs_local_instances_for_its_binders() {
        with_class_ctx(|ctx, add| {
            // `Add N → N`: one instance-typed binder.
            let ty = forall_over_class(ctx, add);
            let cp = ctx.lctx_checkpoint();
            let xs = ctx.forall_bounded_telescope(ty, 1).expect("telescope");
            assert_eq!(xs.len(), 1);
            assert_eq!(
                ctx.local_instances.entries().len(),
                1,
                "the telescope's binder is class-typed, so it is in scope \
                 as a local instance while the telescope is open"
            );
            ctx.lctx_restore(cp);
            assert!(ctx.local_instances.entries().is_empty());
        });
    }
```

`forall_bounded_telescope` is private to `assign.rs`; put this test
there, or widen it to `pub(crate)` if `assign.rs`'s test module cannot
reach the helpers — prefer moving the test.

- [ ] **Step 5: Measure the discriminators**

| Mutation | Expected red |
|---|---|
| `install_local_instance_for` returns `Ok(())` immediately | all four tests |
| gate installation on `bi == BinderInfo::InstImplicit` | `a_class_typed_explicit_binder_is_also_a_local_instance` |
| drop the call from `push_let_decl` only | `pushing_a_class_typed_let_decl_installs_a_local_instance` |
| capture `depth` AFTER the push instead of before | `pushing_a_class_typed_decl_installs_a_local_instance`'s restore assertion (the entry is recorded one deeper than its decl, so a restore to the checkpoint leaves it behind) |

Run each, confirm red, revert.

- [ ] **Step 6: Commit**

```bash
mise run ci
git add crates/leanr_meta/src/metactx.rs crates/leanr_meta/src/assign.rs
git commit -m "$(cat <<'MSG'
local instances: install at the push chokepoints

oracle: `withLocalDeclImp` and `withLetDeclImp`, both via `withNewFVar`
(`Basic.lean:1791`, `:1905-1911`, `:1785-1789`). Installation keys on the
declaration's TYPE alone — binder info plays no part, so
`fun (inst : Add N) => …` is a local instance exactly as `[inst : Add N]`
is.

The oracle's third site, `forallTelescopeReducingAux`, needs no separate
wiring: `forall_bounded_telescope` already mints its fvars through
`push_local_decl`. That is a claim about current call sites rather than a
structural guarantee, so it has its own test.

The implementation-detail filter (`withNewLocalInstanceImp`,
`Basic.lean:1383-1388`) is vacuously satisfied — leanr's `LocalDecl` has
no kind field and nothing mints such a decl — and is recorded as a seam
rather than widening the kernel TCB for a producer that does not exist.

Still no consumer, so behavior is unchanged.

Claude-Session: https://claude.ai/code/session_01MdUSj32wrx862QVNCypLnh
MSG
)"
```

---
### Task 5: The snapshot carries local instances

**Files:**
- Modify: `crates/leanr_meta/src/local_snapshot.rs` (`new`, `empty`, `parts`, `reduced`)
- Modify: `crates/leanr_meta/src/metactx.rs` (`current_lctx` at `:509`, `install_lctx` at `:538`, `with_mvar_context` at `:576`)

**Interfaces:**
- Consumes: `LocalInstance`, `LocalInstanceStack::{to_vec, replace}` (Task 2).
- Produces: `LocalCtxSnapshot::new(lctx, local_names, local_instances)`, `LocalCtxSnapshot::local_instances() -> &[LocalInstance]`, `parts()` returning three components. `MVarDecl.lctx` therefore carries local instances with no new field on `MVarDecl` itself.

**Why this is the PR #39/#40 amendment.** The oracle stores `localInstances` on the metavariable declaration beside `lctx` (`MetavarContext.lean:309`, `:320`), and `MVarId.withContext` reinstalls both (`withLocalContextImp`, `Basic.lean:2002-2004`). leanr's `MVarDecl.lctx` is an `Arc<LocalCtxSnapshot>` (`mvar_ctx.rs:55-60`), so putting the instances **inside the snapshot** gives every metavariable its `localInstances` with no new `MVarDecl` field and no change to any of that slice's call sites.

**A stale comment to fix, not preserve.** `with_mvar_context`'s doc (`metactx.rs:576-590`) currently reads: "`localInstances` is NOT modelled … so the oracle's instance-cache flush has nothing to flush. SEAM, owner: the slice that adds local instances." This slice **is** that owner, so the seam note is replaced. Its premise is also wrong on a second count and must not be carried forward: `withLocalContextImp` (`Basic.lean:2002-2004`) is a plain `withReader` swap with **no** instance-cache flush anywhere in it. Say what is true — leanr has no synthesis cache at all yet (the M4b-3 spec assigns one to "the slice that builds the synthesis cache"), so there is nothing to flush *and* nothing in the oracle flushing it here.

- [ ] **Step 1: Write the failing test**

In `crates/leanr_meta/src/metactx.rs`'s test module:

```rust
    /// oracle: `MVarId.withContext` → `withLocalContextImp`
    /// (`Basic.lean:2002-2004`) swaps `lctx` AND `localInstances`
    /// together. A metavariable minted under an instance binder must see
    /// that instance when its own context is reinstalled — otherwise a
    /// postponed goal resumed after its binder closed would synthesize
    /// against a strictly smaller instance set than the oracle's.
    #[test]
    fn with_mvar_context_reinstalls_local_instances() {
        with_class_ctx(|ctx, add| {
            let add_n = class_app(ctx, add);
            let n = const_named(ctx, "N");

            // Mint a metavariable UNDER an instance binder.
            let cp = ctx.lctx_checkpoint();
            ctx.push_local_decl(None, add_n, BinderInfo::InstImplicit).expect("push");
            let m = ctx.mk_fresh_expr_mvar(n).expect("mvar");
            ctx.lctx_restore(cp);

            // Back at top level, nothing is in scope.
            assert!(
                ctx.local_instances.entries().is_empty(),
                "the binder closed, so its instance is out of scope here"
            );

            // Inside the metavariable's own context, it is.
            let seen = ctx.with_mvar_context(m.0, |c| c.local_instances.entries().len());
            assert_eq!(
                seen, 1,
                "the mvar's recorded context carries the instance that was \
                 in scope when it was minted"
            );

            // And the caller's context is restored on the way out.
            assert!(ctx.local_instances.entries().is_empty());
        });
    }

    /// `reduced` erases an fvar from the context; its local instance must
    /// go with it. oracle: `reduceLocalContext`
    /// (`MetavarContext.lean:1065-1067`) removes the decl, and an
    /// instance whose fvar is no longer declared is a dangling reference
    /// that `get_instances` would offer as a candidate.
    #[test]
    fn reduced_drops_the_local_instance_of_an_erased_fvar() {
        with_class_ctx(|ctx, add| {
            let add_n = class_app(ctx, add);
            let cp = ctx.lctx_checkpoint();
            let inst = ctx
                .push_local_decl(None, add_n, BinderInfo::InstImplicit)
                .expect("push");
            let snap = ctx.current_lctx();
            ctx.lctx_restore(cp);

            assert_eq!(snap.local_instances().len(), 1);

            let id = match ctx.node(inst) {
                Node::FVar { id: Some(id) } => id,
                other => panic!("expected fvar, got {other:?}"),
            };
            let reduced = snap.reduced(&[(inst, id)], |f| match ctx.node(f) {
                Node::FVar { id } => id,
                _ => None,
            });
            assert!(
                reduced.local_instances().is_empty(),
                "erasing the declaration must erase its local instance too — \
                 an instance pointing at an undeclared fvar is a candidate \
                 `get_instances` would hand to the search"
            );
        });
    }
```

`mk_fresh_expr_mvar`'s exact name and return shape vary — grep
`crates/leanr_meta/src/` for the metavariable constructor used by
`synth.rs` and match it, including whether it returns `(MVarId, ExprId)`
or just one.

- [ ] **Step 2: Run to verify failure**

```bash
cargo test -p leanr_meta with_mvar_context_reinstalls
cargo test -p leanr_meta reduced_drops_the_local_instance
```

Expected: FAIL to compile — `LocalCtxSnapshot::local_instances` does not
exist.

- [ ] **Step 3: Grow the snapshot**

In `crates/leanr_meta/src/local_snapshot.rs`, add the field and thread it
through all four constructors/accessors:

```rust
pub struct LocalCtxSnapshot {
    lctx: LocalContext,
    local_names: Vec<(Option<NameId>, ExprId)>,
    /// oracle: `MetavarDecl.localInstances` (`MetavarContext.lean:320`),
    /// which sits beside `MetavarDecl.lctx` (`:309`) for exactly this
    /// reason — `MVarId.withContext` reinstalls the two together
    /// (`withLocalContextImp`, `Basic.lean:2002-2004`).
    ///
    /// Carried INSIDE the snapshot rather than as a second field on
    /// `MVarDecl`: `MVarDecl.lctx` is already an `Arc<LocalCtxSnapshot>`
    /// (`mvar_ctx.rs:55-60`), so this reaches every metavariable with no
    /// change to the metavariable-local-contexts slice's call sites.
    ///
    /// NOT in lockstep with either of the two above — it is sparse. See
    /// `local_instance.rs`.
    local_instances: Vec<LocalInstance>,
}
```

`new` takes the third argument and keeps its existing `debug_assert` for
the first two only (there is no lockstep invariant to assert for the
third). `empty()` supplies `Vec::new()`. `parts()` returns a triple, and
its doc comment gains: "the third half is sparse and has no lockstep
invariant, but travels with the other two because installing a context
without its instances is exactly the divergence this slice exists to
close."

Add the reader:

```rust
    /// The local instances in scope in this context, innermost last.
    pub(crate) fn local_instances(&self) -> &[LocalInstance] {
        &self.local_instances
    }
```

In `reduced`, filter the third component alongside the other two:

```rust
        // An instance whose declaration was erased must go too: the
        // oracle's `reduceLocalContext` (`MetavarContext.lean:1065-1067`)
        // removes the decl, and a local instance pointing at an
        // undeclared fvar would still be offered to the search by
        // `get_instances`.
        let local_instances = self
            .local_instances
            .iter()
            .filter(|li| {
                !fvar_id_of(li.fvar).is_some_and(|id| to_remove.iter().any(|(_, rid)| *rid == id))
            })
            .cloned()
            .collect();
        LocalCtxSnapshot::new(lctx, local_names, local_instances)
```

- [ ] **Step 4: Thread it through `MetaCtx`**

`current_lctx` passes `self.local_instances.to_vec()` as the third
argument. `install_lctx` destructures the triple and installs the third
with `self.local_instances.replace(instances.to_vec())`.

Replace `with_mvar_context`'s stale paragraph:

```rust
    /// `localInstances` travels inside the snapshot (`local_snapshot.rs`),
    /// so this reinstalls the metavariable's instances along with its
    /// declarations — the oracle's `withLocalContextImp` swaps both in
    /// one `withReader` (`Basic.lean:2002-2004`).
    ///
    /// The oracle does NOT flush a synthesis cache here, and neither does
    /// leanr: `withLocalContextImp` is a plain reader swap with no flush
    /// in it, and leanr has no synthesis cache at all yet (the M4b-3 spec
    /// assigns one to "the slice that builds the synthesis cache"). When
    /// that slice lands it must decide cache-vs-local-instances on its
    /// own terms; there is no flush to port from here.
```

(The previous text claimed local instances were unmodelled and that an
oracle instance-cache flush had nothing to flush. The first is no longer
true; the second was never true.)

- [ ] **Step 5: Run**

```bash
cargo test -p leanr_meta
```

Expected: PASS, including the pre-existing
`reduced_drops_the_named_fvars_from_both_halves` in `local_snapshot.rs`
(now three halves) and
`push_local_decl_scopes_and_mk_forall_abstracts`.

- [ ] **Step 6: Measure the discriminators**

| Mutation | Expected red |
|---|---|
| `install_lctx` skips the third component | `with_mvar_context_reinstalls_local_instances` |
| `reduced` copies `self.local_instances` unfiltered | `reduced_drops_the_local_instance_of_an_erased_fvar` |
| `current_lctx` passes `Vec::new()` as the third argument | `with_mvar_context_reinstalls_local_instances` |

Run each, confirm red, revert.

- [ ] **Step 7: Commit**

```bash
mise run ci
git add crates/leanr_meta/src/local_snapshot.rs crates/leanr_meta/src/metactx.rs
git commit -m "$(cat <<'MSG'
local instances: carried on the local-context snapshot

oracle: `MetavarDecl.localInstances` (`MetavarContext.lean:320`) sits
beside `MetavarDecl.lctx`, and `MVarId.withContext` reinstalls both in
one `withReader` (`withLocalContextImp`, `Basic.lean:2002-2004`).

Carried inside `LocalCtxSnapshot` rather than as a second `MVarDecl`
field, because `MVarDecl.lctx` is already an `Arc<LocalCtxSnapshot>` —
so this reaches every metavariable without touching the
metavariable-local-contexts slice's call sites. `reduced` filters
instances alongside declarations: an instance pointing at an erased fvar
would still be offered to the search.

Replaces `with_mvar_context`'s seam note, which named this slice as its
owner. Its second claim — that an oracle instance-cache flush had
nothing to flush — was wrong and is not carried forward:
`withLocalContextImp` performs no flush.

Claude-Session: https://claude.ai/code/session_01MdUSj32wrx862QVNCypLnh
MSG
)"
```

---

### Task 6: `get_instances` appends the locals

**Files:**
- Modify: `crates/leanr_meta/src/instances.rs` (`get_instances` at `:467-494`; the ordering module doc at `:165-216`)

**Interfaces:**
- Consumes: `MetaCtx::is_class` (Task 3), `local_instances` (Tasks 2, 4, 5), `Instance { val, ty, priority, synth_order, global_name }` (`instances.rs:296-322`).
- Produces: `get_instances` returning locals **first**, each with `global_name: None`, `priority` at the default, and a `synth_order` computed from its own type's instance-implicit binders.

**Three things the oracle's own ordering settles** (`getInstances`, `SynthInstance.lean:202-240`):

1. **`className` is computed before the global index is touched** (`:205-209` vs `:210`). leanr must do the same, because `is_class`'s expensive path runs whnf and `get_instances` `mem::take`s its table for the duration of `discr_get_match` (`instances.rs:468-479`). Computing the class name **before** the take satisfies the invariant and is the faithful order — they agree, which is worth not re-deriving later.
2. **Locals are tried first.** The oracle appends them to the end of an ascending-by-priority array (`:230-237`) and `generate` consumes back-to-front. leanr transcribes that composition as sort-ascending-then-reverse (`:486-492`), so the append goes **after the sort and before the reverse**.
3. **A local's `synthOrder` is computed at query time** (`:231-238`), unlike a global's, which the extension precomputes: telescope `inferType linst.fvar` and collect the indices whose binder info is `.instImplicit`.

- [ ] **Step 1: Write the failing tests**

```rust
    /// A local instance solves a goal no global can. oracle:
    /// `getInstances` :230-237.
    #[test]
    fn a_local_instance_is_offered_as_a_candidate() {
        with_class_ctx(|ctx, add| {
            let add_n = class_app(ctx, add);
            let cp = ctx.lctx_checkpoint();
            let inst = ctx
                .push_local_decl(None, add_n, BinderInfo::InstImplicit)
                .expect("push");
            let found = ctx.get_instances(add_n).expect("get_instances");
            assert!(
                found.iter().any(|i| i.val == inst),
                "the in-scope local instance must be a candidate"
            );
            assert!(
                found.iter().find(|i| i.val == inst).unwrap().global_name.is_none(),
                "a local instance has no declaration name"
            );
            ctx.lctx_restore(cp);
        });
    }

    /// A local instance is tried BEFORE every global. oracle: appended
    /// to the end of the ascending array (:230-237), consumed
    /// back-to-front by `generate` — which this crate transcribes as
    /// sort-ascending-then-reverse (:486-492), so the append must land
    /// between the sort and the reverse.
    ///
    /// This is the slice's most mutable line: pushing before the sort
    /// puts the local in default-priority position among the globals
    /// instead of ahead of all of them.
    #[test]
    fn a_local_instance_is_tried_before_every_global() {
        with_class_ctx_and_global_instance(|ctx, add, global| {
            let add_n = class_app(ctx, add);
            let cp = ctx.lctx_checkpoint();
            let local = ctx
                .push_local_decl(None, add_n, BinderInfo::InstImplicit)
                .expect("push");
            let found = ctx.get_instances(add_n).expect("get_instances");
            let li = found.iter().position(|i| i.val == local).expect("local present");
            let gi = found.iter().position(|i| i.val == global).expect("global present");
            assert!(
                li < gi,
                "local at {li}, global at {gi}: locals are consumed first, so \
                 they must come first in this vector"
            );
            ctx.lctx_restore(cp);
        });
    }

    /// An out-of-scope local instance is not a candidate.
    #[test]
    fn a_closed_binders_instance_is_not_offered() {
        with_class_ctx(|ctx, add| {
            let add_n = class_app(ctx, add);
            let cp = ctx.lctx_checkpoint();
            let inst = ctx
                .push_local_decl(None, add_n, BinderInfo::InstImplicit)
                .expect("push");
            ctx.lctx_restore(cp);
            let found = ctx.get_instances(add_n).expect("get_instances");
            assert!(found.iter().all(|i| i.val != inst));
        });
    }

    /// A local instance of a DIFFERENT class is not offered. oracle:
    /// `if linst.className == className` (:231) — exact name equality,
    /// never defeq.
    #[test]
    fn a_local_instance_of_another_class_is_not_offered() {
        with_two_class_ctx(|ctx, add, mul| {
            let mul_n = class_app(ctx, mul);
            let add_n = class_app(ctx, add);
            let cp = ctx.lctx_checkpoint();
            let inst = ctx
                .push_local_decl(None, mul_n, BinderInfo::InstImplicit)
                .expect("push");
            let found = ctx.get_instances(add_n).expect("get_instances");
            assert!(
                found.iter().all(|i| i.val != inst),
                "a `Mul N` in scope is not a candidate for an `Add N` goal"
            );
            ctx.lctx_restore(cp);
        });
    }

    /// A local's `synth_order` is read off the INSTANCE-IMPLICIT binders
    /// of its own type. oracle: :231-238.
    #[test]
    fn a_local_instances_synth_order_comes_from_its_instimplicit_binders() {
        with_class_ctx(|ctx, add| {
            // `{a : Type} → [Add a] → Add (Prod a a)`: binder 0 is
            // implicit, binder 1 is instance-implicit.
            let ty = parametrized_instance_type(ctx, add);
            let goal = class_app_prod(ctx, add);
            let cp = ctx.lctx_checkpoint();
            let inst = ctx.push_local_decl(None, ty, BinderInfo::InstImplicit).expect("push");
            let found = ctx.get_instances(goal).expect("get_instances");
            let li = found.iter().find(|i| i.val == inst).expect("local present");
            assert_eq!(
                li.synth_order,
                vec![1],
                "only binder 1 is instance-implicit; an empty synth_order \
                 would make the search never solve the subgoal"
            );
            ctx.lctx_restore(cp);
        });
    }
```

Write `with_class_ctx_and_global_instance`, `with_two_class_ctx`,
`parametrized_instance_type` and `class_app_prod` alongside the existing
`with_instances_ctx` helper (`instances.rs:790-830`) — read it first and
follow its shape.

- [ ] **Step 2: Run to verify failure**

```bash
cargo test -p leanr_meta local_instance
```

Expected: FAIL — no local is ever offered.

- [ ] **Step 3: Implement**

Rewrite `get_instances` (`instances.rs:467-494`):

```rust
    pub(crate) fn get_instances(&mut self, goal: ExprId) -> Result<Vec<Instance>, MetaError> {
        // oracle: `getInstances` reads the local instances and resolves
        // the goal's class name (:204-209) BEFORE it touches the global
        // index (:210). Transcribing that order is not cosmetic here:
        // `is_class`'s expensive path runs whnf, and the `mem::take`
        // below leaves `self.instances` EMPTY for the duration of
        // `discr_get_match`, so a whnf inside that window would re-enter
        // instance lookup against an empty table and silently report "no
        // instances". Computing the class name up here keeps whnf
        // strictly outside the window — the faithful order and the safe
        // one are the same order.
        let class_name = self.is_class(goal)?;

        // INVARIANT (re-entrancy): `self.instances` is
        // `InstanceTable::default()` (empty) for the whole duration of
        // the `discr_get_match` call below. Harmless today because
        // `mk_path`/`whnf` never consult the instance table, so nothing
        // reachable from `discr_get_match` can observe the table being
        // briefly taken. If a future change makes path construction (or
        // anything else `discr_get_match` transitively calls) re-entrant
        // into instance lookup, a nested `get_instances` call here would
        // silently see this now-empty placeholder table and report "no
        // instances" rather than erroring — there is no assertion below
        // that would catch that, so a future change widening what
        // `discr_get_match` touches must re-check this invariant by
        // inspection. `is_class` above is deliberately OUTSIDE the take
        // for exactly this reason.
        let table = std::mem::take(&mut self.instances);
        let result: Result<Vec<Instance>, MetaError> = self
            .discr_get_match(&table.tree, goal)
            .map(|v| v.into_iter().cloned().collect());
        self.instances = table;
        let mut found = result?;
        // oracle: `insertionSort (·.priority < ·.priority)` (ascending,
        // stable) then `generate`'s back-to-front consumption — see this
        // module's doc for why "stable-ascending-sort, then reverse the
        // whole vector" is the exact (not approximate) transcription of
        // that composition.
        found.sort_by_key(|i| i.priority);
        // oracle: :230-237 — locals are appended to the END of the
        // ascending array, i.e. consumed FIRST. So they go on after the
        // sort and before the reverse; pushing them before the sort
        // would instead file them among the globals at default priority.
        if let Some(class_name) = class_name {
            for li in self.local_instances.to_vec() {
                if li.class_name != class_name {
                    continue;
                }
                found.push(self.local_instance_candidate(li.fvar)?);
            }
        }
        found.reverse();
        Ok(found)
    }

    /// oracle: `getInstances` :231-238 — a local instance's candidate
    /// record. Unlike a global's, its `synthOrder` is computed HERE
    /// rather than read from the instance extension: telescope the
    /// fvar's own type and collect the positions whose binder info is
    /// instance-implicit.
    ///
    /// `global_name` is `None`, and that is legitimate rather than the
    /// malformed-bytes case this module's doc used to describe — see the
    /// `global_name: None` section above.
    fn local_instance_candidate(&mut self, fvar: ExprId) -> Result<Instance, MetaError> {
        let ty = self.infer_type(fvar)?;
        let mut synth_order = Vec::new();
        let cp = self.lctx_checkpoint();
        let mut cur = ty;
        let mut i = 0usize;
        loop {
            let t = if matches!(self.node(cur), Node::Forall { .. }) {
                cur
            } else {
                self.whnf(cur)?
            };
            let Node::Forall {
                binder_name,
                binder_type,
                body,
                binder_info,
            } = self.node(t)
            else {
                break;
            };
            if binder_info == BinderInfo::InstImplicit {
                synth_order.push(i);
            }
            // The telescope must really open the binder: a later
            // binder's type may mention an earlier one, and the oracle
            // runs this inside `forallTelescopeReducing`.
            self.push_local_decl(binder_name, binder_type, binder_info)?;
            cur = body;
            i += 1;
        }
        self.lctx_restore(cp);
        Ok(Instance {
            val: fvar,
            ty,
            priority: DEFAULT_INSTANCE_PRIORITY,
            synth_order,
            global_name: None,
        })
    }
```

**Read before writing:** `DEFAULT_INSTANCE_PRIORITY` may not exist —
grep `instances.rs` for how `InstanceTable::build` fills `priority` when
the extension entry has none, and use the same constant or literal. The
oracle's local-instance record carries no priority at all
(`{ val, synthOrder }`, `:237`), so whatever value the struct requires
must be one that cannot reorder locals among themselves; since they are
appended after the sort, any constant works, but say which and why in the
comment.

**Note the recursion:** `local_instance_candidate` calls
`push_local_decl`, which installs local instances (Task 4), which is
exactly the oracle's own behavior — `forallTelescopeReducing` installs
too (`Basic.lean:1472`). The stack is restored by `lctx_restore(cp)`. This
is the self-reference `Basic.lean:1402-1406` acknowledges; it terminates
because the telescope is finite.

- [ ] **Step 4: Run**

```bash
cargo test -p leanr_meta
```

Expected: PASS, all five new tests plus the pre-existing
`get_instances_orders_by_priority_desc_then_reverse_of_ties`.

- [ ] **Step 5: Measure the discriminators**

| Mutation | Expected red |
|---|---|
| skip the append loop entirely | `a_local_instance_is_offered_as_a_candidate` |
| move the append to **before** `found.sort_by_key` | `a_local_instance_is_tried_before_every_global` |
| drop the `li.class_name != class_name` guard | `a_local_instance_of_another_class_is_not_offered` |
| `synth_order: Vec::new()` in `local_instance_candidate` | `a_local_instances_synth_order_comes_from_its_instimplicit_binders` |
| collect **every** binder index into `synth_order`, not just instImplicit | the same test (expects `vec![1]`, would get `vec![0, 1]`) |
| move `let class_name = self.is_class(goal)?` to **after** `self.instances = table;` | none of the above — see below |

The last row is the one to watch. Moving the `is_class` call after the
table is restored is still *correct*, so no test goes red; the invariant
it protects is about a **future** change to `discr_get_match`. Do not
manufacture a test that pretends otherwise. Instead, confirm by
inspection that the call sits outside the `mem::take` window and that the
comment says why — and record in the commit message that this one is
guarded by comment and review, not by a test. Claiming a kill here would
be exactly the defect this repo keeps hitting.

- [ ] **Step 6: Commit**

```bash
mise run ci
git add crates/leanr_meta/src/instances.rs
git commit -m "$(cat <<'MSG'
local instances: offered as candidates by `get_instances`

oracle: `getInstances` (`SynthInstance.lean:202-240`). Three details its
own ordering settles:

  * the goal's class name is resolved BEFORE the global index is touched
    (:205-209 vs :210). leanr must match, because `is_class`'s expensive
    path runs whnf while `get_instances` `mem::take`s its table for the
    duration of `discr_get_match` — a whnf inside that window would
    re-enter lookup against an empty table. Faithful and safe agree.
  * locals are appended to the END of the ascending array (:230-237) and
    consumed back-to-front, so with this crate's sort-then-reverse
    transcription they go on AFTER the sort and BEFORE the reverse —
    i.e. they are tried first.
  * a local's synthOrder is computed at query time from the
    instance-implicit binders of its own type (:231-238), where a
    global's is precomputed by the extension.

Class matching is exact name equality (:231), never defeq.

Not covered by a test, deliberately: moving the `is_class` call inside
the `mem::take` window is still correct today, so nothing goes red. It
is guarded by the invariant comment and by review, and this is said
plainly rather than claimed as a kill.

Claude-Session: https://claude.ai/code/session_01MdUSj32wrx862QVNCypLnh
MSG
)"
```

---
### Task 7: The `global_name: None` invariant, and its downstream readers

**Files:**
- Modify: `crates/leanr_meta/src/instances.rs` (module doc, the `global_name: None` section at `:89-111`)
- Modify: `crates/leanr_meta/src/synth.rs` (a comment and a test at `mk_const_with_fresh_mvar_levels`, `:2674-2690`, and at `get_subgoals`, `:2552-2584`)

**Why this is a task and not a doc touch-up.** `instances.rs:89-111` argues at length that `global_name: None` is reachable **only** via adversarial or malformed `.olean` bytes, and that dropping such entries is incompleteness-only. Task 6 falsified that: a local instance is a legitimate `global_name: None`, constructed directly in `get_instances` and never passing through `InstanceTable::build`. A standing argument that is now false is worse than no argument — the next reader will rely on it.

**The downstream reader that matters.** `get_subgoals` (`synth.rs:2552-2584`) starts with `mk_const_with_fresh_mvar_levels(inst.val)`, because leanr moved the oracle's level refresh out of `getInstances` (where it lives in the `.const` filterMapM arm, `SynthInstance.lean:216-226`) and into the consumer. A local instance's `val` is an **fvar**, which has no universe arguments to refresh — and the oracle indeed refreshes nothing for locals, pushing the raw fvar (`:237`). `mk_const_with_fresh_mvar_levels` already returns non-`Const` nodes unchanged (`synth.rs:2676-2678`), so this is correct today **by accident**: that early return was written for the arity-0 case. Pin it.

- [ ] **Step 1: Write the failing test**

In `crates/leanr_meta/src/synth.rs`'s test module:

```rust
    /// A local instance's `val` is an FVAR, and the oracle refreshes no
    /// universe levels for locals — `getInstances` refreshes only in its
    /// `.const` arm (`SynthInstance.lean:216-226`) and pushes the raw
    /// fvar for locals (`:237`). leanr moved that refresh into
    /// `get_subgoals`, so the passthrough for non-`Const` values is
    /// load-bearing rather than incidental: refreshing (or erroring on)
    /// an fvar here would corrupt every local-instance candidate.
    #[test]
    fn mk_const_with_fresh_mvar_levels_passes_an_fvar_through_unchanged() {
        with_ctx(|ctx| {
            let base = Some(ctx.view.store);
            let zero = ctx.scratch.level_zero(base).expect("level");
            let sort0 = ctx.scratch.expr_sort(base, zero).expect("Sort 0");
            let fvar = fresh_fvar(ctx, sort0, "inst");
            assert_eq!(
                ctx.mk_const_with_fresh_mvar_levels(fvar).expect("refresh"),
                fvar,
                "an fvar has no universe arguments; it must come back \
                 identical, not rebuilt"
            );
        });
    }
```

- [ ] **Step 2: Run to verify it passes already**

```bash
cargo test -p leanr_meta mk_const_with_fresh_mvar_levels_passes
```

Expected: **PASS immediately.** This is a characterization test, not
TDD-red — it pins behavior that already exists but was never asserted and
is now load-bearing. Say so in the commit message rather than pretending
it drove the implementation.

To confirm it discriminates, mutate `mk_const_with_fresh_mvar_levels`'s
early return to `panic!("not a const")` and re-run: expected **RED**.
Revert.

- [ ] **Step 3: Add the comment at both sites**

In `mk_const_with_fresh_mvar_levels`, above the `let Node::Const … else`
early return:

```rust
        // The non-`Const` passthrough is LOAD-BEARING, not incidental: a
        // local instance's `val` is an fvar (`get_instances`' local
        // append), and the oracle refreshes no levels for locals — its
        // refresh lives in `getInstances`' `.const` arm
        // (`SynthInstance.lean:216-226`) while locals are pushed raw
        // (:237). Pinned by
        // `mk_const_with_fresh_mvar_levels_passes_an_fvar_through_unchanged`.
```

In `get_subgoals`, after the existing HARD REQUIREMENT paragraph:

```rust
        // For a LOCAL instance this is a no-op by construction: `val` is
        // an fvar, so there are no universe arguments to refresh, which
        // is exactly the oracle's own treatment of locals.
```

- [ ] **Step 4: Rewrite the module-doc section**

Replace `instances.rs:89-111`'s `# `global_name: None`` section. It
currently asserts that `global_name: None` is reachable only via
adversarial bytes. Rewrite to distinguish the two sources:

```rust
//! # `global_name: None` — two sources, only one of them adversarial
//!
//! **A local instance (legitimate).** `get_instances` constructs a
//! candidate directly for every in-scope local instance
//! (oracle: `getInstances` :230-237), whose `val` is an fvar and which
//! has no declaration name at all. These never pass through
//! `InstanceTable::build` and are never serialized — `addInstance`
//! (`Instances.lean:283-304`) is the only producer of a persisted
//! `instanceExtension` entry and always sets `globalName? := declName`.
//! So `global_name: None` on a candidate returned by `get_instances`
//! means "local", and any reader that treats it as malformed input is
//! wrong.
//!
//! **A malformed decode (adversarial).** Inside `InstanceTable::build`,
//! reading `global_name = None` off `.olean` bytes still means exactly
//! what it meant before: there is no `Name` to resolve a `ty` from
//! (`EnvView::get` needs one) and no other source for the instance's
//! declared type, so `build` drops the entry. Dropping a candidate is
//! incompleteness only (`get_instances` simply never offers it; the
//! kernel independently re-checks whatever IS synthesized), never a
//! wrong verdict. Global Constraints: `.olean` bytes are untrusted.
//!
//! The distinction is by CONSTRUCTION SITE, not by inspection: nothing
//! about a `None` tells you which it was. Readers must therefore not
//! infer "malformed" from `global_name.is_none()`.
```

- [ ] **Step 5: Audit every downstream reader**

Find them all and check each against the rewritten invariant:

```bash
rg -n 'global_name' crates/ --type rust
```

For each hit, decide and record in the commit message:
- `InstanceTable::build` / `by_name` / `get_by_name` — table-side, unchanged; locals never reach them.
- `instance_named` — table-side, unchanged.
- any read on a candidate returned by `get_instances` — **must** tolerate `None` as "local".

If a reader assumes `Some`, fix it in this task and name it in the commit
message. If there are none, say **that** in the commit message
explicitly, so the next reader knows the audit ran and found nothing
rather than wondering whether it ran.

- [ ] **Step 6: Commit**

```bash
mise run ci
git add crates/leanr_meta/src/instances.rs crates/leanr_meta/src/synth.rs
git commit -m "$(cat <<'MSG'
local instances: `global_name: None` now has a legitimate source

`instances.rs` argued that `global_name: None` was reachable only via
adversarial or malformed `.olean` bytes. A local instance falsifies that:
it is constructed directly in `get_instances`, has no declaration name,
and never passes through `InstanceTable::build`. The section is rewritten
to distinguish the two sources by construction site, since nothing about
a `None` tells them apart on inspection.

Also pins a passthrough that became load-bearing: `get_subgoals` runs
`mk_const_with_fresh_mvar_levels` on every candidate's `val`, and a
local's is an fvar. The oracle refreshes levels only in `getInstances`'
`.const` arm and pushes locals raw, so returning the fvar unchanged is
the faithful behavior — previously true only by accident of the arity-0
early return, now asserted. Characterization test, not TDD-red.

Claude-Session: https://claude.ai/code/session_01MdUSj32wrx862QVNCypLnh
MSG
)"
```

---

### Task 8: Fixture declarations and the differential records

**Files:**
- Modify: `tests/fixtures/meta/Synth0.lean`
- Modify: `tests/fixtures/meta/dump_synth.lean` (query list)
- Modify: `tests/fixtures/meta/synth-queries.jsonl` (regenerated, never hand-edited)
- Modify: `tests/fixtures/meta/Synth0.olean` (regenerated)

**Interfaces:**
- Consumes: the `fvars` channel (Task 1), everything Tasks 2–7 built.
- Produces: the differential coverage the spec's § Records table requires.

**Fixture vocabulary already present** (`Synth0.lean`): `N`, `Prod`, `Add`/`instAddN`, `Mul`/`instMulN`, `Pri`/`instPriHigh`/`instPriLow`, `NoInst` (a class with **no** instances — the one that makes a local the only candidate), `Chain`/`instChainN`/`instChainProd`, `Op` (outParam). Reuse these; add only what is genuinely missing.

- [ ] **Step 1: Add the one missing declaration**

`Synth0.lean` has no class whose *local* inhabitant needs subgoals of its
own. Add, next to the existing `Chain` block:

```lean
-- Local-instances slice: a class with NO global instance for `Prod`, so
-- a PARAMETRIZED local instance is the only way to solve
-- `NoInst (Prod N N)`. Its own `[NoInst a]` binder is what gives the
-- local candidate a non-empty `synthOrder` (`SynthInstance.lean:231-238`)
-- — with an empty one the search never solves the subgoal, which is the
-- mutation `noInstParamLocal` exists to kill.
--
-- Declared but NOT instantiated: there is deliberately no
-- `instance : NoInst (Prod a b)`, because the point is that only the
-- local can answer.
```

No new class is needed — `NoInst` already serves. Confirm by reading
`Synth0.lean:121` before adding anything; **if `NoInst` suffices, add no
declaration at all and say so in the commit message.** Adding an unused
declaration to a frozen fixture changes every downstream `.olean` offset
for no benefit.

- [ ] **Step 2: Add the records**

In `dump_synth.lean`'s curated query list, with the documentation block
each existing entry has:

```lean
  * `noInstLocal`      — `NoInst N` with `[h : NoInst N]` in scope.
                         `NoInst` has no global instance anywhere in the
                         fixture, so the local is the ONLY candidate and
                         the answer is `h` itself. Kills "locals are
                         never appended".
  * `localBeatsGlobal` — `Add N` with `[h : Add N]` in scope, where
                         `instAddN` also matches. The oracle appends
                         locals to the END of the ascending array and
                         consumes back-to-front, so the answer is `h`,
                         NOT `instAddN`. Kills the append moved before
                         the priority sort — the slice's most mutable
                         line.
  * `letLocal`         — `Add N` with `let h : Add N := instAddN` in
                         scope. `withLetDeclImp` routes through the same
                         `withNewFVar` (`Basic.lean:1905-1911`), so a
                         let-bound instance counts; the answer is `h`.
                         Kills dropping the install from `push_let_decl`.
  * `noInstParamLocal` — `NoInst (Prod N N)` with
                         `[h : {a b : Type} → [NoInst a] → [NoInst b] →
                         NoInst (Prod a b)]` and `[ha : NoInst N]` in
                         scope. The candidate `h` has synthOrder `[2,3]`
                         (its two instance-implicit binders); with an
                         empty synthOrder the subgoals are never
                         scheduled and the goal fails. Kills
                         `synth_order: Vec::new()`.
  * `nonClassFvar`     — `Add N` with `(x : N)` AND `(f : N → N)` in
                         scope. Neither is class-typed, so neither is a
                         candidate and the answer stays `instAddN`.
                         NOTE: this record does NOT kill a constant-true
                         `is_class` on its own — see Step 5.
  * `outOfScope`       — deliberately ABSENT. Scope exit is not
                         expressible in this record shape: every `fvars`
                         entry is open for the whole query. It is covered
                         by `a_closed_binders_instance_is_not_offered`
                         (Task 6) instead, and this is recorded here so a
                         later reader does not assume the corpus covers
                         it.
```

- [ ] **Step 3: Regenerate and run**

```bash
mise run fixtures:regen
cargo test -p leanr_meta --test oracle_synth
```

Expected: PASS at **32** records (27 after Task 1 + 5 here).

```bash
git diff --stat tests/fixtures/meta/synth-queries.jsonl
```

Expected: 5 lines added, **zero modified**. If any pre-existing line
changed, stop and diagnose — that is the neutrality gate failing early,
and Task 9 is where it gets adjudicated, not here.

- [ ] **Step 4: Verify the oracle actually answers what the record claims**

For `localBeatsGlobal` in particular, read the emitted `val` and confirm
it is the **fvar**, not `instAddN`:

```bash
grep localBeatsGlobal tests/fixtures/meta/synth-queries.jsonl | python3 -m json.tool
```

Expected: `"val": {"k":"fvar","i":0}`.

**If it is `instAddN`, the whole ordering premise is wrong** and Task 6's
implementation must be revisited — do not adjust the record to match
leanr. The oracle is the specification.

- [ ] **Step 5: Measure the discriminators**

Apply each mutation to `leanr_meta/src`, run
`cargo test -p leanr_meta --test oracle_synth`, confirm the named record
goes red, revert:

| Mutation | Expected red record |
|---|---|
| skip `get_instances`' local append | `noInstLocal`, `localBeatsGlobal`, `letLocal`, `noInstParamLocal` |
| move the append before `found.sort_by_key` | `localBeatsGlobal` |
| drop the install from `push_let_decl` | `letLocal` |
| `synth_order: Vec::new()` for locals | `noInstParamLocal` |
| `is_class` returns the head constant unconditionally | **expected: nothing** |

The last row is the honest one. `nonClassFvar`'s fvars are typed `N` and
`N → N`; a constant-true `is_class` would register them under class `N`,
which no goal in the corpus asks for, so no answer changes. **The corpus
does not discriminate here** — `is_class_rejects_a_non_class_head` (Task
3) is what does. Run the mutation anyway to confirm the prediction, and
if some record unexpectedly goes red, work out why before proceeding: an
unexplained kill means the corpus is coupled in a way nobody modelled.

Record all five outcomes in the commit message, including the null one.

- [ ] **Step 6: Commit**

```bash
mise run ci
git add tests/fixtures/meta/
git commit -m "$(cat <<'MSG'
local instances: differential records

Five records at the meta tier: a local as the only candidate
(`noInstLocal`), a local beating a matching global (`localBeatsGlobal` —
the ordering claim, and the slice's most mutable line), a let-bound
instance (`letLocal`), a parametrized local whose own instance-implicit
binders give it a non-empty synthOrder (`noInstParamLocal`), and
non-class fvars that must change nothing (`nonClassFvar`).

Scope exit is deliberately NOT a record: every `fvars` entry is open for
the whole query, so the shape cannot express it. Covered by
`a_closed_binders_instance_is_not_offered` instead, and said here so a
later reader does not assume the corpus covers it.

`nonClassFvar` does not kill a constant-true `is_class` — its fvars are
typed `N` and `N -> N`, and no goal asks for class `N`, so no answer
moves. The unit test `is_class_rejects_a_non_class_head` is what kills
it. Recorded rather than claimed.

Claude-Session: https://claude.ai/code/session_01MdUSj32wrx862QVNCypLnh
MSG
)"
```

---

### Task 9: The neutrality gate

**Files:** none modified unless a record moves.

**What is being decided.** The spec states this gate as **measured, not structural** (§ Neutrality gate). The producer sits at the meta-tier telescopes, so any *existing* synthesis that runs with a class-typed fvar in scope can change answer. This task runs the measurement and adjudicates the result — it is not a formality, and a moved record is a finding, not a chore.

- [ ] **Step 1: Measure both corpora**

```bash
git stash list
cargo test -p leanr_meta
cargo test -p leanr_elab
mise run meta:fast
```

Then the byte-identity check that actually matters:

```bash
git diff --stat tests/fixtures/meta/synth-queries.jsonl tests/fixtures/elab/elab-queries.jsonl
```

Expected: `synth-queries.jsonl` shows exactly the 6 records added by
Tasks 1 and 8 (27 + 5 = 32 total, from a committed baseline of 26);
`elab-queries.jsonl` shows **no change at all**, still 117 records.

- [ ] **Step 2: Adjudicate**

**If both are clean:** record the counts in the commit message and move
on.

**If a record moved:** stop and diagnose before touching anything. Do
**not** regenerate a new baseline. The candidates, in order of
likelihood:

1. `dflt/polyInstImplicitUnderBinder` — the spec names it as the most
   likely to move, because it is the existing record most likely to run
   synthesis with a class-typed fvar in scope.
2. Any elaboration record whose term elaborates under a binder whose type
   is a class.

For whichever moved, answer three questions in writing before proceeding:
- **What does the oracle say?** Re-dump that single record and compare.
  If leanr's new answer matches the oracle and the old one did not, leanr
  was previously right by accident and the record should be updated —
  with the diagnosis in the commit message.
- **If leanr's new answer does NOT match the oracle**, the slice has a
  bug. Fix the bug; do not update the record.
- **Which mechanism moved it?** Name the specific install site. "Local
  instances changed it" is not a diagnosis.

- [ ] **Step 3: Check the elaborator-seam prediction**

The spec predicts (§ One prediction, written down in advance) that
wiring a meta-tier mechanism may wake a dormant `leanr_elab` scoping bug,
as elimMVarDeps did for `default_inst.rs` rung 3. The Global Constraints
allow exactly one response: an **additive fix to a seam that a measured
regression names**.

```bash
cargo test -p leanr_elab 2>&1 | tail -40
```

If a `leanr_elab` test fails, that is the prediction landing. Fix the one
named seam additively, and say in the commit message which measurement
forced it and which `mvarId.withContext` site (or equivalent) was missing
— the same shape Amendment 7 records. **Do not** take the exception for
anything a measurement did not name.

- [ ] **Step 4: Commit the measurement**

```bash
mise run ci
git commit --allow-empty -m "$(cat <<'MSG'
local instances: neutrality gate measured

Both committed corpora checked against the pre-slice baseline: the
elaboration corpus is unchanged at 117 records, and the synthesis corpus
grew from 26 to 32 with every pre-existing record byte-identical.

The gate is measured, not structural — the producer sits at the meta-tier
telescopes, so an existing synthesis running with a class-typed fvar in
scope could have moved. None did.

Claude-Session: https://claude.ai/code/session_01MdUSj32wrx862QVNCypLnh
MSG
)"
```

(Adjust the message to the truth if a record moved; an empty commit is
appropriate only when nothing did.)

---

### Task 10: Seams, module docs, and the whole-branch review

**Files:**
- Modify: `crates/leanr_meta/src/instances.rs` (module doc: the `scoped instance` and erasure sections)
- Modify: `crates/leanr_meta/src/local_instance.rs` (the inherited-circularity note)
- Modify: `docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md` (Amendment 8, item 5)

- [ ] **Step 1: Record the seams the spec names**

In `local_instance.rs`'s module doc, add:

```rust
//! # An inherited circularity, named rather than resolved
//!
//! `isClassExpensive?` runs whnf, and whnf depends indirectly on the set
//! of local instances being computed. The oracle says so in as many
//! words (`Basic.lean:1402-1406`). leanr inherits it exactly, and it
//! surfaces a second time in `get_instances`'
//! `local_instance_candidate`, whose telescope installs further local
//! instances while computing one candidate's `synthOrder`. Both
//! terminate — the telescope is finite and the whnf is under
//! `withReducible` — but neither is "resolved", and a future change that
//! makes `is_class` consult the instance table would close the loop for
//! real.
//!
//! # Seams this slice does NOT close
//!
//! * `"type class instance expected"` — the oracle throws when a goal's
//!   `isClass?` is `none` (`SynthInstance.lean:207`); leanr's
//!   `get_instances` returns candidates regardless. PRE-EXISTING, and
//!   deliberately left: closing it here would put corpus movement from
//!   an unrelated fix inside this slice's neutrality gate, which is the
//!   whole approval argument for a non-additive change. Explicitly
//!   unowned.
//! * `scoped instance` namespace activation — unchanged, still unowned
//!   (this module's own `# Scope: global instances only` section).
//! * erasure / private-instance filtering — unchanged, still unowned.
//!   Note these filters live in `getInstances`' `.const` arm
//!   (`SynthInstance.lean:216-228`) and so do not apply to locals at
//!   all, which is faithful rather than a gap.
//! * `withNewMCtxDepth`'s depth machinery does not reach local
//!   instances: they are fvars, not metavariables. Recorded as a
//!   NON-interaction so a later reader does not go looking for one.
```

In `instances.rs`, update the `# Scope: global instances only (named
seam)` section (`:64-88`) — its title is now wrong. Local instances are
in scope; what remains unowned is `scoped instance` activation. Retitle
and narrow it to that, keeping the existing ownership note.

- [ ] **Step 2: Close the Amendment 8 loop**

In `docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md`,
Amendment 8 item 5 currently reads "**Ordering.** Local instances, then
P5." Append the landing note, in the shape Amendment 7 used:

```
**That slice has now landed.** `MetaCtx` carries a sparse
`local_instances` stack installed at `push_local_decl`/`push_let_decl`
(and so at every telescope), carried on `LocalCtxSnapshot` and therefore
on every `MetavarDecl`, and consumed by `get_instances`, which resolves
the goal's class name before taking its table and appends matching
locals between the priority sort and the reverse — so locals are tried
first. The synth record shape gained an `fvars` field; the corpus grew
from 26 to 32 records, and the 117 elaboration records stayed
byte-identical. M4b-3 P5's instance-implicit binders now have a
consumer.
```

Fill the counts from Task 9's actual measurement rather than from this
plan, and if a record moved, say which and why.

- [ ] **Step 3: Run the full gate**

```bash
mise run ci
mise run meta:fast
```

Expected: all green, including `cargo fmt --check` and clippy.

- [ ] **Step 4: Request a whole-branch review**

Use the `superpowers:requesting-code-review` skill against the full
branch diff (`git diff main...local-instances`). The two prior
prerequisite slices each had a whole-branch review find a *second*
prerequisite, so this is not a formality. Direct the reviewer's attention
at:

- the ordering claim in `get_instances` (locals before globals) and
  whether `localBeatsGlobal` really pins it;
- whether any `leanr_meta` path pushes an fvar **without** going through
  `push_local_decl`/`push_let_decl`, which would silently skip
  installation (Task 4's telescope test covers the one known case);
- the `global_name: None` audit from Task 7 — whether any reader still
  infers "malformed" from a `None`;
- whether `local_instance_candidate`'s telescope can diverge on a
  pathological local instance type.

- [ ] **Step 5: Commit and open the PR**

```bash
mise run ci
git add -A
git commit -m "$(cat <<'MSG'
local instances: seams, module docs, and the amendment-8 landing note

Records the seams this slice does not close — the pre-existing
"type class instance expected" divergence, `scoped instance` activation,
erasure/private-instance filtering — and the inherited circularity
(`Basic.lean:1402-1406`) that surfaces a second time in
`local_instance_candidate`'s own telescope. Notes `withNewMCtxDepth` as a
non-interaction so a later reader does not go looking.

`instances.rs`'s "Scope: global instances only" section is retitled and
narrowed: local instances are now in scope, and what remains unowned is
`scoped instance` activation.

Claude-Session: https://claude.ai/code/session_01MdUSj32wrx862QVNCypLnh
MSG
)"
git push -u origin local-instances
gh pr create --title "Local instances (LocalInstances)" --body "$(cat <<'BODY'
Models the oracle's `LocalInstances` context in `leanr_meta`, so that
M4b-3 P5's instance-implicit binders have a consumer instead of shipping
decorative.

Prerequisite slice ahead of P5, recorded as Amendment 8 in the M4b-3
spec — the third such slice in a row, after metavariable-local-contexts
and elimMVarDeps.

**Spec:** `docs/superpowers/specs/2026-09-09-local-instances-design.md`
**Plan:** `docs/superpowers/plans/2026-09-09-local-instances.md`

## What lands

- a sparse `local_instances` stack on `MetaCtx`, truncated by recorded
  depth rather than by index
- `is_class` — `isClassQuick?`'s whnf-free structural walk with
  `isClassExpensive?` behind its three `.undef` arms
- installation at `push_local_decl`/`push_let_decl`, which covers every
  in-crate telescope
- local instances carried on `LocalCtxSnapshot`, hence on every
  `MetavarDecl`, so `with_mvar_context` reinstalls them
- `get_instances` appends matching locals between the priority sort and
  the reverse, so locals are tried first — the oracle's own ordering
- the synth record's new `fvars` field, without which the mechanism has
  no differential channel at this tier

## Verification

Meta tier: the synthesis corpus grew from 26 to 32 records. The
elaboration corpus is unchanged at 117, byte-identical.

The neutrality gate is **measured, not structural** — the producer sits
at the meta-tier telescopes, so an existing synthesis with a class-typed
fvar in scope could have moved.

Two things are stated rather than claimed as test kills: the `is_class`
call's position outside the `mem::take` window (guarded by comment and
review, since moving it is still correct today), and `nonClassFvar`'s
inability to kill a constant-true `is_class` (the unit test does that).

https://claude.ai/code/session_01MdUSj32wrx862QVNCypLnh
BODY
)"
```

Then follow the standing merge workflow: merge on green CI, verify the
merge landed, and delete the branch.

---

## Self-Review

**Spec coverage.** Every section of `2026-09-09-local-instances-design.md`
maps to a task: § Data model → Tasks 2–4; § `is_class` → Task 3; § Two
oracle filters → Task 4 (implementation-detail, vacuous) and Task 6
(erasure, faithful non-application); § Consumption → Task 6; § One
documented invariant this falsifies → Task 7; § Verification → Tasks 1, 8;
§ Neutrality gate → Task 9; § Seams and § Non-goals → Task 10; § What P5
inherits → Task 10 Step 2.

**Two corrections applied to this plan's own front matter**, found while
writing the tasks. Both are recorded rather than only fixed, because each
is a claim an executor might otherwise re-derive the wrong way:

1. The **Architecture** paragraph and the **File Structure** table first
   listed `assign.rs::forall_bounded_telescope` as a third install site.
   It is **not** a code change: it already mints its fvars through
   `push_local_decl` (`assign.rs:645`), so Task 4 covers it with a test
   rather than an edit. Both now say two chokepoints, and `assign.rs` is
   modified only if that test reveals otherwise.
2. The plan has **10 tasks, not the 11** the spec estimated. The spec
   listed `MetavarDecl.localInstances` and the telescope install as
   separate items; both collapsed into existing structures —
   `MVarDecl.lctx` is already an `Arc<LocalCtxSnapshot>`, and the
   telescope already routes through the chokepoint.

**Placeholder scan.** No `TBD`/`TODO`/"similar to Task N". Three steps
say **read before writing** (`app_fn`'s spelling in `leanr_meta`,
`isClassQuickConst?`'s exact arms, `DEFAULT_INSTANCE_PRIORITY`'s
existence) rather than inventing a name — these are deliberate: guessing
an identifier that does not exist is worse than directing the executor to
the one that does.

**Type consistency.** `LocalInstance { class_name, fvar, at_depth }`,
`LocalInstanceStack::{push, truncate_to, entries, replace, to_vec}`,
`ClassTable::is_class_name`, `MetaCtx::{is_class, is_class_quick,
is_class_quick_const, is_class_expensive, install_local_instance_for}`,
`LocalCtxSnapshot::{new/3, parts/3, local_instances}`,
`MetaCtx::local_instance_candidate` — each is defined once and used with
the same spelling and arity everywhere it recurs.

**Honesty ledger** — three places this plan declines to claim a kill,
because the repo's recurring defect is briefs that name mutations their
tests do not kill:
- Task 3 Step 6, row 4: `Sort` returning `Undef` may not be observable
  from the result alone.
- Task 6 Step 5, last row: moving `is_class` inside the `mem::take`
  window is still correct today; guarded by comment and review.
- Task 8 Step 5, last row: `nonClassFvar` does not discriminate a
  constant-true `is_class`.
