# M4c-1 P2: command elaborator for a single declaration — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** `CommandElab::elab_decl` elaborates one non-recursive `def`/`theorem`/`abbrev`/`opaque`/`axiom`/`example` command into kernel-admitted constants that equal the oracle's exactly, gated by a 79-record differential corpus.

**Architecture:** A new `leanr_elab::command` module. `DefView` decodes the syntax and raises named seams. Each declaration gets one `TermElabM` scope over a fresh scratch `Store`: header, then body, then level params, then the unassigned-mvar check, then nested-proof abstraction. The scope returns the `Declaration`s, and they are committed through P1's `Environment::add_decl_in`; an `example` only gets `check_declaration`. Three cross-cutting term-elaborator fixes land first because the declaration corpus depends on them:
- oracle first lines for type mismatches,
- unassigned-mvar diagnostics,
- per-name binder-group types.

**Tech Stack:** Rust (workspace crates `leanr_elab`, `leanr_meta`, `leanr_kernel`, `leanr_syntax`), Lean 4 `v4.33.0-rc1` as the oracle (fixture generation only), `serde_json` in tests.

**Spec:** `docs/superpowers/specs/2026-10-03-m4c1-single-decl-design.md`, including Amendment 1 and the Amendment 2 committed with this plan. P1 (the declaration substrate) landed in #70 (`472491a`). Read the spec's "The oracle model" and both amendments before starting.

## Global Constraints

- Pinned oracle: `leanprover/lean4:v4.33.0-rc1`. Every oracle citation in code is opened against `~/.elan/toolchains/leanprover--lean4---v4.33.0-rc1/src/lean/` before it is written. Cites drift by 1-25 lines (see the leanr-oracle-citations memory), so open the line.
- `leanr_meta/src` changes are allowed only as additive accessors that `leanr_elab` needs (the M4b accessor precedent). This plan needs none: every `leanr_meta` API it uses is already `pub`.
- `leanr_kernel` is untouched. It is the TCB.
- Named-seam discipline: every out-of-scope input returns `ElabError::UnsupportedSyntax("<what> — <slice label>")`, never a panic, never a wrong `Ok`, never an unrelated error. The slice labels are `M4c-2` (command loop, namespaces, auto-bound) and `later M4` (everything else).
- Temporary task seams use exactly the label `not yet ported (M4c-1 P2 Task N)`. Task 10 adds a test that no such label survives.
- Build only under `/workspace` (`target/`), never `/tmp`. `/tmp` is a 20Gi EmptyDir, and filling it evicts the pod.
- Before every push, run `mise run ci` and block on it in-turn (fmt, clippy `-D warnings`, tests). Never background it and end the turn.
- Every task's mutation list is executed for real: apply the mutation, run the named test, confirm it FAILS, then revert. Record the outcomes in the task's commit body. A brief's test is not trusted until a mutation fails it.
- Rule explicitly on every DONE_WITH_CONCERNS item. P1's final review found that a concern a task reviewer had called "benign" was a silent wrong `Ok`.
- Fixtures are regenerated only with the mise tasks. CI never installs Lean, and the committed JSONL is the whole input.
- Style: match the surrounding code. Doc comments cite the oracle line they port. Tests in `leanr_elab` integration files use `mod support;` (`crates/leanr_elab/tests/support/mod.rs`).

## Review Focus

These are the inputs most likely to bite a user that the happy-path corpus does not exercise. Each one has a test in the task that owns the code.

1. **An unknown identifier or universe in a declaration header** is auto-bound by the oracle (`def ab (a : α) : α := a` succeeds with `u_1`), so leanr must NOT report "Unknown identifier" there. It must raise the auto-bound seam. In the body, the same identifier is a real error (`err/unknownIdBody`). → Task 6 tests `header_unknown_ident_is_the_auto_bound_seam` and `header_unknown_universe_is_the_auto_bound_seam`.
2. **A dotted or `_root_` declaration name** (`def Foo.bar`) opens a namespace for the body in the oracle, so leanr must seam it rather than elaborate it at the root. → Task 5 test `dotted_decl_name_is_an_m4c2_seam`.
3. **Self-reference**, including a dotted use (`sr.foo`), must seam even though leanr has no recursion support to fall back on. Otherwise it surfaces as "Unknown identifier", which reads as a real oracle error. → Task 5 test `self_reference_is_a_recursion_seam`.
4. **Non-declaration and unsupported commands** (`instance`, `structure`, `mutual`, `#check`, `namespace`) must return a named seam, never panic. → Task 5 test `unsupported_commands_are_named_seams`.
5. **Two error infos matching the same pending set:** the oracle logs the MOST RECENT registration first (`mvarErrorInfos` is a consed `List`). Iterating leanr's `Vec` oldest-first would report the wrong argument. → Task 4 test `most_recent_error_info_is_reported_first` (`pick _ _` → `y`, not `x`).

## Plan-time oracle facts

Every corpus record below was run through the final `dump_decls.lean` (Task 1) on 2026-10-03. Facts that shaped this plan, and are recorded in spec Amendment 2:

- **Async theorems report through snapshot tasks.** With `Elab.async=true`, every well-formed theorem takes `elabAsync`. `levelMVarToParamHeaders` runs BEFORE the `!type.hasMVar` test (`MutualDef.lean:1239-1247`), so header level mvars no longer block it. Its body errors go to `Command.State.snapshotTasks`, not `messages`. Without walking them, `theorem tx … := <ill-typed>` dumps as `consts: []` with no error.
- **The theorem signature check uses the type only.** `elabAsync` runs `sortDeclLevelParams` on the header type alone (`MutualDef.lean:1281-1291`). `theorem ta.{u} : True := (fun (_ : Sort u) => True.intro) PUnit.{u}` therefore fails with `unused universe parameter 'u'`.
- **`u_N` order depends on the path.**
  - For a theorem or a Prop-typed def, header level mvars become params in `levelMVarToParamHeaders`, which records them in the header's `levelNames`. `sortDeclLevelParams` then treats them as USER names, in declaration order: `u_1 … u_9, u_10, u_11`.
  - For other defs, they are converted later (`levelMVarToParamTypesPreDecls`, under `withLevelNames allUserLevelNames`). They count as leftovers and sort lexicographically: `u_1, u_10, u_11, u_2, …`.
  - Axioms follow the def rule (`elabAxiom` sorts against the original user names).
- **The value's binder types are `cleanupAnnotations`'d.** `elabFunValues` reopens the header with `forallBoundedTelescope … (cleanupAnnotations := true)` (`MutualDef.lean:536`). So `def oe (n : optParam Nat Nat.zero) : Nat := n` has an `optParam` binder in its TYPE but a `Nat` binder in its VALUE.
- **A binder group's type is elaborated once PER NAME** (`toBinderViews` and `elabBinderViews`, `Binders.lean:208-223`). So `(α β : Sort _)` gives `u_1, u_2`. leanr's `push_binder_group` elaborated it once per group, which is a pre-existing divergence in `forall`/`depArrow`/`let` binders. Fixed in Task 3.
- **Compile errors are logged as errors.** `Elab0` lacks the compiler's runtime support (`Nat.succ` compiles to `Nat.add`). So `def x := Nat.succ Nat.zero` logs "Unknown constant `Nat.add`" from codegen even though the constant is added. Compilation is a spec seam, and the corpus avoids values whose code generation needs missing constants.
- **The constant map is unordered.** The dumper emits `consts` sorted by `Name.lt`. The gate sorts leanr's admitted names the same way (`leanr_meta::name_cmp`) and checks the admission order (every `_proof_N` before the main declaration) separately.
- **Parser gap:** leanr's parser has no `binderDefault` (`(n : Nat := Nat.zero)` fails at `:=`). Those records are excluded, and the explicit `optParam` spelling covers the same elaborator path.
- **The unassigned-mvar error lines need state leanr lacked:**
  - `mvarArgNames` (`App.lean:428`, `:1277`)
  - the `.custom` error kind (`registerFailedToInferBinderTypeInfo`, `Binders.lean:177-183`; `registerFailedToInferDefTypeInfo`, `MutualDef.lean:123-137`)
  - `LevelMVarErrorInfo` (`TermElabM.lean:146-151`)
  - most-recent-first iteration (`:871`, `:942`)

  Task 4 ports all four.
- **`Type mismatch` vs `Application type mismatch`:** `ensureArgType` passes `f?` (`App.lean:54-62`), which routes to `throwAppTypeMismatch` (`Meta/Check.lean:250-270`). That message says "The last" when the argument already occurs among `f`'s arguments (`dep Nat Nat`) and "The argument" otherwise.

---

### Task 1: Oracle dumper, decl corpus fixture, parse gate

**Files:**
- Create: `tests/fixtures/elab/dump_decls.lean`
- Create (generated): `tests/fixtures/elab/decl-queries.jsonl`
- Modify: `mise.toml` (new task `fixtures:regen-decls`; add it to `fixtures:regen`'s `depends_post`)
- Modify: `crates/leanr_elab/tests/support/mod.rs` (add `parse_command`)
- Create: `crates/leanr_elab/tests/oracle_decl.rs`

**Interfaces:**
- Consumes: the committed `tests/fixtures/elab/Elab0.olean`.
- Produces:
  - `tests/fixtures/elab/decl-queries.jsonl`, 79 records. Shapes: `{"id","src","consts":[C…]}` and `{"id","src","err"}`, with `C` as documented in the dumper's module doc.
  - `pub fn parse_command(src: &str) -> (leanr_syntax::ParseResult, leanr_syntax::tree::SyntaxNode)` in the test support. It parses `src` with `leanr_syntax::parse_module(src, &leanr_syntax::builtin::snapshot())`, asserts no parse errors and exactly one command (ignoring the `Lean.Parser.Module.header` and `Lean.Parser.Command.eoi` nodes), and returns the tree and that command node.

- [ ] **Step 1: Write the dumper.** Create `tests/fixtures/elab/dump_decls.lean` with exactly this content. It was run at plan time, and all 79 records come out clean with nothing on stderr. The encoder section is a verbatim copy of `dump_elab.lean`'s, which is the existing convention: `dump_elab.lean` copies `dump_defeq.lean`'s.

```lean
/- Emits the M4c-1 declaration corpus (spec
`docs/superpowers/specs/2026-10-03-m4c1-single-decl-design.md` § Harness):
for each `(id, src)`, the COMMAND `src` is parsed and elaborated with
`Lean.Elab.Command.elabCommandTopLevel` against the Elab0 environment, and
the constants it added are dumped.

Runs with LEAN_PATH set to this directory so `Elab0` resolves to the
committed fixture and nothing else (the `dump_elab.lean` hermetic contract).

`Elab.async` is set to `true`, matching the `lean` command line
(`CoreM.lean:35`): a theorem then takes `elabAsync`
(`MutualDef.lean:1266`). An async body reports its errors through
`Command.State.snapshotTasks`, NOT `messages`, so the error scan below walks
both (an async error left out reads as a silently dropped theorem).

Record shapes:
  {"id","src","consts":[C...]}   -- the command added these constants
  {"id","src","err":<string>}    -- the first error's first line
where `C` is
  {"name","kind":"defn"|"thm"|"opaque"|"axiom","levelParams":[..],
   "type":E, "value":E?, "hints":"opaque"|"abbrev"|{"regular":N}?,
   "safety":"safe"|"unsafe"|"partial"?, "unsafe":bool?, "all":[..]?}
and `E` is the canonical expr scheme of `dump_elab.lean` (copied verbatim
below). `consts` is sorted by `Name.lt`: the environment's constant map
is unordered, so the dumper cannot observe insertion order. The leanr
gate sorts its own admitted names the same way and checks the admission
order (every `_proof_N` before the main declaration) separately.

A `declQueries` command that logs an error is reported on stderr and
DROPPED (the gate's floor catches a shrinking corpus); a `declErrQueries`
command that elaborates cleanly is reported on stderr and dropped.
-/
-- NOT `import Elab0`: see `dump_elab.lean` (Elab0 is prelude-mode and
-- collides with the real `Init` this file needs).
import Lean
open Lean Lean.Meta Lean.Elab

-- ===== canonical expr/level encoder (dump_defeq.lean's scheme + lmvar) =====

/-- `default`->d, `implicit`->i, `strictImplicit`->s, `instImplicit`->c
(binder NAMES are erased everywhere; only this kind letter survives). -/
def biStr : BinderInfo → String
  | .default => "d"
  | .implicit => "i"
  | .strictImplicit => "s"
  | .instImplicit => "c"

/-- Per-query numbering state for mvars/fvars/level-mvars, first-
occurrence order. Shared across one query's whole encode call (there is
only ever ONE side per elab query — `exp` — unlike `dump_defeq.lean`'s
`in`/`out` pair, so there is no `encPair`-style threading need here;
`EncSt` is still its own structure, freshly `{}`-initialized per query,
mirroring `dump_defeq.lean`'s naming for the same role). -/
structure EncSt where
  fvars : Std.HashMap FVarId Nat := {}
  fNext : Nat := 0
  mvars : Std.HashMap MVarId Nat := {}
  mNext : Nat := 0
  lvars : Std.HashMap LMVarId Nat := {}
  lNext : Nat := 0

abbrev EncM := StateM EncSt

partial def encLevel : Level → EncM Json
  | .zero => pure <| Json.mkObj [("k", "zero")]
  | .succ u => do
    let uj ← encLevel u
    pure <| Json.mkObj [("k", "succ"), ("u", uj)]
  | .max a b => do
    let aj ← encLevel a
    let bj ← encLevel b
    pure <| Json.mkObj [("k", "max"), ("a", aj), ("b", bj)]
  | .imax a b => do
    let aj ← encLevel a
    let bj ← encLevel b
    pure <| Json.mkObj [("k", "imax"), ("a", aj), ("b", bj)]
  | .param n => pure <| Json.mkObj [("k", "param"), ("n", n.toString (escape := false))]
  | .mvar id => do
    let st ← get
    match st.lvars.get? id with
    | some n => pure <| Json.mkObj [("k", "lmvar"), ("i", n)]
    | none =>
      let n := st.lNext
      modify fun s => { s with lvars := s.lvars.insert id n, lNext := n + 1 }
      pure <| Json.mkObj [("k", "lmvar"), ("i", n)]

partial def encExpr : Expr → EncM Json
  | .bvar i => pure <| Json.mkObj [("k", "bvar"), ("i", i)]
  | .fvar id => do
    let st ← get
    match st.fvars.get? id with
    | some n => pure <| Json.mkObj [("k", "fvar"), ("i", n)]
    | none =>
      let n := st.fNext
      modify fun s => { s with fvars := s.fvars.insert id n, fNext := n + 1 }
      pure <| Json.mkObj [("k", "fvar"), ("i", n)]
  | .mvar id => do
    let st ← get
    match st.mvars.get? id with
    | some n => pure <| Json.mkObj [("k", "mvar"), ("i", n)]
    | none =>
      let n := st.mNext
      modify fun s => { s with mvars := s.mvars.insert id n, mNext := n + 1 }
      pure <| Json.mkObj [("k", "mvar"), ("i", n)]
  | .sort u => do
    let uj ← encLevel u
    pure <| Json.mkObj [("k", "sort"), ("u", uj)]
  | .const n us => do
    let usj ← us.mapM encLevel
    pure <| Json.mkObj
      [("k", "const"), ("n", n.toString (escape := false)), ("us", Json.arr usj.toArray)]
  | .app f a => do
    let fj ← encExpr f
    let aj ← encExpr a
    pure <| Json.mkObj [("k", "app"), ("f", fj), ("a", aj)]
  | .lam _ t b bi => do
    let tj ← encExpr t
    let bj ← encExpr b
    pure <| Json.mkObj [("k", "lam"), ("bi", biStr bi), ("t", tj), ("b", bj)]
  | .forallE _ t b bi => do
    let tj ← encExpr t
    let bj ← encExpr b
    pure <| Json.mkObj [("k", "pi"), ("bi", biStr bi), ("t", tj), ("b", bj)]
  | .letE _ t v b nd => do
    let tj ← encExpr t
    let vj ← encExpr v
    let bj ← encExpr b
    pure <| Json.mkObj [("k", "let"), ("t", tj), ("v", vj), ("b", bj), ("nd", nd)]
  | .lit (.natVal n) => pure <| Json.mkObj [("k", "lit"), ("n", toString n)]
  | .lit (.strVal s) => pure <| Json.mkObj [("k", "str"), ("v", s)]
  | .proj s i e => do
    let ej ← encExpr e
    pure <| Json.mkObj [("k", "proj"), ("s", s.toString (escape := false)), ("i", i), ("e", ej)]
  | .mdata _ e => encExpr e -- mdata ERASED: recurse straight through

-- ===== query corpus (Task 4: `str` slice only) =====

def hintsJ : ReducibilityHints → Json
  | .opaque => "opaque"
  | .abbrev => "abbrev"
  | .regular h => Json.mkObj [("regular", toJson h.toNat)]

def safetyStr : DefinitionSafety → String
  | .safe => "safe" | .unsafe => "unsafe" | .partial => "partial"

def nameJ (n : Name) : Json := n.toString (escape := false)

def namesJ (ns : List Name) : Json := Json.arr (ns.map nameJ).toArray

def constJ (ci : ConstantInfo) : Json :=
  let enc (e : Expr) : Json := (encExpr e).run' {}
  let base : List (String × Json) :=
    [("name", nameJ ci.name), ("levelParams", namesJ ci.levelParams), ("type", enc ci.type)]
  let kind (k : String) : String × Json := ("kind", Json.str k)
  match ci with
  | .defnInfo v => Json.mkObj (kind "defn" :: base ++
      [("value", enc v.value), ("hints", hintsJ v.hints),
       ("safety", Json.str (safetyStr v.safety)), ("all", namesJ v.all)])
  | .thmInfo v => Json.mkObj (kind "thm" :: base ++
      [("value", enc v.value), ("all", namesJ v.all)])
  | .opaqueInfo v => Json.mkObj (kind "opaque" :: base ++
      [("value", enc v.value), ("unsafe", toJson v.isUnsafe), ("all", namesJ v.all)])
  | .axiomInfo v => Json.mkObj (kind "axiom" :: base ++ [("unsafe", toJson v.isUnsafe)])
  | _ => Json.mkObj (kind "other" :: base)

-- ===== query corpus (spec § Corpus; every record probed at plan time) =====

def declQueries : List (String × String) := [
  ("kind/def", "def d1 : Nat := Nat.zero"),
  ("kind/theorem", "theorem t1 : True := True.intro"),
  ("kind/abbrev", "abbrev a1 : Nat := Nat.zero"),
  ("kind/opaque", "opaque o1 : Nat := Nat.zero"),
  ("kind/axiom", "axiom ax1 : Nat"),
  ("kind/example", "example : Nat := Nat.zero"),
  ("kind/exampleParams", "example (x : Nat) : Nat := x"),
  ("kind/propDef", "def dp : True := True.intro"),
  ("kind/abbrevProp", "abbrev abp : True := True.intro"),
  ("kind/opaqueProp", "opaque opp : True := True.intro"),
  ("type/inferred", "def inf1 := List.cons Nat.zero List.nil"),
  ("type/unify", "def uni1 : List Nat := List.nil"),
  ("type/lamValue", "def lam1 : Nat → Nat := fun x => x"),
  ("type/implicitBinder", "def ib {α : Type} (a : α) : α := a"),
  ("type/instBinder", "def ii {a : Type} [Wrap a] (x : a) : a := Wrap.wrap x"),
  ("type/optParamCleanup", "def oe (n : optParam Nat Nat.zero) : Nat := n"),
  ("type/headerMVarSolvedByBody", "def dv : Sort _ := Nat"),
  ("type/groupHoles", "def tw (α β : Sort _) (a : α) (b : β) : α := a"),
  ("univ/explicit1", "def ue1.{u} (α : Sort u) (a : α) : α := a"),
  ("univ/explicit2", "def ue2.{u, v} (α : Sort u) (β : Sort v) (a : α) (b : β) : α := a"),
  ("univ/sortHole", "def us1 (α : Sort _) (a : α) : α := a"),
  ("univ/idBody", "def ub1 := @id"),
  ("univ/order", "def uo.{v} (α : Sort _) (β : Sort v) (a : α) (b : β) : β := b"),
  ("univ/orderRev", "def uo2.{v, u} (α : Sort u) (β : Sort v) (a : α) (b : β) : β := b"),
  ("univ/skipUsedName", "def sk.{u_1} (α : Sort u_1) (β : Sort _) (b : β) : β := b"),
  ("univ/defElevenLex", "def el (a1 : Sort _) (a2 : Sort _) (a3 : Sort _) (a4 : Sort _) (a5 : Sort _) (a6 : Sort _) (a7 : Sort _) (a8 : Sort _) (a9 : Sort _) (a10 : Sort _) (a11 : Sort _) : Nat := Nat.zero"),
  ("univ/thmElevenNumeric", "theorem el2 (a1 : Sort _) (a2 : Sort _) (a3 : Sort _) (a4 : Sort _) (a5 : Sort _) (a6 : Sort _) (a7 : Sort _) (a8 : Sort _) (a9 : Sort _) (a10 : Sort _) (a11 : Sort _) : True := True.intro"),
  ("univ/propDefElevenNumeric", "def el3 (a1 : Sort _) (a2 : Sort _) (a3 : Sort _) (a4 : Sort _) (a5 : Sort _) (a6 : Sort _) (a7 : Sort _) (a8 : Sort _) (a9 : Sort _) (a10 : Sort _) (a11 : Sort _) : True := True.intro"),
  ("univ/thmSortHole", "theorem ut1 (α : Sort _) (a : α) : Eq a a := rfl"),
  ("univ/thmExplicit", "theorem te.{u} (α : Sort u) (a : α) : Eq a a := rfl"),
  ("univ/thmUserAndHole", "theorem tuh.{v} (α : Sort _) (β : Sort v) (b : β) : Eq b b := rfl"),
  ("univ/defHeaderUnivByBody", "def dx (α : Sort _) : Nat := (fun (_ : Type) => Nat.zero) α"),
  ("univ/axiomSortHole", "axiom as1 (α : Sort _) : α"),
  ("univ/axiomElevenLex", "axiom ael (a1 : Sort _) (a2 : Sort _) (a3 : Sort _) (a4 : Sort _) (a5 : Sort _) (a6 : Sort _) (a7 : Sort _) (a8 : Sort _) (a9 : Sort _) (a10 : Sort _) (a11 : Sort _) : Nat"),
  ("univ/abbrevUniv", "abbrev abu.{u} (α : Sort u) : Sort u := α"),
  ("univ/thmLevelOnlyBody", "theorem tl : True := (fun (_ : Sort 1) => True.intro) Nat"),
  ("height/pick", "def hc := pick Nat.zero Nat.zero"),
  ("height/id", "def hid := id Nat.zero"),
  ("height/overThm", "def ht := @eq_of_heq"),
  ("height/abbrev", "abbrev ab2 := pick Nat.zero"),
  ("height/explicitTy", "def dit : Nat → Nat := id"),
  ("np/one", "def np1 (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl"),
  ("np/trivial", "def np0 (n : Nat) : PProd Nat (Eq n n) := PProd.mk n rfl"),
  ("np/shared", "def np2 (n : Nat) : PProd (Eq (Nat.succ n) (Nat.succ n)) (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk rfl rfl"),
  ("np/distinct", "def np3 (n : Nat) : PProd (Eq (Nat.succ n) (Nat.succ n)) (Eq (Nat.succ (Nat.succ n)) (Nat.succ (Nat.succ n))) := PProd.mk rfl rfl"),
  ("np/binder", "def np4 : (n : Nat) → PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := fun n => PProd.mk n rfl"),
  ("np/univ", "def np5.{u} (α : Sort u) (a : α) : PProd α (Eq (id a) (id a)) := PProd.mk a rfl"),
  ("np/theorem", "theorem np6 (n : Nat) : True := (fun (_ : PProd Nat (Eq (Nat.succ n) (Nat.succ n))) => True.intro) (PProd.mk n rfl)"),
  ("np/example", "example (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl"),
  ("np/abbrev", "abbrev np7 (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl"),
  ("np/opaque", "opaque np8 (n : Nat) : PProd Nat (Eq (Nat.succ n) (Nat.succ n)) := PProd.mk n rfl"),
  ("np/twoBinders", "def npb (n : Nat) (m : Nat) : PProd Nat (Eq (Nat.succ m) (Nat.succ m)) := PProd.mk n rfl"),
  ("np/lambdaArg", "def npl (n : Nat) : Nat := (fun (_ : Eq (Nat.succ n) (Nat.succ n)) => n) rfl"),
  ("np/nestedTwice", "def npn (n : Nat) : PProd Nat (PProd Nat (Eq (Nat.succ n) (Nat.succ n))) := PProd.mk n (PProd.mk n rfl)")
]

def declErrQueries : List (String × String) := [
  ("err/already", "def pick : Nat := Nat.zero"),
  ("err/thmAlready", "theorem eq_of_heq : True := True.intro"),
  ("err/univDup", "def udup.{u, u} : Nat := Nat.zero"),
  ("err/unusedUniv", "def uu.{u} : Nat := Nat.zero"),
  ("err/unusedUniv2", "def uu2.{u, v} (α : Sort v) : Sort v := α"),
  ("err/axiomUnusedUniv", "axiom au.{u} : Nat"),
  ("err/thmUnivValueOnly", "theorem ta.{u} : True := (fun (_ : Sort u) => True.intro) PUnit.{u}"),
  ("err/mismatch", "def em : Nat := True.intro"),
  ("err/exampleMismatch", "example : Nat := True.intro"),
  ("err/thmTypeNotProp", "theorem tnp : Nat := Nat.zero"),
  ("err/propDefHeaderUniv", "def dxp (α : Sort _) : True := (fun (_ : Type) => True.intro) α"),
  ("err/appLast", "def dl : Nat := dep Nat Nat"),
  ("err/thmHeaderUnivByBody", "theorem tx (α : Sort _) : True := (fun (_ : Type) => True.intro) α"),
  ("err/unassignedImplicit", "def eu := id"),
  ("err/holeArg", "def eh2 : Nat := pick _ Nat.zero"),
  ("err/holeBare", "def eh3 := _"),
  ("err/binderHole", "def eh (x : _) : Nat := Nat.zero"),
  ("err/funBinderType", "def eh4 := fun x => x"),
  ("err/defTypeHole", "def eh5 : _ := Nat.zero"),
  ("err/thmTypeHole", "theorem thb : _ := True.intro"),
  ("err/axiomBinderHole", "axiom ah (x : _) : Nat"),
  ("err/axiomTypeHole", "axiom ahole : _"),
  ("err/levelMVarValue", "def lv : Nat := (fun (_ : Sort _) => Nat.zero) PUnit"),
  ("err/levelMVarThm", "theorem tc : True := (fun (_ : Sort _) => True.intro) PUnit"),
  ("err/unknownIdBody", "def uib : Nat := nope")
]

/-- Elaborate one command; `.inl firstErrorLine` or `.inr newConstants`. -/
def runCmd (env : Environment) (opts : Options) (src : String) :
    IO (Except String (Except String (Array Json))) := do
  match Lean.Parser.runParserCategory env `command src with
  | .error msg => return .error s!"parse error: {msg}"
  | .ok stx =>
    let ctx : Command.Context :=
      { fileName := "<dump_decls>", fileMap := FileMap.ofString src, snap? := none, cancelTk? := none }
    let r ← (((Command.elabCommandTopLevel stx).run ctx).run (Command.mkState env {} opts)).toBaseIO
    match r with
    | .error ex => return .ok (.error ((← ex.toMessageData.toString).splitOn "\n" |>.headD ""))
    | .ok ((), s) =>
      let snapMsgs := s.snapshotTasks.toList.flatMap fun t =>
        t.get.getAll.toList.flatMap fun snap => snap.diagnostics.msgLog.toList
      let errs := (s.messages.toList ++ snapMsgs).filter (·.severity == .error)
      match errs.head? with
      | some m => return .ok (.error (((← m.data.toString).splitOn "\n").headD ""))
      | none =>
        let news := (s.env.constants.map₂.toList.map (·.1)).toArray.qsort Name.lt
        return .ok (.ok (news.filterMap fun n => (s.env.find? n).map constJ))

unsafe def main (_args : List String) : IO Unit := do
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules #[{ module := `Elab0 }] {} (trustLevel := 0) (loadExts := true)
  let opts : Options := Elab.async.set {} true
  for (id, src) in declQueries do
    match ← runCmd env opts src with
    | .error msg => IO.eprintln s!"dump_decls: {id}: {msg}"
    | .ok (.error e) => IO.eprintln s!"dump_decls: {id} logged an error: {e}"
    | .ok (.ok cs) =>
      IO.println <| Json.compress <| Json.mkObj [("id", id), ("src", src), ("consts", Json.arr cs)]
  for (id, src) in declErrQueries do
    match ← runCmd env opts src with
    | .error msg => IO.eprintln s!"dump_decls: {id}: {msg}"
    | .ok (.ok _) => IO.eprintln s!"dump_decls: {id} was expected to fail but elaborated"
    | .ok (.error e) =>
      IO.println <| Json.compress <| Json.mkObj [("id", id), ("src", src), ("err", e)]
```

- [ ] **Step 2: Add the mise task.** In `mise.toml`, after `[tasks."fixtures:regen-elab-op"]`, add:

```toml
[tasks."fixtures:regen-decls"]
description = "Regenerate the M4c-1 declaration corpus (dump_decls.lean elaborates each command against Elab0 with Elab.async=true and dumps the constants it added, or the first error line). Needs the elan toolchain; never runs in CI."
depends = ["elan:bootstrap"]
run = [
  "sh -c 'cd tests/fixtures/elab && LEAN_PATH=$PWD lean --run dump_decls.lean > decl-queries.jsonl'",
]
```

and change `fixtures:regen`'s `depends_post` to `["fixtures:regen-notation", "fixtures:regen-elab", "fixtures:regen-elab-op", "fixtures:regen-decls"]`.

- [ ] **Step 3: Generate the fixture.**

Run: `mise run fixtures:regen-decls && wc -l tests/fixtures/elab/decl-queries.jsonl`
Expected: `79 tests/fixtures/elab/decl-queries.jsonl`. Nothing is printed on stderr: any `dump_decls: …` line means a record was dropped, so stop and investigate.

Spot-check against the plan-time probe:

Run: `jq -c 'if .err then [.id,.err] else [.id,(.consts|map([.name,.levelParams]))] end' tests/fixtures/elab/decl-queries.jsonl | grep -E 'univ/defElevenLex|univ/thmElevenNumeric|np/distinct|err/appLast'`
Expected:
```
["univ/defElevenLex",[["el",["u_1","u_10","u_11","u_2","u_3","u_4","u_5","u_6","u_7","u_8","u_9"]]]]
["univ/thmElevenNumeric",[["el2",["u_1","u_2","u_3","u_4","u_5","u_6","u_7","u_8","u_9","u_10","u_11"]]]]
["np/distinct",[["np3",[]],["np3._proof_1",[]],["np3._proof_2",[]]]]
["err/appLast","Application type mismatch: The last"]
```

- [ ] **Step 4: Write the failing parse test.** Create `crates/leanr_elab/tests/oracle_decl.rs`:

```rust
//! M4c-1 P2 declaration differential gate (spec
//! `docs/superpowers/specs/2026-10-03-m4c1-single-decl-design.md`
//! § Harness). Every committed `{id, src, consts|err}` record of
//! `decl-queries.jsonl` (`tests/fixtures/elab/dump_decls.lean`) is parsed
//! by leanr's own parser as exactly one command.

mod support;

/// `wc -l tests/fixtures/elab/decl-queries.jsonl` at the last deliberate
/// regen. `>=`: adding a record is a one-line bump, not a failing gate.
const CORPUS_FLOOR: usize = 79;

#[test]
fn decl_corpus_sources_parse_as_one_command() {
    let text = std::fs::read_to_string(support::fixture_in("elab", "decl-queries.jsonl"))
        .expect("committed decl corpus");
    let mut n = 0;
    for line in text.lines().filter(|l| !l.trim().is_empty()) {
        let q: serde_json::Value = serde_json::from_str(line).expect("valid JSONL");
        let src = q["src"].as_str().expect("src field");
        let _ = support::parse_command(src);
        n += 1;
    }
    assert!(n >= CORPUS_FLOOR, "decl corpus shrank: {n} < {CORPUS_FLOOR}");
}
```

- [ ] **Step 5: Run it to confirm it fails.**

Run: `cargo test -p leanr_elab --test oracle_decl`
Expected: compile error, `cannot find function parse_command in module support`.

- [ ] **Step 6: Add `parse_command` to the test support.** Append to `crates/leanr_elab/tests/support/mod.rs`:

```rust
/// Parse `src` as ONE command (no `prelude`/`import` header) with the
/// builtin grammar, the way `dump_decls.lean` runs
/// `runParserCategory env `command src`. Panics on a parse error, or if
/// `src` holds anything but exactly one command: a silent second command
/// would be skipped by the gate. Returns the parse result (its `tree`
/// owns the `KindInterner`) and the command node.
pub fn parse_command(
    src: &str,
) -> (leanr_syntax::ParseResult, leanr_syntax::tree::SyntaxNode) {
    let parsed = leanr_syntax::parse_module(src, &leanr_syntax::builtin::snapshot());
    assert!(
        parsed.errors.is_empty(),
        "leanr parse errors for {src:?}: {:?}",
        parsed.errors
    );
    let root = parsed.tree.root();
    let cmds: Vec<leanr_syntax::tree::SyntaxNode> = root
        .children()
        .filter(|n| {
            let k = parsed.tree.kinds.name(n.kind());
            k != "Lean.Parser.Module.header" && k != "Lean.Parser.Command.eoi"
        })
        .collect();
    assert_eq!(cmds.len(), 1, "{src:?} must be exactly one command");
    let cmd = cmds[0].clone();
    (parsed, cmd)
}
```

If `SyntaxNode` has no `children()` iterator, use `children_with_tokens().filter_map(|el| el.into_node())`; `leanr_elab::dispatch` uses `children_with_tokens`. Check `crates/leanr_syntax/src/tree.rs` first.

- [ ] **Step 7: Run the test to confirm it passes.**

Run: `cargo test -p leanr_elab --test oracle_decl`
Expected: `test decl_corpus_sources_parse_as_one_command ... ok`.

Mutation: change `CORPUS_FLOOR` to `80`, confirm it FAILS ("decl corpus shrank"), then revert.

- [ ] **Step 8: Commit.**

```bash
git add tests/fixtures/elab/dump_decls.lean tests/fixtures/elab/decl-queries.jsonl mise.toml \
  crates/leanr_elab/tests/support/mod.rs crates/leanr_elab/tests/oracle_decl.rs
git commit -m "M4c-1 P2: dump_decls.lean oracle corpus (79 records) + parse gate"
```

### Task 2: Declaration error variants and oracle first lines

**Files:**
- Modify: `crates/leanr_elab/src/error.rs`
- Modify: `crates/leanr_elab/src/coe.rs:76` (construct `TypeMismatch` with `app: None`)
- Modify: `crates/leanr_elab/src/app/args.rs:1054-1063` (`elab_and_add_new_arg`: attach the application context)
- Modify: `crates/leanr_elab/src/lib.rs` (re-export `AppArgMismatch`)
- Create: `crates/leanr_elab/tests/decl_diagnostics_smoke.rs`

**Interfaces:**
- Produces, on `ElabError`:
  - `AlreadyDeclared(String)` → "`` `{n}` has already been declared``"
  - `UniverseAlreadyDeclared(String)` → "a universe level named `` `{u}` `` has already been declared"
  - `UnusedUniverseParam(String)` → "unused universe parameter '{u}'"
  - `TheoremTypeNotProp(String)` → "type of theorem `` `{n}` `` is not a proposition"
  - `UnassignedMVars(String)` and `UnassignedLevelMVars(String)`: the first line, already rendered
  - `Kernel(leanr_kernel::KernelError)` → `None`
- `TypeMismatch` gains the field `app: Option<AppArgMismatch>`, with `pub struct AppArgMismatch { pub f: ExprId, pub arg_already_in_f: bool }`.
- `oracle_first_line` now also answers:
  - `TypeMismatch { app: None, .. }` → "Type mismatch"
  - `app: Some(a)` → "Application type mismatch: The last" if `a.arg_already_in_f`, otherwise "Application type mismatch: The argument"
  - `UnknownIdent(s)` → "Unknown identifier `` `{s}` ``"

The oracle sources:
- `checkNotAlreadyDeclared` (`Elab/DeclModifiers.lean:40-44`)
- `throwAlreadyDeclaredUniverseLevel` (`Elab/Exception.lean:43-44`)
- `sortDeclLevelParams` (`Elab/DeclUtil.lean:79-81`)
- `pushMain` (`Elab/MutualDef.lean:1052-1053`)
- `throwTypeMismatchError` (`Elab/Term/TermElabM.lean:1134-1153`): `f? = none` → `mkTypeMismatchError`, whose first line is "Type mismatch"; `f? = some f` → `Meta.throwAppTypeMismatch f e` (`Meta/Check.lean:250-270`), with `argDescStr` "last…" when `f.getAppArgs.any (· == a)`
- `ensureArgType` (`App.lean:54-62`), which passes `f`

All of these first lines were confirmed by the plan-time decl probe.

- [ ] **Step 1: Write the failing tests.** Create `crates/leanr_elab/tests/decl_diagnostics_smoke.rs`:

```rust
//! M4c-1 P2: term-level oracle first lines that the declaration corpus
//! (`oracle_decl.rs`) relies on. Each string was produced by the oracle in
//! the plan-time decl probe (plan `2026-10-03-m4c1-p2-command-elab.md`).

mod support;

use leanr_syntax::builtin;

/// Elaborate `src` against Elab0 with `elab_term_and_synthesize`; the
/// first line of its error, if any.
fn first_line(src: &str) -> Option<String> {
    let r = support::replay_fixture_in("elab", "Elab0.olean");
    support::with_record_elab(&r, src, &builtin::snapshot(), |elab, elem, kinds| {
        match elab.elab_term_and_synthesize(elem, kinds, None) {
            Ok(_) => None,
            Err(e) => Some(e.oracle_first_line().unwrap_or_else(|| format!("<no line: {e:?}>"))),
        }
    })
}

#[test]
fn ascription_mismatch_is_type_mismatch() {
    // oracle: `def em : Nat := True.intro` -> "Type mismatch" (ensureHasType, f? = none)
    assert_eq!(first_line("(True.intro : Nat)").as_deref(), Some("Type mismatch"));
}

#[test]
fn argument_mismatch_is_application_type_mismatch() {
    // oracle: `def da : Nat := pick True.intro Nat.zero`
    assert_eq!(
        first_line("pick True.intro Nat.zero").as_deref(),
        Some("Application type mismatch: The argument")
    );
}

#[test]
fn argument_already_in_f_says_the_last() {
    // oracle: `def dl : Nat := dep Nat Nat` — `f = dep Nat`, `a = Nat`,
    // `f.getAppArgs.any (· == a)` holds (Meta/Check.lean:254).
    assert_eq!(
        first_line("dep Nat Nat").as_deref(),
        Some("Application type mismatch: The last")
    );
}

#[test]
fn unknown_identifier_first_line() {
    // oracle: `def uib : Nat := nope` -> "Unknown identifier `nope`"
    assert_eq!(first_line("nope").as_deref(), Some("Unknown identifier `nope`"));
}
```

and append to `error.rs`'s `mod tests`:

```rust
    #[test]
    fn declaration_error_first_lines_are_the_oracles() {
        // Each string is the plan-time oracle output for the decl corpus record named.
        assert_eq!(
            ElabError::AlreadyDeclared("pick".into()).oracle_first_line().as_deref(),
            Some("`pick` has already been declared") // err/already
        );
        assert_eq!(
            ElabError::UniverseAlreadyDeclared("u".into()).oracle_first_line().as_deref(),
            Some("a universe level named `u` has already been declared") // err/univDup
        );
        assert_eq!(
            ElabError::UnusedUniverseParam("u".into()).oracle_first_line().as_deref(),
            Some("unused universe parameter 'u'") // err/unusedUniv
        );
        assert_eq!(
            ElabError::TheoremTypeNotProp("tnp".into()).oracle_first_line().as_deref(),
            Some("type of theorem `tnp` is not a proposition") // err/thmTypeNotProp
        );
        assert_eq!(
            ElabError::UnassignedMVars("don't know how to synthesize placeholder".into())
                .oracle_first_line()
                .as_deref(),
            Some("don't know how to synthesize placeholder")
        );
        assert_eq!(
            ElabError::Kernel(leanr_kernel::KernelError::UnknownConstant("x".into()))
                .oracle_first_line(),
            None
        );
    }
```

Check `KernelError::UnknownConstant`'s payload type in `crates/leanr_kernel/src/error.rs` and adjust the constructor argument if needed. Any variant will do: the assertion is that kernel errors have no first line.

- [ ] **Step 2: Run the tests to confirm they fail.**

Run: `cargo test -p leanr_elab --test decl_diagnostics_smoke; cargo test -p leanr_elab --lib error::tests`
Expected: the smoke tests FAIL with `<no line: TypeMismatch { … }>` / `<no line: UnknownIdent(…)>`, and the lib test fails to compile (no `AlreadyDeclared`).

- [ ] **Step 3: Implement the variants.** In `error.rs`:

1. Change the `TypeMismatch` variant to:

```rust
    TypeMismatch {
        expected: ExprId,
        got: ExprId,
        /// `Some` when the mismatch is an application argument's
        /// (`ensureArgType`, `App.lean:54-62`, passes `f?`), which the
        /// oracle reports through `Meta.throwAppTypeMismatch`
        /// (`Meta/Check.lean:250-270`) instead of `mkTypeMismatchError`
        /// (`TermElabM.lean:1151-1153`).
        app: Option<AppArgMismatch>,
    },
```

2. Add these variants before `Postpone` (keep the doc style of the file):

```rust
    /// oracle: `checkNotAlreadyDeclared` (`Elab/DeclModifiers.lean:40-44`),
    /// reached from `expandDeclId` → `mkDeclName` → `applyVisibility`
    /// (`:244-251`). Carries the rendered declaration name.
    AlreadyDeclared(String),
    /// oracle: `throwAlreadyDeclaredUniverseLevel` (`Elab/Exception.lean:43-44`),
    /// from `expandDeclId`'s `.{…}` fold (`Elab/DeclModifiers.lean:326-339`).
    UniverseAlreadyDeclared(String),
    /// oracle: `sortDeclLevelParams` (`Elab/DeclUtil.lean:79-81`).
    UnusedUniverseParam(String),
    /// oracle: `MutualClosure.pushMain` (`Elab/MutualDef.lean:1052-1053`).
    TheoremTypeNotProp(String),
    /// oracle: the first error `logUnassignedUsingErrorInfos`
    /// (`Term/TermElabM.lean:934-958`) logs, rendered to its first line by
    /// `unassigned.rs` (`MVarErrorInfo.logError`, `:901-925`).
    UnassignedMVars(String),
    /// oracle: the first error `logUnassignedLevelMVarsUsingErrorInfos`
    /// (`:997-1013`) logs (`LevelMVarErrorInfo.logError`, `:983-988`), or
    /// `ensureNoUnassignedLevelMVarsAtPreDef`'s fallback
    /// (`PreDefinition/Main.lean:76-97`). First line, rendered.
    UnassignedLevelMVars(String),
    /// The kernel rejected a declaration the elaborator built (`addDecl`).
    /// The oracle's kernel messages start with `(kernel)`; leanr's
    /// `KernelError` has no message layer, so there is no first line.
    Kernel(leanr_kernel::KernelError),
```

3. Add after the `ElabError` enum:

```rust
/// The application context of an argument type mismatch: oracle
/// `ensureArgType`'s `f` (`App.lean:54-62`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AppArgMismatch {
    /// The partial application the argument was being added to.
    pub f: ExprId,
    /// `f.getAppArgs.any (· == a)` (`Meta/Check.lean:254`): the oracle then
    /// says "The last … argument" instead of "The argument".
    pub arg_already_in_f: bool,
}
```

4. `is_oracle_error`: add `| ElabError::Kernel(_)` to the `matches!`. A kernel rejection is not an elaborator `Exception.error` that a term-level catch could retry.

5. Extend `oracle_first_line`:

```rust
    pub fn oracle_first_line(&self) -> Option<String> {
        match self {
            Self::Eliminator { reason } => Some(reason.oracle_first_line()),
            Self::UnknownConstant(n) => Some(format!("Unknown constant `{n}`")),
            // oracle: `throwError m!"Unknown identifier `{n}`"` (probed:
            // `def uib : Nat := nope`). leanr's `sort.rs` also raises
            // `UnknownIdent` for an unknown universe name, which the oracle
            // words differently; no corpus record reaches that.
            Self::UnknownIdent(s) => Some(format!("Unknown identifier `{s}`")),
            Self::TypeMismatch { app: None, .. } => Some("Type mismatch".into()),
            Self::TypeMismatch { app: Some(a), .. } => Some(
                if a.arg_already_in_f {
                    "Application type mismatch: The last"
                } else {
                    "Application type mismatch: The argument"
                }
                .into(),
            ),
            Self::AlreadyDeclared(n) => Some(format!("`{n}` has already been declared")),
            Self::UniverseAlreadyDeclared(u) => {
                Some(format!("a universe level named `{u}` has already been declared"))
            }
            Self::UnusedUniverseParam(u) => Some(format!("unused universe parameter '{u}'")),
            Self::TheoremTypeNotProp(n) => {
                Some(format!("type of theorem `{n}` is not a proposition"))
            }
            Self::UnassignedMVars(line) | Self::UnassignedLevelMVars(line) => Some(line.clone()),
            _ => None,
        }
    }
```

Update the doc comment of `oracle_first_line` to say it answers for every variant the corpus gates compare.

6. In `lib.rs`, add `AppArgMismatch` to the `pub use error::{…}` list.

- [ ] **Step 4: Construct the new field.**

In `coe.rs:76`, change `Err(ElabError::TypeMismatch { expected, got })` to `Err(ElabError::TypeMismatch { expected, got, app: None })`.

In `app/args.rs` `elab_and_add_new_arg`, replace `let val = app.elab.ensure_has_type(&stx, Some(expected), val)?;` with:

```rust
    // oracle: `ensureArgType f arg expectedType` passes `f` as
    // `throwTypeMismatchError`'s `f?` (`App.lean:54-62`,
    // `TermElabM.lean:1151-1153`), so an argument mismatch is reported by
    // `throwAppTypeMismatch f a` (`Meta/Check.lean:250-270`).
    let f = app.st.f;
    let val = match app.elab.ensure_has_type(&stx, Some(expected), val) {
        Err(ElabError::TypeMismatch {
            expected,
            got,
            app: None,
        }) => {
            let arg_already_in_f = app_spine_args(app, f).contains(&val);
            return Err(ElabError::TypeMismatch {
                expected,
                got,
                app: Some(crate::error::AppArgMismatch {
                    f,
                    arg_already_in_f,
                }),
            });
        }
        r => r?,
    };
```

and add, next to `add_new_arg`:

```rust
/// `Expr.getAppArgs` of `e`: the arguments of its application spine, in
/// order. Compared by `ExprId`, which is the oracle's structural `==`
/// under hash-consing (`Meta/Check.lean:254`).
fn app_spine_args(app: &AppElab, e: ExprId) -> Vec<ExprId> {
    let mut args = Vec::new();
    let mut cur = e;
    while let Node::App { f, arg } = app.node(cur) {
        args.push(arg);
        cur = f;
    }
    args.reverse();
    args
}
```

`app.node(e)` is the accessor `add_new_arg` already uses. If the borrow checker objects to `app_spine_args(app, f)` while `app.elab` is borrowed, compute it after the `match` arm binds, as written: the `ensure_has_type` borrow has ended by then.

- [ ] **Step 5: Run the tests to confirm they pass.**

Run: `cargo test -p leanr_elab --test decl_diagnostics_smoke && cargo test -p leanr_elab --lib error::tests && cargo test -p leanr_elab`
Expected: all PASS. The whole crate's suite matters here: `TypeMismatch { .. }` patterns in `anon_ctor_smoke.rs`, `binder_smoke.rs` and `app_smoke.rs` still match because they use `..`.

- [ ] **Step 6: Run the mutations.** Each must FAIL the named test; then revert.
  1. Always set `arg_already_in_f: false` → `argument_already_in_f_says_the_last` FAILS.
  2. Leave `app: None` in `args.rs` (skip the remap) → `argument_mismatch_is_application_type_mismatch` FAILS.
  3. Swap the two `TypeMismatch` arms' strings → `ascription_mismatch_is_type_mismatch` FAILS.
  4. Compare `val` against `f_args` instead of the spine. This is EQUIVALENT for this corpus whenever the head is a constant. Record it as equivalent with that reason, and keep the spine walk because it is the oracle's `getAppArgs`.

- [ ] **Step 7: Commit.**

```bash
git add crates/leanr_elab/src/error.rs crates/leanr_elab/src/coe.rs crates/leanr_elab/src/app/args.rs \
  crates/leanr_elab/src/lib.rs crates/leanr_elab/tests/decl_diagnostics_smoke.rs
git commit -m "leanr_elab: declaration error variants + Type/Application type mismatch first lines"
```

### Task 3: A binder group's type is elaborated once per name

**Files:**
- Modify: `crates/leanr_elab/src/builtin/binder/mod.rs` (`push_binder_group`, and its doc comment; make it `pub(crate)`)
- Test: `crates/leanr_elab/tests/decl_diagnostics_smoke.rs`

**Interfaces:**
- Produces: `pub(crate) fn push_binder_group(elab: &mut TermElabM, g: &BinderGroup, kinds: &KindInterner) -> Result<Vec<ExprId>, ElabError>`. The signature is unchanged; only the visibility and behavior change. `extract_binder_group` and `elab_type` are already `pub(crate)`. Task 6 calls all three for declaration headers.

The oracle: `toBinderViews` makes one `BinderView` per identifier, all sharing the group's type syntax (`Binders.lean`, `toBinderViews`). `elabBinderViews` (`:208-223`) then runs `elabType binderView.type` once PER VIEW, inside the previous views' `withLocalDecl`. So `(α β : Sort _)` gets two independent level mvars, and the second copy of the type elaborates with `α` in scope. Plan-time probe: `def tw (α β : Sort _) (a : α) (b : β) : α := a` has level params `[u_1, u_2]` (corpus record `type/groupHoles`). leanr elaborated the type once, so `β : Sort u_1`. That is a wrong type, and it affects `forall`, `depArrow` and `let`/`have` binders. `fun` binders (`fun.rs`) are already elaborated per view.

- [ ] **Step 1: Write the failing test.** Append to `decl_diagnostics_smoke.rs`:

```rust
/// `∀ (α β : Sort _), α → β → α`: the two binder domains are `Sort ?u`
/// and `Sort ?v` with DISTINCT level mvars (oracle `elabBinderViews`
/// elaborates the group's type once per name, `Binders.lean:208-223`;
/// probe: `def tw (α β : Sort _) …` gets `[u_1, u_2]`).
#[test]
fn binder_group_type_is_elaborated_per_name() {
    use leanr_kernel::bank::terms::Node;
    let r = support::replay_fixture_in("elab", "Elab0.olean");
    support::with_record_elab(
        &r,
        "∀ (α β : Sort _), α → β → α",
        &builtin::snapshot(),
        |elab, elem, kinds| {
            let e = elab.elab_term_and_synthesize(elem, kinds, None).expect("elaborates");
            let base = Some(elab.view.store);
            let st = elab.mctx.store();
            let Node::Forall { binder_type: t1, body, .. } = st.expr_node(base, e) else {
                panic!("outer forall")
            };
            let Node::Forall { binder_type: t2, .. } = st.expr_node(base, body) else {
                panic!("inner forall")
            };
            assert_ne!(t1, t2, "one shared `Sort ?u` for both binders: the group was elaborated once");
        },
    );
}
```

- [ ] **Step 2: Run it to confirm it fails.**

Run: `cargo test -p leanr_elab --test decl_diagnostics_smoke binder_group_type_is_elaborated_per_name`
Expected: FAIL with "one shared `Sort ?u` for both binders".

- [ ] **Step 3: Implement.** Replace `push_binder_group` in `builtin/binder/mod.rs` with:

```rust
/// Push one bracketed binder group's names into the local context,
/// returning their fvars in declaration order. oracle: `elabBinderViews`
/// (`Binders.lean:208-223`) over the group's views. `toBinderViews` makes
/// one view PER NAME sharing the type syntax, and each view runs
/// `elabType` again inside the previous views' scope. So `(x y : T)`
/// elaborates `T` twice: `(α β : Sort _)` gets two independent level
/// mvars, and the second `T` sees `x`. Shared by `elab_binders_and_forall`
/// (the `forall`/`depArrow` telescope), `push_let_binders` (the
/// `let`/`have` telescope) and the declaration header
/// (`command/header.rs`).
pub(crate) fn push_binder_group(
    elab: &mut TermElabM,
    g: &BinderGroup,
    kinds: &KindInterner,
) -> Result<Vec<ExprId>, ElabError> {
    let mut fvars = Vec::with_capacity(g.names.len());
    for &name in &g.names {
        let dom = elab_type(elab, &g.ty, kinds)?;
        // oracle: `elabBinderViews` (`Binders.lean:216-219`) — after
        // `elabType`, before the binder is pushed. `fun`
        // (`elabFunBinderViews`) runs no such check.
        if matches!(g.bi, BinderInfo::InstImplicit) {
            check_inst_binder_type(elab, dom)?;
        }
        fvars.push(push_user_binder(elab, name, dom, g.bi)?);
    }
    Ok(fvars)
}
```

Re-read the oracle lines before writing them into the comment: `toBinderViews` and `elabBinderViews` sit near `Binders.lean:150-223` in v4.33.0-rc1.

- [ ] **Step 4: Run the tests to confirm they pass, then run the existing corpora.**

Run: `cargo test -p leanr_elab`
Expected: all PASS, including `oracle_elab_gate` and `oracle_op` unchanged. If an existing elab record with a grouped binder now diverges, stop: that record's committed oracle answer must already have had two mvars, so the old code was failing it. Report it rather than editing the record.

- [ ] **Step 5: Run the mutation.** Hoist `elab_type` back out of the loop (one call per group) → `binder_group_type_is_elaborated_per_name` FAILS. Revert.

- [ ] **Step 6: Commit.**

```bash
git add crates/leanr_elab/src/builtin/binder/mod.rs crates/leanr_elab/tests/decl_diagnostics_smoke.rs
git commit -m "leanr_elab: elaborate a binder group's type once per name (elabBinderViews)"
```

### Task 4: Unassigned-mvar diagnostics (error infos, arg names, reporting)

**Files:**
- Modify: `crates/leanr_elab/src/synthetic/state.rs` (`MVarErrorKind::Custom`, `LevelMVarErrorInfo`, the register methods, `SavedTermState`)
- Modify: `crates/leanr_elab/src/synthetic/mod.rs` (re-export `LevelMVarErrorInfo`)
- Modify: `crates/leanr_elab/src/elab.rs` (two new `TermElabM` fields)
- Modify: `crates/leanr_elab/src/builtin/binder/mod.rs` (`register_failed_to_infer_binder_type_info`, called from `push_binder_group`)
- Modify: `crates/leanr_elab/src/builtin/binder/fun.rs` (call it per fun binder view)
- Modify: `crates/leanr_elab/src/app/args.rs` (`add_new_arg` registers the arg name)
- Modify: `crates/leanr_elab/src/app/elim.rs:199-210` (`saveArgInfo`)
- Create: `crates/leanr_elab/src/unassigned.rs`; register it in `lib.rs` as `mod unassigned;`
- Test: `crates/leanr_elab/tests/decl_diagnostics_smoke.rs`

**Interfaces:**
- Consumes: `ElabError::UnassignedMVars` / `UnassignedLevelMVars` (Task 2), and the per-name `push_binder_group` (Task 3).
- Produces (all on `TermElabM`, `pub` so the integration tests can call them):
  - `pub fn get_mvars(&mut self, e: ExprId) -> Result<Vec<MVarId>, ElabError>`
  - `pub fn get_level_mvars(&mut self, e: ExprId) -> Result<Vec<LMVarId>, ElabError>`
  - `pub fn log_unassigned_using_error_infos(&mut self, pending: &[MVarId]) -> Result<Option<ElabError>, ElabError>`. `Some(ElabError::UnassignedMVars(first_line))` is the first error the oracle would log, and `None` means it logs nothing.
  - `pub fn log_unassigned_level_mvars_using_error_infos(&mut self, pending: &[LMVarId]) -> Result<Option<ElabError>, ElabError>`
  - `pub fn register_custom_error_if_mvar(&mut self, e: ExprId, stx: SynElem, msg: String)`
  - `pub fn register_mvar_arg_name(&mut self, mvar_id: MVarId, name: NameId)`
  - `pub fn register_level_mvar_error_expr_info(&mut self, expr: ExprId, msg: Option<String>)`
  - `pub(crate) fn name_has_macro_scopes(&self, n: NameId) -> bool`
  - `pub(crate) fn register_failed_to_infer_binder_type_info(elab: &mut TermElabM, ty: ExprId, name: Option<NameId>, stx: SynElem)` in `builtin/binder/mod.rs`

The oracle code being ported (`Elab/Term/TermElabM.lean` unless noted):
- **State.**
  - `mvarErrorInfos : List MVarErrorInfo` is consed (`:185`, `:871`), so the head is the MOST RECENT. leanr's `Vec` is pushed, so it iterates `.iter().rev()`.
  - `levelMVarErrorInfos` (`:187`, `:961`) is consed the same way.
  - `mvarArgNames : MVarIdMap Name` (`:199`, `:888`).
  - All three are `Term.State`, so `Term.SavedState` saves and restores them (`:206-209`). Add them to `SavedTermState`.
- **`MVarErrorKind.custom msgData`** (`:121`), registered by `registerCustomErrorIfMVar` (`:882-885`) when `e.getAppFn` is an mvar.
- **`registerMVarArgName`.** Called from `addNewArg` (`App.lean:420-428`, if `arg.isMVar`, with the forall's binder name) and from `ElabElim.saveArgInfo` (`App.lean:1274-1277`).
- **`registerFailedToInferBinderTypeInfo`** (`Binders.lean:177-183`):
  - message `"type of binder `{id}`"`, or `"binder type"` when the id has macro scopes;
  - `registerCustomErrorIfMVar type ref m!"Failed to infer {msg}"`;
  - `registerLevelMVarErrorExprInfo type ref m!"Failed to infer universe levels in {msg}"`;
  - called from `elabBinderViews` (`:215`) and `elabFunBinderViews` (`:429`), right after `elabType`.
- **`MVarErrorInfo.logError`** (`:901-925`) — first lines:
  - `.implicitArg`: "don't know how to synthesize implicit argument" + `` " `α`" `` if an arg name is registered and has no macro scopes;
  - `.hole`: "don't know how to synthesize placeholder" + `` " for argument `x`" ``;
  - `.custom m`: `m`.
- **`logUnassignedUsingErrorInfos`** (`:934-958`): for each info, newest first, skipping mvars already visited, the info counts if `getMVars (mkMVar mvarId)` meets `pending`. leanr returns at its first error, so `hasOtherErrors` is always false there, and the first counted info IS the first logged error.
- **`LevelMVarErrorInfo.logError`** (`:983-988`): `msgData?.getD "don't know how to synthesize universe level metavariables"`. **`logUnassignedLevelMVarsUsingErrorInfos`** (`:997-1013`): newest first, counted if `collectLevelMVars (instantiateMVars info.expr)` meets `pending`.
- **`getMVars`** (`Meta/CollectMVars.lean:25-39`): instantiate, collect the mvars in order of first occurrence, and for each newly collected mvar that is delayed-assigned, recurse into `mvarIdPending`.
- **`Name.hasMacroScopes`** (`Init/Prelude.lean`): `.str _ s => s == "_hyg"`, `.num p _ => p.hasMacroScopes`. leanr's own fresh names (`_leanr_elab_…`, `elab.rs`'s `mk_fresh_*`) stand in for the oracle's macro-scoped names, so they count too.

- [ ] **Step 1: Write the failing tests.** Append to `decl_diagnostics_smoke.rs`:

```rust
/// Elaborate `src` (no synthesis failure expected), then report the first
/// unassigned-mvar error the oracle's `logUnassignedUsingErrorInfos` would
/// log for the mvars left in the result; and the level-mvar one.
fn unassigned_first_lines(src: &str) -> (Option<String>, Option<String>) {
    let r = support::replay_fixture_in("elab", "Elab0.olean");
    support::with_record_elab(&r, src, &builtin::snapshot(), |elab, elem, kinds| {
        let e = elab.elab_term(elem, kinds, None).expect("elaborates");
        elab.synthesize_synthetic_mvars_no_postponing(kinds).expect("synthesizes");
        let e = elab.mctx.instantiate_mvars(e).expect("instantiates");
        let pending = elab.get_mvars(e).expect("get_mvars");
        let expr_line = elab
            .log_unassigned_using_error_infos(&pending)
            .expect("log")
            .and_then(|err| err.oracle_first_line());
        let lpending = elab.get_level_mvars(e).expect("get_level_mvars");
        let level_line = elab
            .log_unassigned_level_mvars_using_error_infos(&lpending)
            .expect("log levels")
            .and_then(|err| err.oracle_first_line());
        (expr_line, level_line)
    })
}

#[test]
fn hole_argument_names_its_parameter() {
    // oracle: `def eh2 : Nat := pick _ Nat.zero`
    assert_eq!(
        unassigned_first_lines("pick _ Nat.zero").0.as_deref(),
        Some("don't know how to synthesize placeholder for argument `x`")
    );
}

#[test]
fn most_recent_error_info_is_reported_first() {
    // `mvarErrorInfos` is consed: the hole for `y` (registered last) is logged first.
    assert_eq!(
        unassigned_first_lines("pick _ _").0.as_deref(),
        Some("don't know how to synthesize placeholder for argument `y`")
    );
}

#[test]
fn bare_hole_has_no_argument_name() {
    // oracle: `def eh3 := _`
    assert_eq!(
        unassigned_first_lines("_").0.as_deref(),
        Some("don't know how to synthesize placeholder")
    );
}

#[test]
fn implicit_argument_names_its_parameter() {
    // oracle: `def eu := id`
    assert_eq!(
        unassigned_first_lines("id").0.as_deref(),
        Some("don't know how to synthesize implicit argument `α`")
    );
}

#[test]
fn untyped_fun_binder_is_failed_to_infer() {
    // oracle: `def eh4 := fun x => x`
    assert_eq!(
        unassigned_first_lines("fun x => x").0.as_deref(),
        Some("Failed to infer type of binder `x`")
    );
}

#[test]
fn forall_binder_hole_is_failed_to_infer() {
    // oracle (decl header analogue): `def eh (x : _) : Nat := Nat.zero`
    assert_eq!(
        unassigned_first_lines("∀ (x : _), Nat").0.as_deref(),
        Some("Failed to infer type of binder `x`")
    );
}

#[test]
fn level_mvar_in_hole_binder_names_the_binder_type() {
    // oracle: `def lv : Nat := (fun (_ : Sort _) => Nat.zero) PUnit`
    assert_eq!(
        unassigned_first_lines("(fun (_ : Sort _) => Nat.zero) PUnit").1.as_deref(),
        Some("Failed to infer universe levels in binder type")
    );
}
```

- [ ] **Step 2: Run them to confirm they fail.**

Run: `cargo test -p leanr_elab --test decl_diagnostics_smoke`
Expected: compile error, no method `get_mvars` on `TermElabM`.

- [ ] **Step 3: Extend the state** (`synthetic/state.rs`).

```rust
/// oracle: `inductive MVarErrorKind` (`TermElabM.lean:116-124`).
#[derive(Debug, Clone)]
pub enum MVarErrorKind {
    /// oracle: `.implicitArg (lctx) (ctx)` — the parent application.
    /// leanr stores only the application: the oracle's `lctx` exists for
    /// the named-argument eta feature's error rendering, which is prose.
    ImplicitArg { app: ExprId },
    Hole,
    /// oracle: `.custom msgData` (`:121`). leanr keeps the message's first
    /// line, the only part a gate compares.
    Custom(String),
}

/// oracle: `structure LevelMVarErrorInfo` (`TermElabM.lean:146-151`),
/// minus the `lctx`/`ref` used only for rendering the expression.
#[derive(Debug, Clone)]
pub struct LevelMVarErrorInfo {
    pub expr: ExprId,
    /// `msgData?`, as its first line.
    pub msg: Option<String>,
}
```

Add `mvar_arg_names: HashMap<MVarId, NameId>` and `level_mvar_error_infos: Vec<LevelMVarErrorInfo>` to `SavedTermState`, and clone/restore them in `save_term_state`/`restore_term_state`, exactly as `mvar_error_infos` is. Add the register methods to the `impl<'e> TermElabM<'e>` block next to `register_mvar_error_hole_info`:

```rust
    /// oracle: `registerCustomErrorIfMVar` (`TermElabM.lean:882-885`) —
    /// registers only if `e.getAppFn` is an mvar.
    pub fn register_custom_error_if_mvar(&mut self, e: ExprId, stx: SynElem, msg: String) {
        let base = Some(self.view.store);
        let mut head = e;
        while let Node::App { f, .. } = self.mctx.store().expr_node(base, head) {
            head = f;
        }
        if let Node::MVar { id: Some(n) } = self.mctx.store().expr_node(base, head) {
            self.mvar_error_infos.push(MVarErrorInfo {
                mvar_id: MVarId(n),
                stx,
                kind: MVarErrorKind::Custom(msg),
            });
        }
    }

    /// oracle: `registerMVarArgName` (`TermElabM.lean:887-888`).
    pub fn register_mvar_arg_name(&mut self, mvar_id: MVarId, name: NameId) {
        self.mvar_arg_names.insert(mvar_id, name);
    }

    /// oracle: `registerLevelMVarErrorExprInfo` (`TermElabM.lean:963-964`).
    pub fn register_level_mvar_error_expr_info(&mut self, expr: ExprId, msg: Option<String>) {
        self.level_mvar_error_infos
            .push(LevelMVarErrorInfo { expr, msg });
    }
```

(`Node` is `leanr_kernel::bank::terms::Node`; add the import.) In `synthetic/mod.rs`, add `LevelMVarErrorInfo` to the `pub use state::{…}` list.

In `elab.rs`, add these fields to `TermElabM`, documented like `mvar_error_infos`, and initialize both empty in `new`:

```rust
    /// oracle: `Term.State.mvarArgNames` (`TermElabM.lean:189-199`).
    pub mvar_arg_names: HashMap<MVarId, NameId>,
    /// oracle: `Term.State.levelMVarErrorInfos` (`TermElabM.lean:187`).
    /// Pushed; the oracle conses, so readers iterate in reverse.
    pub level_mvar_error_infos: Vec<crate::synthetic::LevelMVarErrorInfo>,
```

- [ ] **Step 4: Register at the oracle's sites.**

In `builtin/binder/mod.rs` add:

```rust
/// oracle: `registerFailedToInferBinderTypeInfo` (`Binders.lean:177-183`).
pub(crate) fn register_failed_to_infer_binder_type_info(
    elab: &mut TermElabM,
    ty: ExprId,
    name: Option<NameId>,
    stx: SynElem,
) {
    let msg = match name {
        Some(n) if !elab.name_has_macro_scopes(n) => {
            let base = Some(elab.view.store);
            format!(
                "type of binder `{}`",
                elab.mctx.store().to_name(base, Some(n))
            )
        }
        _ => "binder type".to_string(),
    };
    elab.register_custom_error_if_mvar(ty, stx, format!("Failed to infer {msg}"));
    elab.register_level_mvar_error_expr_info(
        ty,
        Some(format!("Failed to infer universe levels in {msg}")),
    );
}
```

In `push_binder_group` (Task 3's loop), right after `let dom = elab_type(elab, &g.ty, kinds)?;`, add `register_failed_to_infer_binder_type_info(elab, dom, name, g.ty.clone());`.

In `fun.rs`, in the `for view in views` loop, right after `let dom = match &view.ty { … };`, add:

```rust
                // oracle: `elabFunBinderViews` (`Binders.lean:428-429`) —
                // `registerFailedToInferBinderTypeInfo` right after
                // `elabType` (an elided type is `elabType` of a hole).
                super::register_failed_to_infer_binder_type_info(
                    elab,
                    dom,
                    view.name,
                    view.ty.clone().unwrap_or_else(|| item.clone()),
                );
```

`item` is the binder syntax element the loop is iterating. Check its name in the surrounding code and adapt; any `SynElem` for the binder is fine, because the ref is not part of the first line.

In `app/args.rs` `add_new_arg`, bind `binder_name` from the `Node::Forall` it already destructures, and before returning `Ok(())` add:

```rust
    // oracle: `addNewArg` (`App.lean:420-428`): `if arg.isMVar then
    // registerMVarArgName arg.mvarId! argName`, `argName` being the
    // forall's binder name. An anonymous binder name is not registered:
    // the oracle would render `[anonymous]`, and no fixture constant has
    // one.
    if let (Node::MVar { id: Some(m) }, Some(bn)) = (app.node(arg), binder_name) {
        app.elab.register_mvar_arg_name(leanr_meta::MVarId(m), bn);
    }
```

In `app/elim.rs`, replace the comment at `:199-201` ("`saveArgInfo`'s `registerMVarArgName` is … not ported") with the port:

```rust
            // oracle: `addArgAndContinue` → `saveArgInfo arg binderName`
            // (`App.lean:1274-1277`, `:1286`).
            if let (Node::MVar { id: Some(m) }, Some(bn)) = (lval::node(self.elab, arg), binder_name) {
                self.elab.register_mvar_arg_name(leanr_meta::MVarId(m), bn);
            }
```

Also delete the stale "not ported (`args.rs`'s `mk_inst_mvar` precedent)" wording wherever it refers to `registerMVarArgName`: `grep -rn registerMVarArgName crates/leanr_elab/src`.

- [ ] **Step 5: Write `unassigned.rs`.**

```rust
//! Reporting unassigned metavariables: oracle `logUnassignedUsingErrorInfos`
//! / `logUnassignedLevelMVarsUsingErrorInfos` (`Elab/Term/TermElabM.lean:
//! 901-1013`) and `getMVars` (`Meta/CollectMVars.lean:25-39`). leanr returns
//! the FIRST error the oracle would log instead of logging. It stops at its
//! first error, so the oracle's `hasOtherErrors` is always false here.

use std::collections::HashSet;

use leanr_kernel::bank::levels::LevelRow;
use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, LevelId, NameId};
use leanr_meta::{LMVarId, MVarId};

use crate::elab::TermElabM;
use crate::error::ElabError;
use crate::synthetic::MVarErrorKind;

impl TermElabM<'_> {
    /// oracle: `getMVars` (`Meta/CollectMVars.lean:25-39`): the unassigned
    /// mvars of `instantiateMVars e` in order of first occurrence, and for
    /// each delayed-assigned one, those of its pending mvar too.
    pub fn get_mvars(&mut self, e: ExprId) -> Result<Vec<MVarId>, ElabError> {
        let mut out = Vec::new();
        self.collect_mvars(e, &mut out)?;
        Ok(out)
    }

    fn collect_mvars(&mut self, e: ExprId, out: &mut Vec<MVarId>) -> Result<(), ElabError> {
        let e = self.mctx.instantiate_mvars(e)?;
        let start = out.len();
        let base = Some(self.view.store);
        // `Expr.collectMVars`: pre-order, function before argument.
        let mut seen: HashSet<ExprId> = HashSet::new();
        let mut stack = vec![e];
        while let Some(t) = stack.pop() {
            if !self.mctx.store().expr_data(base, t).has_expr_mvar() || !seen.insert(t) {
                continue;
            }
            match self.mctx.store().expr_node(base, t) {
                Node::MVar { id: Some(n) } => {
                    if !out.contains(&MVarId(n)) {
                        out.push(MVarId(n));
                    }
                }
                Node::App { f, arg } => {
                    stack.push(arg);
                    stack.push(f);
                }
                Node::Lam { binder_type, body, .. } | Node::Forall { binder_type, body, .. } => {
                    stack.push(body);
                    stack.push(binder_type);
                }
                Node::LetE { ty, value, body, .. } => {
                    stack.push(body);
                    stack.push(value);
                    stack.push(ty);
                }
                Node::MData { expr, .. } => stack.push(expr),
                Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                    stack.push(structure)
                }
                _ => {}
            }
        }
        let added: Vec<MVarId> = out[start..].to_vec();
        for m in added {
            let pending = self.mctx.mctx().delayed_assignment(m).map(|d| d.mvar_id_pending);
            if let Some(p) = pending {
                let pe = self
                    .mctx
                    .store_mut()
                    .expr_mvar(base, Some(p.0))
                    .map_err(leanr_meta::MetaError::from)?;
                self.collect_mvars(pe, out)?;
            }
        }
        Ok(())
    }

    /// oracle: `collectLevelMVars {} (← instantiateMVars e)`.
    pub fn get_level_mvars(&mut self, e: ExprId) -> Result<Vec<LMVarId>, ElabError> {
        let e = self.mctx.instantiate_mvars(e)?;
        let base = Some(self.view.store);
        let mut out = Vec::new();
        let mut seen: HashSet<ExprId> = HashSet::new();
        let mut stack = vec![e];
        while let Some(t) = stack.pop() {
            if !self.mctx.store().expr_data(base, t).has_level_mvar() || !seen.insert(t) {
                continue;
            }
            match self.mctx.store().expr_node(base, t) {
                Node::Sort { level } => self.collect_level_mvars_of(level, &mut out),
                Node::Const { levels, .. } => {
                    let ls = self.mctx.store().level_list_at(base, levels).to_vec();
                    for l in ls {
                        self.collect_level_mvars_of(l, &mut out);
                    }
                }
                Node::App { f, arg } => {
                    stack.push(arg);
                    stack.push(f);
                }
                Node::Lam { binder_type, body, .. } | Node::Forall { binder_type, body, .. } => {
                    stack.push(body);
                    stack.push(binder_type);
                }
                Node::LetE { ty, value, body, .. } => {
                    stack.push(body);
                    stack.push(value);
                    stack.push(ty);
                }
                Node::MData { expr, .. } => stack.push(expr),
                Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                    stack.push(structure)
                }
                _ => {}
            }
        }
        Ok(out)
    }

    fn collect_level_mvars_of(&self, l: LevelId, out: &mut Vec<LMVarId>) {
        let base = Some(self.view.store);
        let mut stack = vec![l];
        while let Some(l) = stack.pop() {
            match *self.mctx.store().level_row(base, l) {
                LevelRow::Succ(a) => stack.push(a),
                LevelRow::Max(a, b) | LevelRow::IMax(a, b) => {
                    stack.push(b);
                    stack.push(a);
                }
                LevelRow::MVar(Some(n)) => {
                    if !out.contains(&LMVarId(n)) {
                        out.push(LMVarId(n));
                    }
                }
                _ => {}
            }
        }
    }

    /// oracle: `Name.hasMacroScopes` (`Init/Prelude.lean`): the last string
    /// component is `_hyg`, looking through numeric components. leanr's own
    /// fresh names (`_leanr_elab_*`) stand in for the oracle's macro-scoped
    /// ones, so they count as well.
    pub(crate) fn name_has_macro_scopes(&self, n: NameId) -> bool {
        let base = Some(self.view.store);
        let s = self.mctx.store().to_name(base, Some(n)).to_string();
        if s.starts_with("_leanr_elab_") {
            return true;
        }
        s.split('.')
            .rev()
            .find(|c| c.parse::<u64>().is_err())
            .is_some_and(|c| c == "_hyg")
    }

    /// `addArgName` (`TermElabM.lean:917-920`): `` " `{argName}`" `` (after
    /// `extra`) if a name is registered and has no macro scopes.
    fn arg_name_suffix(&self, m: MVarId, extra: &str) -> String {
        match self.mvar_arg_names.get(&m) {
            Some(&n) if !self.name_has_macro_scopes(n) => {
                let base = Some(self.view.store);
                format!("{extra} `{}`", self.mctx.store().to_name(base, Some(n)))
            }
            _ => String::new(),
        }
    }

    /// oracle: `logUnassignedUsingErrorInfos` (`TermElabM.lean:934-958`) +
    /// `MVarErrorInfo.logError`'s first line (`:901-912`).
    pub fn log_unassigned_using_error_infos(
        &mut self,
        pending: &[MVarId],
    ) -> Result<Option<ElabError>, ElabError> {
        if pending.is_empty() {
            return Ok(None);
        }
        let mut visited: HashSet<MVarId> = HashSet::new();
        // newest first: the oracle's list is consed (`:871`)
        let infos: Vec<_> = self.mvar_error_infos.iter().rev().cloned().collect();
        for info in infos {
            if !visited.insert(info.mvar_id) {
                continue;
            }
            let e = self
                .mctx
                .store_mut()
                .expr_mvar(Some(self.view.store), Some(info.mvar_id.0))
                .map_err(leanr_meta::MetaError::from)?;
            let deps = self.get_mvars(e)?;
            if !deps.iter().any(|d| pending.contains(d)) {
                continue;
            }
            let line = match &info.kind {
                MVarErrorKind::ImplicitArg { .. } => format!(
                    "don't know how to synthesize implicit argument{}",
                    self.arg_name_suffix(info.mvar_id, "")
                ),
                MVarErrorKind::Hole => format!(
                    "don't know how to synthesize placeholder{}",
                    self.arg_name_suffix(info.mvar_id, " for argument")
                ),
                MVarErrorKind::Custom(m) => m.lines().next().unwrap_or("").to_string(),
            };
            return Ok(Some(ElabError::UnassignedMVars(line)));
        }
        Ok(None)
    }

    /// oracle: `logUnassignedLevelMVarsUsingErrorInfos` (`TermElabM.lean:
    /// 997-1013`) + `LevelMVarErrorInfo.logError`'s first line (`:983-988`).
    pub fn log_unassigned_level_mvars_using_error_infos(
        &mut self,
        pending: &[LMVarId],
    ) -> Result<Option<ElabError>, ElabError> {
        if pending.is_empty() {
            return Ok(None);
        }
        let infos: Vec<_> = self.level_mvar_error_infos.iter().rev().cloned().collect();
        for info in infos {
            let lmvars = self.get_level_mvars(info.expr)?;
            if lmvars.iter().any(|l| pending.contains(l)) {
                let line = info
                    .msg
                    .unwrap_or_else(|| "don't know how to synthesize universe level metavariables".into());
                return Ok(Some(ElabError::UnassignedLevelMVars(line)));
            }
        }
        Ok(None)
    }
}
```

Fix up the API names against the code as you go:
- `Store::expr_mvar(base, Option<NameId>)` is how an mvar node is interned. Find the constructor used in `elab.rs`'s `mk_fresh_expr_mvar` and use that.
- `MetaCtx::mctx()` returns `&MetavarContext`, which has `delayed_assignment(MVarId)`.
- `Store::level_list_at(base, LevelsId) -> &[LevelId]`.
- `MVarErrorInfo` derives `Clone` already.
- Whether `instantiate_mvars` also instantiates assigned LEVEL mvars: if it does not, `get_level_mvars` must call the level instantiator first. Check `assign.rs:1280` and write a unit assertion if unsure.

- [ ] **Step 6: Run the tests to confirm they pass.**

Run: `cargo test -p leanr_elab --test decl_diagnostics_smoke && cargo test -p leanr_elab`
Expected: all PASS (existing corpora unchanged: registrations do not change any term).

- [ ] **Step 7: Run the mutations.** Each must FAIL the named test; then revert.
  1. Iterate `mvar_error_infos` oldest-first (drop `.rev()`) → `most_recent_error_info_is_reported_first` FAILS.
  2. Skip the `register_mvar_arg_name` call in `add_new_arg` → `hole_argument_names_its_parameter` and `implicit_argument_names_its_parameter` FAIL.
  3. Drop the `fun.rs` registration → `untyped_fun_binder_is_failed_to_infer` FAILS.
  4. Drop the `push_binder_group` registration → `forall_binder_hole_is_failed_to_infer` FAILS.
  5. Register the level info with `msg: None` → `level_mvar_in_hole_binder_names_the_binder_type` FAILS.
  6. `name_has_macro_scopes` always `true` → `untyped_fun_binder_is_failed_to_infer` FAILS (it says "binder type").
  7. Drop the `visited` skip. This is EQUIVALENT under leanr's first-error contract: a second info for an already-visited mvar can only follow the first match, and leanr returns at the first. Record it as equivalent.

- [ ] **Step 8: Commit.**

```bash
git add crates/leanr_elab/src/synthetic/state.rs crates/leanr_elab/src/synthetic/mod.rs crates/leanr_elab/src/elab.rs \
  crates/leanr_elab/src/builtin/binder/mod.rs crates/leanr_elab/src/builtin/binder/fun.rs \
  crates/leanr_elab/src/app/args.rs crates/leanr_elab/src/app/elim.rs crates/leanr_elab/src/unassigned.rs \
  crates/leanr_elab/src/lib.rs crates/leanr_elab/tests/decl_diagnostics_smoke.rs
git commit -m "leanr_elab: unassigned-mvar diagnostics (custom/level error infos, mvarArgNames, logUnassigned*)"
```

### Task 5: `DefView` — decode a declaration command, raise named seams

**Files:**
- Create: `crates/leanr_elab/src/command/mod.rs` (module doc plus `pub(crate) mod view;`, and nothing else yet)
- Create: `crates/leanr_elab/src/command/view.rs`
- Modify: `crates/leanr_elab/src/lib.rs` (`pub mod command; // M4c-1 P2`)

**Interfaces:**
- Produces:

```rust
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DefKind { Def, Theorem, Abbrev, Opaque, Example, Axiom }

pub(crate) struct DefView {
    pub kind: DefKind,
    /// The declaration's short name as written. `None` for `example`,
    /// whose name is `_example` (`DefView.lean:201-208`).
    pub name: Option<String>,
    /// The `declId` node (for messages); `None` for `example`.
    pub decl_id: Option<SynElem>,
    /// `.{u, v}` names in source order.
    pub univ_names: Vec<String>,
    /// The bracketed binder groups, in order.
    pub binders: Vec<SyntaxNode>,
    /// The `: T` term, if written (always `Some` for theorem/opaque/axiom).
    pub ty: Option<SynElem>,
    /// The `:= v` term (`None` only for `axiom`).
    pub value: Option<SynElem>,
}

impl DefView {
    pub(crate) fn from_syntax(cmd: &SyntaxNode, kinds: &KindInterner) -> Result<DefView, ElabError>;
}
```

The syntax shapes, confirmed with `leanr parse --dump` at plan time. Children are listed without trivia.
- **`Lean.Parser.Command.declaration`**: `[declModifiers, <kind node>]`.
- **`declModifiers`** has 7 children, each an empty `null` node when absent, in this order: docComment, attributes, visibility (`private`/`public`), `protected`, `meta`/`noncomputable`, `unsafe`, `partial`/`nonrec` (`Command.lean:114-121`).
- **Kind nodes:**
  - `definition`: `["def", declId, optDeclSig, declVal, optDefDeriving]`
  - `theorem`: `["theorem", declId, declSig, declVal]`
  - `abbrev`: `["abbrev", declId, optDeclSig, declVal]`
  - `opaque`: `["opaque", declId, declSig, null[declValSimple?]]`
  - `axiom`: `["axiom", declId, declSig]`
  - `example`: `["example", optDeclSig, declVal]`
- **`declId`**: `[<ident>, null]`, or `[<ident>, null[".{", null[u, ",", v, …], "}"]]`.
- **`declSig`**: `[null[binders…], typeSpec]`. **`optDeclSig`**: `[null[binders…], null[typeSpec?]]`. **`typeSpec`**: `[":", term]`.
- **`declValSimple`**: `[":=", term, Termination.suffix[null, null], null[whereDecls?]]`. Other `declVal` kinds are `declValEqns` and `whereStructInst`.

Seams. Every message is `"<what> — <label>"`, and the tests match on the `<what>` substring:

| Input | Seam message |
|---|---|
| a non-`declaration` command | ``command `<kind>` — M4c-2 (command loop)`` |
| a doc comment | `doc comment — later M4 (docs)` |
| attributes | `attributes — later M4` |
| `private`/`public` | `visibility modifier — later M4` |
| `protected` | `` `protected` — M4c-2 (namespaces) `` |
| `meta`/`noncomputable` | `` `meta`/`noncomputable` — later M4 (compilation) `` |
| `unsafe` | `` `unsafe` — later M4 `` |
| `partial`/`nonrec` | `` `partial`/`nonrec` — later M4 (recursion) `` |
| any other declaration kind (`instance`, `structure`, `inductive`, `classInductive`, …) | ``declaration kind `<kind>` — later M4`` |
| `deriving` | `deriving — later M4` |
| a dotted or `_root_` name | ``dotted declaration name `<n>` — M4c-2 (namespaces)`` |
| a `_` universe | `universe hole in .{…} — later M4` |
| a bare binder identifier (`def f x`) | `bare binder identifier — later M4` |
| `opaque` without a value | `` `opaque` without a value — later M4 (Inhabited/Nonempty default) `` |
| `declValEqns` | `pattern-matching equations — later M4 (match / equation compiler)` |
| `whereStructInst` | `` `where` structure instance — later M4 `` |
| termination hints | `termination hints — later M4 (recursion)` |
| `where` | `` `where` declarations — later M4 `` |
| self-reference | ``recursive reference to `<n>` — later M4 (recursion)`` |

The self-reference rule: an `<ident>` token in the VALUE whose text is the short name, or starts with `"<name>."`. The oracle elaborates the body under `withFunLocalDecls` (`MutualDef.lean:1343`), so such an identifier resolves to the function itself. The scan is conservative: a binder shadowing the name also seams, which is safe because it is never a wrong `Ok`.

- [ ] **Step 1: Write the failing tests.** In `command/view.rs`, put the tests module at the bottom:

```rust
#[cfg(test)]
mod tests {
    use super::*;

    fn view_of(src: &str) -> Result<DefView, ElabError> {
        let parsed = leanr_syntax::parse_module(src, &leanr_syntax::builtin::snapshot());
        assert!(parsed.errors.is_empty(), "{src:?}: {:?}", parsed.errors);
        let root = parsed.tree.root();
        let cmd = root
            .children()
            .find(|n| {
                let k = parsed.tree.kinds.name(n.kind());
                k != "Lean.Parser.Module.header" && k != "Lean.Parser.Command.eoi"
            })
            .expect("one command");
        DefView::from_syntax(&cmd, &parsed.tree.kinds)
    }

    fn seam(src: &str) -> String {
        match view_of(src) {
            Err(ElabError::UnsupportedSyntax(m)) => m,
            Err(e) => panic!("{src:?}: expected a named seam, got {e:?}"),
            Ok(_) => panic!("{src:?}: expected a named seam, got a view"),
        }
    }

    #[test]
    fn decodes_a_def_with_universes_binders_type_and_value() {
        let v = view_of("def ue1.{u, v} (α : Sort u) {a : α} : α := a").unwrap();
        assert_eq!(v.kind, DefKind::Def);
        assert_eq!(v.name.as_deref(), Some("ue1"));
        assert_eq!(v.univ_names, vec!["u".to_string(), "v".to_string()]);
        assert_eq!(v.binders.len(), 2);
        assert!(v.ty.is_some() && v.value.is_some());
    }

    #[test]
    fn decodes_every_kind() {
        assert_eq!(view_of("theorem t : True := True.intro").unwrap().kind, DefKind::Theorem);
        assert_eq!(view_of("abbrev a := Nat.zero").unwrap().kind, DefKind::Abbrev);
        assert_eq!(view_of("opaque o : Nat := Nat.zero").unwrap().kind, DefKind::Opaque);
        let ax = view_of("axiom ax (x : Nat) : Nat").unwrap();
        assert_eq!((ax.kind, ax.binders.len(), ax.value.is_none()), (DefKind::Axiom, 1, true));
        let ex = view_of("example : Nat := Nat.zero").unwrap();
        assert_eq!((ex.kind, ex.name.is_none()), (DefKind::Example, true));
        let inf = view_of("def inf1 := Nat.zero").unwrap();
        assert!(inf.ty.is_none());
    }

    #[test]
    fn modifiers_are_named_seams() {
        assert!(seam("/-- d -/ def a : Nat := Nat.zero").contains("doc comment"));
        assert!(seam("@[simp] def a : Nat := Nat.zero").contains("attributes"));
        assert!(seam("private def a : Nat := Nat.zero").contains("visibility modifier"));
        assert!(seam("protected def a : Nat := Nat.zero").contains("`protected`"));
        assert!(seam("noncomputable def a : Nat := Nat.zero").contains("`meta`/`noncomputable`"));
        assert!(seam("unsafe def a : Nat := Nat.zero").contains("`unsafe`"));
        assert!(seam("partial def a : Nat := Nat.zero").contains("`partial`/`nonrec`"));
    }

    #[test]
    fn dotted_decl_name_is_an_m4c2_seam() {
        let m = seam("def Foo.bar : Nat := Nat.zero");
        assert!(m.contains("dotted declaration name `Foo.bar`") && m.contains("M4c-2"), "{m}");
        assert!(seam("def _root_.baz : Nat := Nat.zero").contains("dotted declaration name"));
    }

    #[test]
    fn self_reference_is_a_recursion_seam() {
        assert!(seam("def sr : Nat := sr").contains("recursive reference to `sr`"));
        assert!(seam("def sr : Nat := sr.foo").contains("recursive reference to `sr`"));
        // an unrelated identifier that merely starts with the name is not one
        assert!(view_of("def sr : Nat := srx").is_ok());
    }

    #[test]
    fn unsupported_value_forms_are_named_seams() {
        assert!(seam("def f : Nat → Nat\n  | n => n").contains("pattern-matching equations"));
        assert!(seam("def a : Nat := b\nwhere b := Nat.zero").contains("`where` declarations"));
        assert!(seam("def a : Nat := Nat.zero\ntermination_by 1").contains("termination hints"));
        assert!(seam("def a : Nat := Nat.zero deriving Repr").contains("deriving"));
        assert!(seam("opaque o : Nat").contains("`opaque` without a value"));
        assert!(seam("def a b : Nat := Nat.zero").contains("bare binder identifier"));
    }

    #[test]
    fn unsupported_commands_are_named_seams() {
        assert!(seam("instance : Wrap Nat := ⟨fun x => x⟩").contains("declaration kind"));
        assert!(seam("structure S where\n  x : Nat").contains("declaration kind"));
        assert!(seam("namespace Foo").contains("M4c-2 (command loop)"));
        assert!(seam("#check Nat").contains("M4c-2 (command loop)"));
        assert!(seam("mutual\ndef a : Nat := Nat.zero\nend").contains("M4c-2 (command loop)"));
    }
}
```

Each source above must parse cleanly in leanr; `view_of` asserts that. If one does not parse (for example, `termination_by` without recursion), replace it with a spelling that leanr parses and that reaches the same seam. Check it with `./target/debug/leanr parse <file>` first. Do not delete the seam assertion.

- [ ] **Step 2: Run them to confirm they fail.**

Run: `cargo test -p leanr_elab --lib command::view`
Expected: compile error (module/`DefView` missing).

- [ ] **Step 3: Implement `view.rs`.**

```rust
//! `DefView`: the M4c-1 subset of oracle `mkDefView` (`Elab/DefView.lean:
//! 140-230`) plus `elabAxiom`'s syntax access (`Elab/Declaration.lean:
//! 101-105`). Decodes one `declaration` command and raises a named seam for
//! everything outside M4c-1 (spec § Architecture, `DefView::from_syntax`).

use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::{NodeOrToken, SyntaxNode};

use crate::dispatch::{non_trivia_children, SynElem};
use crate::error::ElabError;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum DefKind {
    Def,
    Theorem,
    Abbrev,
    Opaque,
    Example,
    Axiom,
}

pub(crate) struct DefView {
    pub kind: DefKind,
    pub name: Option<String>,
    pub decl_id: Option<SynElem>,
    pub univ_names: Vec<String>,
    pub binders: Vec<SyntaxNode>,
    pub ty: Option<SynElem>,
    pub value: Option<SynElem>,
}

fn seam(what: impl Into<String>) -> ElabError {
    ElabError::UnsupportedSyntax(what.into())
}

fn ill(what: &str) -> ElabError {
    ElabError::IllFormedSyntax(format!("declaration: {what}"))
}

fn node_kind<'k>(kinds: &'k KindInterner, el: &SynElem) -> &'k str {
    match el {
        NodeOrToken::Node(n) => kinds.name(n.kind()),
        NodeOrToken::Token(t) => kinds.name(t.kind()),
    }
}

fn as_node(el: Option<&SynElem>, what: &str) -> Result<SyntaxNode, ElabError> {
    el.and_then(|e| e.as_node()).cloned().ok_or_else(|| ill(what))
}

fn is_empty(n: &SyntaxNode) -> bool {
    non_trivia_children(n).is_empty()
}

impl DefView {
    pub(crate) fn from_syntax(cmd: &SyntaxNode, kinds: &KindInterner) -> Result<DefView, ElabError> {
        let ck = kinds.name(cmd.kind());
        if ck != "Lean.Parser.Command.declaration" {
            return Err(seam(format!("command `{ck}` — M4c-2 (command loop)")));
        }
        let ch = non_trivia_children(cmd);
        let mods = as_node(ch.first(), "declModifiers")?;
        check_modifiers(&mods)?;
        let decl = as_node(ch.get(1), "declaration kind")?;
        let dk = kinds.name(decl.kind());
        let d = non_trivia_children(&decl);
        // (kind, declId, declSig, optDeclSig, declVal) — owned, so `opaque`
        // can hand over the declValSimple INSIDE its optional slot.
        let (kind, decl_id, sig, opt_sig, val): (
            DefKind,
            Option<SynElem>,
            Option<SynElem>,
            Option<SynElem>,
            Option<SynElem>,
        ) = match dk {
            "Lean.Parser.Command.definition" => {
                if let Some(der) = d.get(4).and_then(|e| e.as_node()) {
                    if !is_empty(der) {
                        return Err(seam("deriving — later M4"));
                    }
                }
                (DefKind::Def, d.get(1).cloned(), None, d.get(2).cloned(), d.get(3).cloned())
            }
            "Lean.Parser.Command.theorem" => {
                (DefKind::Theorem, d.get(1).cloned(), d.get(2).cloned(), None, d.get(3).cloned())
            }
            "Lean.Parser.Command.abbrev" => {
                (DefKind::Abbrev, d.get(1).cloned(), None, d.get(2).cloned(), d.get(3).cloned())
            }
            "Lean.Parser.Command.opaque" => {
                let slot = as_node(d.get(3), "opaque value slot")?;
                let Some(dv) = non_trivia_children(&slot).first().cloned() else {
                    return Err(seam(
                        "`opaque` without a value — later M4 (Inhabited/Nonempty default)",
                    ));
                };
                (DefKind::Opaque, d.get(1).cloned(), d.get(2).cloned(), None, Some(dv))
            }
            "Lean.Parser.Command.axiom" => {
                (DefKind::Axiom, d.get(1).cloned(), d.get(2).cloned(), None, None)
            }
            "Lean.Parser.Command.example" => {
                (DefKind::Example, None, None, d.get(1).cloned(), d.get(2).cloned())
            }
            other => return Err(seam(format!("declaration kind `{other}` — later M4"))),
        };
        let (name, univ_names) = match &decl_id {
            Some(id) => decode_decl_id(&as_node(Some(id), "declId")?, kinds)?,
            None => (None, Vec::new()),
        };
        let (binders, ty) = match (&sig, &opt_sig) {
            (Some(s), _) => decode_sig(&as_node(Some(s), "declSig")?, kinds, false)?,
            (None, Some(s)) => decode_sig(&as_node(Some(s), "optDeclSig")?, kinds, true)?,
            (None, None) => return Err(ill("missing signature")),
        };
        let value = match &val {
            None => None,
            Some(v) => Some(decode_decl_val(&as_node(Some(v), "declVal")?, kinds)?),
        };
        if let (Some(n), Some(v)) = (&name, &value) {
            check_no_self_reference(n, v, kinds)?;
        }
        Ok(DefView {
            kind,
            name,
            decl_id,
            univ_names,
            binders,
            ty,
            value,
        })
    }
}
```

Then the helpers:

```rust
/// declModifiers' 7 slots (`Command.lean:114-121`); M4c-1 accepts none.
fn check_modifiers(mods: &SyntaxNode) -> Result<(), ElabError> {
    const SEAMS: [&str; 7] = [
        "doc comment — later M4 (docs)",
        "attributes — later M4",
        "visibility modifier — later M4",
        "`protected` — M4c-2 (namespaces)",
        "`meta`/`noncomputable` — later M4 (compilation)",
        "`unsafe` — later M4",
        "`partial`/`nonrec` — later M4 (recursion)",
    ];
    for (i, slot) in non_trivia_children(mods).iter().enumerate() {
        let empty = slot.as_node().is_some_and(is_empty);
        if !empty {
            return Err(seam(*SEAMS.get(i).unwrap_or(&"declaration modifier — later M4")));
        }
    }
    Ok(())
}

/// `declId := ident >> optional (".{" >> sepBy1 (ident <|> hole) ", " >> "}")`.
fn decode_decl_id(
    id: &SyntaxNode,
    kinds: &KindInterner,
) -> Result<(Option<String>, Vec<String>), ElabError> {
    let ch = non_trivia_children(id);
    let name = match ch.first() {
        Some(NodeOrToken::Token(t)) if kinds.name(t.kind()) == "<ident>" => t.text().to_string(),
        _ => return Err(ill("declId name")),
    };
    if name.contains('.') || name.starts_with("_root_") {
        return Err(seam(format!("dotted declaration name `{name}` — M4c-2 (namespaces)")));
    }
    let mut univs = Vec::new();
    if let Some(NodeOrToken::Node(opt)) = ch.get(1) {
        for el in non_trivia_children(opt) {
            if let NodeOrToken::Node(list) = el {
                for u in non_trivia_children(&list) {
                    match &u {
                        NodeOrToken::Token(t) if kinds.name(t.kind()) == "<ident>" => {
                            univs.push(t.text().to_string())
                        }
                        NodeOrToken::Token(t) if t.text() == "," => {}
                        _ => return Err(seam("universe hole in .{…} — later M4")),
                    }
                }
            }
        }
    }
    Ok((Some(name), univs))
}

/// `declSig := many binder >> typeSpec`; `optDeclSig := many binder >> optType`.
fn decode_sig(
    sig: &SyntaxNode,
    kinds: &KindInterner,
    optional_type: bool,
) -> Result<(Vec<SyntaxNode>, Option<SynElem>), ElabError> {
    let ch = non_trivia_children(sig);
    let bs = as_node(ch.first(), "binders")?;
    let mut binders = Vec::new();
    for b in non_trivia_children(&bs) {
        match b {
            NodeOrToken::Node(n) if kinds.name(n.kind()) != "Lean.Parser.Term.hole" => binders.push(n),
            _ => return Err(seam("bare binder identifier — later M4")),
        }
    }
    let ty_spec = if optional_type {
        let opt = as_node(ch.get(1), "optType")?;
        non_trivia_children(&opt).first().cloned()
    } else {
        ch.get(1).cloned()
    };
    let ty = match ty_spec {
        None => None,
        Some(spec) => {
            let spec = as_node(Some(&spec), "typeSpec")?;
            Some(non_trivia_children(&spec).get(1).cloned().ok_or_else(|| ill("typeSpec term"))?)
        }
    };
    Ok((binders, ty))
}

/// `declVal := declValSimple <|> declValEqns <|> whereStructInst`.
fn decode_decl_val(v: &SyntaxNode, kinds: &KindInterner) -> Result<SynElem, ElabError> {
    match kinds.name(v.kind()) {
        "Lean.Parser.Command.declValSimple" => {
            let ch = non_trivia_children(v);
            if let Some(NodeOrToken::Node(suffix)) = ch.get(2) {
                if non_trivia_children(suffix).iter().any(|s| s.as_node().is_some_and(|n| !is_empty(n))) {
                    return Err(seam("termination hints — later M4 (recursion)"));
                }
            }
            if let Some(NodeOrToken::Node(w)) = ch.get(3) {
                if !is_empty(w) {
                    return Err(seam("`where` declarations — later M4"));
                }
            }
            ch.get(1).cloned().ok_or_else(|| ill("declValSimple term"))
        }
        "Lean.Parser.Command.declValEqns" => {
            Err(seam("pattern-matching equations — later M4 (match / equation compiler)"))
        }
        "Lean.Parser.Command.whereStructInst" => Err(seam("`where` structure instance — later M4")),
        other => Err(ill(&format!("declVal kind {other}"))),
    }
}

/// The oracle elaborates the body under `withFunLocalDecls`
/// (`MutualDef.lean:1343`): the short name resolves to the function being
/// defined, i.e. recursion. leanr has no recursion, so any use seams.
fn check_no_self_reference(name: &str, value: &SynElem, kinds: &KindInterner) -> Result<(), ElabError> {
    let dotted = format!("{name}.");
    let hit = |text: &str| text == name || text.starts_with(&dotted);
    let found = match value {
        NodeOrToken::Token(t) => kinds.name(t.kind()) == "<ident>" && hit(t.text()),
        NodeOrToken::Node(n) => n
            .descendants_with_tokens()
            .filter_map(|el| el.into_token())
            .any(|t| kinds.name(t.kind()) == "<ident>" && hit(t.text())),
    };
    if found {
        return Err(seam(format!("recursive reference to `{name}` — later M4 (recursion)")));
    }
    Ok(())
}
```

Adapt `descendants_with_tokens`/`into_token`/`as_node`/`text()` to the `leanr_syntax::tree` API: read `crates/leanr_syntax/src/tree.rs` and copy the idioms `dispatch.rs` uses. Keep the behavior as written.

In `command/mod.rs`:

```rust
//! Command elaboration (M4c). M4c-1: a single non-recursive
//! `def`/`theorem`/`abbrev`/`opaque`/`axiom`/`example` becomes kernel
//! declarations (spec `docs/superpowers/specs/2026-10-03-m4c1-single-decl-design.md`,
//! plan `docs/superpowers/plans/2026-10-03-m4c1-p2-command-elab.md`).

pub(crate) mod view;
```

and in `lib.rs`, next to the other `pub mod` lines: `pub mod command; // M4c-1 P2`.

- [ ] **Step 4: Run the tests to confirm they pass.**

Run: `cargo test -p leanr_elab --lib command::view`
Expected: all PASS. (`DefKind`/`DefView` are unused outside tests until Task 6. If clippy flags dead code, add `#[allow(dead_code)]` on the module with a comment "used from Task 6", and remove it in Task 6.)

- [ ] **Step 5: Run the mutations.** Each must FAIL the named test; then revert.
  1. Drop the `starts_with(&dotted)` half of `hit` → `self_reference_is_a_recursion_seam` FAILS (`sr.foo`).
  2. Make `hit` use `starts_with(name)` (no dot) → the `srx` assertion FAILS.
  3. Skip `check_modifiers` → `modifiers_are_named_seams` FAILS.
  4. Accept dotted names → `dotted_decl_name_is_an_m4c2_seam` FAILS.

- [ ] **Step 6: Commit.**

```bash
git add crates/leanr_elab/src/command crates/leanr_elab/src/lib.rs
git commit -m "leanr_elab: command::view — DefView decoding and M4c-1 named seams"
```

### Task 6: `CommandElab` and the `def`/`abbrev`/`opaque`/`example` pipeline, plus the gate

**Files:**
- Modify: `crates/leanr_elab/src/command/mod.rs` (`CommandElab`, `Built`, commit)
- Create: `crates/leanr_elab/src/command/levels.rs` (`with_level_names`, `level_mvar_to_param`)
- Create: `crates/leanr_elab/src/command/header.rs` (`expand_decl_id`, `elab_header`)
- Create: `crates/leanr_elab/src/command/def.rs` (body, level params, unassigned check, decl build)
- Modify: `crates/leanr_elab/src/builtin/binder/mod.rs` (`pub(crate) use fun::cleanup_annotations;` if not already reachable as `crate::builtin::binder::fun::cleanup_annotations`)
- Modify: `crates/leanr_elab/tests/support/mod.rs` (`with_command_elab`, `run_decl_corpus`)
- Modify: `crates/leanr_elab/tests/oracle_decl.rs` (`oracle_decl_gate`, `ENABLED`, smoke tests)

**Interfaces:**
- Consumes:
  - `DefView`/`DefKind` (Task 5)
  - `get_mvars`, `get_level_mvars`, `log_unassigned_*`, `register_custom_error_if_mvar` (Task 4)
  - the per-name `push_binder_group` (Task 3)
  - the error variants (Task 2)
  - P1: `Environment::add_decl_in`, `leanr_kernel::check_declaration`, `leanr_kernel::bank::scratch::promote_name`, `MetaCtx::{level_mvar_to_param, collect_level_params, get_max_height}`, `leanr_meta::{sort_decl_level_params, CollectLevelParams}`
- Produces:

```rust
// command/mod.rs
pub struct CommandElab<'x> { /* env: Environment, exts: EnvExtensions<'x> */ }
impl<'x> CommandElab<'x> {
    pub fn new(env: Environment, exts: EnvExtensions<'x>) -> Self;
    pub fn env(&self) -> &Environment;
    pub fn into_env(self) -> Environment;
    /// The persistent names of the constants added, in admission order
    /// (aux `_proof_N` theorems first, the main declaration last); empty for `example`.
    pub fn elab_decl(&mut self, cmd: &SyntaxNode, kinds: &KindInterner) -> Result<Vec<NameId>, ElabError>;
}
pub(crate) enum Built { Add(Vec<Declaration>), Check(Declaration) }

// command/header.rs
pub(super) struct DeclId { pub name: NameId, pub short: String, pub level_names: Vec<NameId> }
pub(super) struct Header { pub ty: ExprId, pub level_names: Vec<NameId>, pub num_params: usize }
pub(super) fn expand_decl_id(elab: &mut TermElabM, view: &DefView) -> Result<DeclId, ElabError>;
pub(super) fn elab_header(elab: &mut TermElabM, view: &DefView, id: &DeclId, kinds: &KindInterner) -> Result<Header, ElabError>;
pub(super) fn unknown_ident_to_auto_bound_seam(e: ElabError) -> ElabError;

// command/def.rs
pub(super) fn elab_def(elab: &mut TermElabM, view: &DefView, kinds: &KindInterner) -> Result<Built, ElabError>;
pub(super) fn fix_level_params(elab: &mut TermElabM, exprs: &[ExprId], all_user: &[NameId]) -> Result<Vec<NameId>, ElabError>;
pub(super) fn ensure_no_unassigned_mvars_at_pre_def(elab: &mut TermElabM, decl: &str, ty: ExprId, value: ExprId) -> Result<(), ElabError>;
pub(super) fn reject_let(elab: &TermElabM, e: ExprId) -> Result<(), ElabError>;

// command/levels.rs (impl TermElabM)
pub(crate) fn with_level_names<R>(&mut self, names: Vec<NameId>, k: impl FnOnce(&mut Self) -> Result<R, ElabError>) -> Result<R, ElabError>;
pub(crate) fn level_mvar_to_param(&mut self, e: ExprId) -> Result<ExprId, ElabError>;

// tests/support/mod.rs
pub fn with_command_elab<R>(src: &str, k: impl FnOnce(&mut leanr_elab::command::CommandElab<'_>, &SyntaxNode, &KindInterner) -> R) -> R;
pub fn run_decl_corpus(queries: &str, enabled: impl Fn(&str) -> bool) -> usize;
```

**Level-name convention.** `TermElabM::level_names` holds the oracle's `levelNames` list order, so index 0 is the MOST RECENTLY declared name. `.{u, v}` gives `[v, u]` (`expandDeclId`'s `foldlM … (id :: levelNames)`, `DeclModifiers.lean:330-337`). `Term.levelMVarToParam` prepends its new names reversed (`TermElabM.lean:1059-1065`: `setLevelNames (r.newParamNames.reverse.toList ++ levelNames)`), always starting at index 1. `sort_decl_level_params` (P1) takes `scope_params`/`all_user_params` in this same order. M4c-1 has no `universe` command, so the scope's level names are always `[]`.

The oracle flow this task ports, for a non-theorem, non-Prop header:
1. `expandDeclId`:
   - the univ fold raises the duplicate error;
   - `mkDeclName` → `applyVisibility` → `checkNotAlreadyDeclared`.
2. `elabHeaders`' per-view body (`MutualDef.lean:254-292`), under `withLevelNames levelNames`:
   - `elabBindersEx`;
   - `elabType typeStx`, or `elabType (mkHole value)` when the type is omitted;
   - `registerFailedToInferDefTypeInfo`;
   - `synthesizeSyntheticMVarsNoPostponing`;
   - `mkForallFVars' xs type` (the prime only sets mvar user names; expression-identical);
   - `instantiateMVars`;
   - if the type was written: `logUnassignedUsingErrorInfos (getMVars type)`.
3. `finishElab` → `elabFunValues` (`:515-560`):
   - `forallBoundedTelescope header.type header.numParams (cleanupAnnotations := true)`;
   - `elabTermEnsuringType valStx type`;
   - `synthesizeSyntheticMVarsNoPostponing`;
   - `instantiateMVars`;
   - `mkLambdaFVars xs val`.

   Then `synthesizeSyntheticMVarsNoPostponing` again, and `instantiateMVars` on the values and headers (`:1398-1403`).
4. `levelMVarToParamTypesPreDecls` under `withLevelNames allUserLevelNames` (`:1431`; types only, `PreDefinition/Basic.lean:56-58`), then `instantiateMVarsAtPreDecls`, then `fixLevelParams preDefs [] allUserLevelNames` (`:1435`).
5. `addPreDefinitions` → `ensureNoUnassignedMVarsAtPreDef` (`PreDefinition/Main.lean:99-110`, `:76-97`) → `addAndCompileNonRec` → `addNonRecAux` (`PreDefinition/Basic.lean:179-210`):
   - `letToHaveType`/`Value` (a seam here);
   - build the declaration;
   - `addDecl`.

   `example` runs under `withoutModifyingEnv` (`MutualDef.lean:1195-1203`): kernel-checked, then discarded.

**Deliberate omissions** (no observable effect in M4c-1; each is noted in a doc comment):
- `withFunLocalDecls`'s auxDecl, since self-reference is a seam;
- `shareCommonPreDefs` (hash-consing);
- `fixLevelParams`' self-`const` rewrite (no self-reference);
- `ensureEqnReservedNamesAvailable` (root names only);
- `cleanupOfNat` (instances only);
- attributes, compilation, docs and info trees (spec seams).

- [ ] **Step 1: Write the gate and the smoke tests.** In `tests/support/mod.rs`, append:

```rust
/// Replay Elab0 into a fresh owned `Environment`, parse `src` as one
/// command, and run `k` with a `CommandElab` over them. One replay per call:
/// the spec's per-record environment (§ Harness).
pub fn with_command_elab<R>(
    src: &str,
    k: impl FnOnce(
        &mut leanr_elab::command::CommandElab<'_>,
        &leanr_syntax::tree::SyntaxNode,
        &leanr_syntax::kind::KindInterner,
    ) -> R,
) -> R {
    let Replayed {
        env,
        reducibility,
        matchers,
        instances,
        default_instances,
        projection_fns,
        classes,
        coe_decls,
        aux_recs,
        elab_as_elim,
        structures,
    } = replay_fixture_in("elab", "Elab0.olean");
    let exts = leanr_meta::EnvExtensions {
        reducibility: &reducibility,
        matchers: &matchers,
        instances: &instances,
        default_instances: &default_instances,
        projection_fns: &projection_fns,
        classes: &classes,
        coe_decls: &coe_decls,
        aux_recs: &aux_recs,
        elab_as_elim: &elab_as_elim,
        structures: &structures,
    };
    let (parsed, cmd) = parse_command(src);
    let mut ce = leanr_elab::command::CommandElab::new(env, exts);
    k(&mut ce, &cmd, &parsed.tree.kinds)
}

/// The canonical JSON of admitted constant `n`, in `dump_decls.lean`'s
/// `constJ` shape.
fn decl_const_json(env: &Environment, n: NameId) -> Value {
    use leanr_kernel::ReducibilityHints;
    let st = env.store();
    let name = |n: NameId| json!(name_to_string(st, None, Some(n)));
    let names = |ns: &[NameId]| Value::Array(ns.iter().map(|&n| name(n)).collect());
    let enc = |e: ExprId| encode_expr(st, None, e, &mut EncSt::default());
    let hints = |h: &ReducibilityHints| match h {
        ReducibilityHints::Opaque => json!("opaque"),
        ReducibilityHints::Abbrev => json!("abbrev"),
        ReducibilityHints::Regular(k) => json!({ "regular": k }),
    };
    let ci = env.get(n).expect("admitted constant is in the environment");
    let cv = ci.constant_val();
    let mut o = serde_json::Map::new();
    o.insert("name".into(), name(cv.name));
    o.insert("levelParams".into(), names(&cv.level_params));
    o.insert("type".into(), enc(cv.ty));
    match ci {
        ConstantInfo::Defn(d) => {
            o.insert("kind".into(), json!("defn"));
            o.insert("value".into(), enc(d.value));
            o.insert("hints".into(), hints(&d.hints));
            let safety = match d.safety {
                leanr_kernel::DefinitionSafety::Safe => "safe",
                leanr_kernel::DefinitionSafety::Unsafe => "unsafe",
                leanr_kernel::DefinitionSafety::Partial => "partial",
            };
            o.insert("safety".into(), json!(safety));
            o.insert("all".into(), names(&d.all));
        }
        ConstantInfo::Thm(t) => {
            o.insert("kind".into(), json!("thm"));
            o.insert("value".into(), enc(t.value));
            o.insert("all".into(), names(&t.all));
        }
        ConstantInfo::Opaque(v) => {
            o.insert("kind".into(), json!("opaque"));
            o.insert("value".into(), enc(v.value));
            o.insert("unsafe".into(), json!(v.is_unsafe));
            o.insert("all".into(), names(&v.all));
        }
        ConstantInfo::Axiom(a) => {
            o.insert("kind".into(), json!("axiom"));
            o.insert("unsafe".into(), json!(a.is_unsafe));
        }
        other => panic!("elab_decl admitted an unexpected constant kind: {other:?}"),
    }
    Value::Object(o)
}

/// Elaborate every enabled `{id, src, consts|err}` record of
/// `tests/fixtures/elab/<queries>` in its own fresh Elab0 environment and
/// compare with the oracle: the admitted constants' canonical JSON (sorted
/// by `Name.lt`, as the dumper sorts), or the first error line. Panics
/// listing every divergence; returns the number of records checked.
pub fn run_decl_corpus(queries: &str, enabled: impl Fn(&str) -> bool) -> usize {
    let text = std::fs::read_to_string(fixture_in("elab", queries))
        .unwrap_or_else(|e| panic!("committed decl corpus {queries}: {e}"));
    let mut failures = Vec::new();
    let mut checked = 0usize;
    for line in text.lines().filter(|l| !l.trim().is_empty()) {
        let q: Value = serde_json::from_str(line).expect("committed JSONL is valid");
        let id = q["id"].as_str().expect("id").to_string();
        if !enabled(&id) {
            continue;
        }
        checked += 1;
        let src = q["src"].as_str().expect("src").to_string();
        assert!(
            !q.to_string().contains("\"sorryAx\""),
            "{id}: the oracle record contains sorryAx — it is an oracle error"
        );
        with_command_elab(&src, |ce, cmd, kinds| {
            let got = ce.elab_decl(cmd, kinds);
            if let Some(want) = q.get("err").and_then(Value::as_str) {
                match got {
                    Err(e) => {
                        let line = e.oracle_first_line();
                        if line.as_deref() != Some(want) {
                            failures.push(format!(
                                "{id}: leanr error {e:?} (first line {line:?}); oracle {want:?}"
                            ));
                        }
                    }
                    Ok(ns) => failures.push(format!(
                        "{id}: leanr admitted {} constant(s); oracle errors with {want:?}",
                        ns.len()
                    )),
                }
                return;
            }
            let want = q["consts"].as_array().expect("consts").clone();
            let names = match got {
                Ok(ns) => ns,
                Err(e) => {
                    failures.push(format!("{id}: leanr error {e:?}; oracle admits {}", want.len()));
                    return;
                }
            };
            let env = ce.env();
            // Admission order: the main declaration last, every aux before it.
            let rendered: Vec<String> = names
                .iter()
                .map(|&n| name_to_string(env.store(), None, Some(n)))
                .collect();
            if let Some((last, auxes)) = rendered.split_last() {
                if last.contains("._proof_") || auxes.iter().any(|a| !a.contains("._proof_")) {
                    failures.push(format!("{id}: admission order {rendered:?}"));
                }
            }
            let mut sorted = names.clone();
            sorted.sort_by(|a, b| leanr_meta::name_cmp(env.store(), None, Some(*a), Some(*b)));
            let got_json: Vec<Value> = sorted.iter().map(|&n| decl_const_json(env, n)).collect();
            let s = Value::Array(got_json.clone()).to_string();
            for bad in ["\"sorryAx\"", "\"k\":\"fvar\"", "\"k\":\"mvar\"", "\"k\":\"lmvar\""] {
                if s.contains(bad) {
                    failures.push(format!("{id}: admitted constant contains {bad}"));
                }
            }
            if got_json != want {
                failures.push(format!(
                    "{id}:\n  leanr  {s}\n  oracle {}",
                    Value::Array(want)
                ));
            }
        });
    }
    assert!(
        failures.is_empty(),
        "{} decl divergence(s):\n{}",
        failures.len(),
        failures.join("\n")
    );
    checked
}
```

Add `Environment`, `ConstantInfo`, `NameId`, `ExprId`, `json`, `Value` imports as the support file needs: check the `use` lines at the top of `crates/leanr_meta/tests/support/mod.rs`, which `pub use meta_support::*` re-exports. Check that `ConstantInfo::constant_val()` exists (`leanr_kernel/src/decl.rs`); `leanr_elab/src/elab.rs` calls it.

In `oracle_decl.rs`, append:

```rust
/// The records the pipeline handles so far. Tasks 7-9 of
/// `docs/superpowers/plans/2026-10-03-m4c1-p2-command-elab.md` append theirs;
/// Task 10 deletes this list and gates the whole corpus.
const ENABLED: &[&str] = &[
    // Task 6 — def/abbrev/opaque/example
    "kind/def", "kind/abbrev", "kind/opaque", "kind/example", "kind/exampleParams",
    "type/inferred", "type/unify", "type/lamValue", "type/implicitBinder", "type/instBinder",
    "type/optParamCleanup", "type/headerMVarSolvedByBody", "type/groupHoles",
    "univ/explicit1", "univ/explicit2", "univ/sortHole", "univ/idBody", "univ/order",
    "univ/orderRev", "univ/skipUsedName", "univ/defElevenLex", "univ/defHeaderUnivByBody",
    "univ/abbrevUniv",
    "height/pick", "height/id", "height/overThm", "height/abbrev", "height/explicitTy",
    "err/already", "err/univDup", "err/unusedUniv", "err/unusedUniv2", "err/mismatch",
    "err/exampleMismatch", "err/appLast", "err/unassignedImplicit", "err/holeArg",
    "err/holeBare", "err/binderHole", "err/funBinderType", "err/defTypeHole",
    "err/levelMVarValue", "err/unknownIdBody",
];

#[test]
fn oracle_decl_gate() {
    let checked = support::run_decl_corpus("decl-queries.jsonl", |id| ENABLED.contains(&id));
    assert_eq!(checked, ENABLED.len(), "an ENABLED id is missing from the corpus");
}

fn decl_result(src: &str) -> Result<Vec<String>, leanr_elab::ElabError> {
    support::with_command_elab(src, |ce, cmd, kinds| {
        ce.elab_decl(cmd, kinds).map(|ns| {
            ns.iter()
                .map(|&n| support::name_to_string(ce.env().store(), None, Some(n)))
                .collect()
        })
    })
}

fn seam_message(src: &str) -> String {
    match decl_result(src) {
        Err(leanr_elab::ElabError::UnsupportedSyntax(m)) => m,
        other => panic!("{src:?}: expected a named seam, got {other:?}"),
    }
}

#[test]
fn header_unknown_ident_is_the_auto_bound_seam() {
    // The oracle auto-binds `α` (probe: `def ab (a : α) : α := a` admits `ab.{u_1}`).
    let m = seam_message("def ab (a : α) : α := a");
    assert!(m.contains("auto-bound") && m.contains("M4c-2"), "{m}");
}

#[test]
fn header_unknown_universe_is_the_auto_bound_seam() {
    // probe: `def uuh (α : Sort w) : Sort w := α` admits `uuh.{w}`.
    let m = seam_message("def uuh (α : Sort w) : Sort w := α");
    assert!(m.contains("auto-bound"), "{m}");
}

#[test]
fn let_and_have_in_a_value_are_the_let_to_have_seam() {
    assert!(seam_message("def sl : Nat := let x := Nat.zero; x").contains("letToHave"));
    assert!(seam_message("def sh : Nat := have x := Nat.zero; x").contains("letToHave"));
}

#[test]
fn example_is_checked_but_not_added() {
    support::with_command_elab("example : Nat := Nat.zero", |ce, cmd, kinds| {
        let before = ce.env().len();
        assert_eq!(ce.elab_decl(cmd, kinds).expect("elaborates"), Vec::new());
        assert_eq!(ce.env().len(), before, "an example must not add constants");
    });
}
```

`Environment::len` may not exist. Use whatever constant-count accessor the kernel offers (`grep -n "pub fn" crates/leanr_kernel/src/env.rs`), or assert that `_example` is absent by interning it into a throwaway lookup. Do NOT add a method to `leanr_kernel`, which is the TCB; if nothing fits, assert absence by name.

- [ ] **Step 2: Run them to confirm they fail.**

Run: `cargo test -p leanr_elab --test oracle_decl`
Expected: compile error (`leanr_elab::command::CommandElab` missing).

- [ ] **Step 3: Write `command/levels.rs`.**

```rust
//! Term-level universe-name scoping used by command elaboration.

use leanr_kernel::bank::{ExprId, NameId};

use crate::elab::TermElabM;
use crate::error::ElabError;

impl TermElabM<'_> {
    /// oracle: `withLevelNames` (`Elab/Term/TermElabM.lean`) — run `k` with
    /// `level_names` replaced, restored on both paths.
    pub(crate) fn with_level_names<R>(
        &mut self,
        names: Vec<NameId>,
        k: impl FnOnce(&mut Self) -> Result<R, ElabError>,
    ) -> Result<R, ElabError> {
        let prev = std::mem::replace(&mut self.level_names, names);
        let out = k(self);
        self.level_names = prev;
        out
    }

    /// oracle: `Term.levelMVarToParam` (`Elab/Term/TermElabM.lean:1059-1065`):
    /// fresh `u_i` avoiding `levelNames`, index from 1, and the new names
    /// prepended REVERSED (head = most recent).
    pub(crate) fn level_mvar_to_param(&mut self, e: ExprId) -> Result<ExprId, ElabError> {
        let r = self.mctx.level_mvar_to_param(e, &self.level_names, 1)?;
        let mut names = r.new_param_names;
        names.reverse();
        names.extend(self.level_names.iter().copied());
        self.level_names = names;
        Ok(r.expr)
    }
}
```

- [ ] **Step 4: Write `command/header.rs`.**

```rust
//! Declaration headers: oracle `expandDeclId` (`Elab/DeclModifiers.lean:
//! 318-339`) and `elabHeaders`' per-view body (`Elab/MutualDef.lean:254-292`).

use leanr_kernel::bank::{ExprId, NameId};
use leanr_meta::{MVarKind, MetaError};
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::NodeOrToken;

use super::view::{DefKind, DefView};
use crate::builtin::binder::{elab_type, extract_binder_group, push_binder_group};
use crate::dispatch::SynElem;
use crate::elab::TermElabM;
use crate::error::ElabError;

pub(super) struct DeclId {
    pub name: NameId,
    pub short: String,
    /// oracle order: head = last declared (`.{u, v}` → `[v, u]`).
    pub level_names: Vec<NameId>,
}

pub(super) struct Header {
    /// `∀ binders, type`, instantiated.
    pub ty: ExprId,
    /// `levelNames` after the header (`DefViewElabHeaderData.levelNames`).
    pub level_names: Vec<NameId>,
    pub num_params: usize,
}

pub(super) fn intern_atomic(elab: &mut TermElabM, s: &str) -> Result<NameId, ElabError> {
    let base = elab.view.store;
    let st = elab.mctx.store_mut();
    let sid = st.intern_str(Some(base), s).map_err(MetaError::from)?;
    Ok(st.name_str(Some(base), None, sid).map_err(MetaError::from)?)
}

/// oracle: `expandDeclId` (`DeclModifiers.lean:318-339`). The `.{…}` fold
/// conses onto the scope's level names (`[]` in M4c-1) and rejects a
/// repeat. Then `mkDeclName` (`:263-286`) → `applyVisibility` (`:244-251`)
/// → `checkNotAlreadyDeclared` (`:29-55`). The reserved-name and private
/// checks cannot fire for the atomic, unmodified names `view.rs` admits.
pub(super) fn expand_decl_id(elab: &mut TermElabM, view: &DefView) -> Result<DeclId, ElabError> {
    let mut level_names: Vec<NameId> = Vec::new();
    for u in &view.univ_names {
        let id = intern_atomic(elab, u)?;
        if level_names.contains(&id) {
            return Err(ElabError::UniverseAlreadyDeclared(u.clone()));
        }
        level_names.insert(0, id);
    }
    // `example`'s name is `_example` (`DefView.lean:204`).
    let short = view.name.clone().unwrap_or_else(|| "_example".to_string());
    let name = intern_atomic(elab, &short)?;
    if elab.view.get(name).is_some() {
        return Err(ElabError::AlreadyDeclared(short));
    }
    Ok(DeclId {
        name,
        short,
        level_names,
    })
}

/// oracle: `elabHeaders` runs under `withAutoBoundImplicit`
/// (`MutualDef.lean:253-254`; `elabAxiom` too, `Declaration.lean:108`): an
/// unbound identifier or universe in a header is auto-bound, not an error.
/// Auto-bound implicits are M4c-2.
pub(super) fn unknown_ident_to_auto_bound_seam(e: ElabError) -> ElabError {
    match e {
        ElabError::UnknownIdent(s) => ElabError::UnsupportedSyntax(format!(
            "unbound `{s}` in a declaration header (auto-bound implicit) — M4c-2"
        )),
        e => e,
    }
}

pub(super) fn elab_header(
    elab: &mut TermElabM,
    view: &DefView,
    id: &DeclId,
    kinds: &KindInterner,
) -> Result<Header, ElabError> {
    elab.with_level_names(id.level_names.clone(), |elab| {
        let cp = elab.mctx.lctx_checkpoint();
        let out = header_in_scope(elab, view, kinds);
        elab.mctx.lctx_restore(cp);
        out
    })
    .map_err(unknown_ident_to_auto_bound_seam)
}

fn header_in_scope(
    elab: &mut TermElabM,
    view: &DefView,
    kinds: &KindInterner,
) -> Result<Header, ElabError> {
    let mut xs = Vec::new();
    for b in &view.binders {
        let g = extract_binder_group(elab, b, kinds)?;
        xs.extend(push_binder_group(elab, &g, kinds)?);
    }
    let ty = match &view.ty {
        Some(t) => {
            let ty = elab_type(elab, t, kinds)?;
            register_failed_to_infer_def_type_info(elab, view, ty, t.clone());
            ty
        }
        None => {
            // oracle: `elabType (mkHole refForElabFunType)` (`MutualDef.lean:
            // 265-270`): `elabHole` against `Sort ?u` mints a natural mvar
            // and registers its hole info (`BuiltinTerm.lean:62-68`); the
            // ref is the value syntax.
            let r = view
                .value
                .clone()
                .ok_or_else(|| ElabError::Internal("a header without a type needs a value".into()))?;
            let u = elab.mk_fresh_level_mvar()?;
            let sort = elab
                .mctx
                .store_mut()
                .expr_sort(None, u)
                .map_err(MetaError::from)?;
            let (ty, mid) = elab.mk_fresh_expr_mvar_of_kind(sort, MVarKind::Natural)?;
            elab.register_mvar_error_hole_info(mid, r.clone());
            register_failed_to_infer_def_type_info(elab, view, ty, r);
            ty
        }
    };
    elab.synthesize_synthetic_mvars_no_postponing(kinds)?;
    // `mkForallFVars' xs type` only sets mvar user names for messages.
    let ty = elab.mctx.mk_forall(&xs, ty)?;
    let ty = elab.mctx.instantiate_mvars(ty)?;
    if view.ty.is_some() {
        let pending = elab.get_mvars(ty)?;
        if let Some(e) = elab.log_unassigned_using_error_infos(&pending)? {
            return Err(e);
        }
    }
    Ok(Header {
        ty,
        level_names: elab.level_names.clone(),
        num_params: xs.len(),
    })
}

/// oracle: `registerFailedToInferDefTypeInfo` (`MutualDef.lean:123-137`).
fn register_failed_to_infer_def_type_info(
    elab: &mut TermElabM,
    view: &DefView,
    ty: ExprId,
    stx: SynElem,
) {
    let what = match view.kind {
        DefKind::Example => "example".to_string(),
        DefKind::Theorem => format!("theorem `{}`", decl_id_text(view)),
        _ => format!("definition `{}`", decl_id_text(view)),
    };
    elab.register_custom_error_if_mvar(ty, stx, format!("Failed to infer type of {what}"));
}

/// `{view.declId}` in a message: the oracle pretty-prints the `declId`
/// syntax. For the atomic names M4c-1 admits, the source text agrees with
/// that (at most whitespace inside `.{…}` could differ).
fn decl_id_text(view: &DefView) -> String {
    match &view.decl_id {
        Some(NodeOrToken::Node(n)) => n.text().to_string().trim().to_string(),
        Some(NodeOrToken::Token(t)) => t.text().to_string(),
        None => String::new(),
    }
}
```

Make `elab_type` and `extract_binder_group` reachable from `crate::command` if they are not: they are `pub(crate)` in `builtin::binder`, so check that `builtin` and `binder` are reachable modules (`pub mod builtin` in `lib.rs`; `binder` may need `pub(crate) mod binder` in `builtin/mod.rs`).

- [ ] **Step 5: Write `command/def.rs`.**

```rust
//! The `def`/`abbrev`/`opaque`/`example` pipeline: oracle `finishElab`
//! (`Elab/MutualDef.lean:1343-1440`) → `addPreDefinitions`
//! (`PreDefinition/Main.lean:288-311`) → `addNonRecAux`
//! (`PreDefinition/Basic.lean:179-210`), restricted to one non-recursive
//! declaration (spec § The oracle model, steps 5-8).
//!
//! Not modelled, none observable in M4c-1: `withFunLocalDecls`'s auxDecl
//! (self-reference is a `view.rs` seam), `shareCommonPreDefs`,
//! `fixLevelParams`' self-`const` rewrite (same reason),
//! `ensureEqnReservedNamesAvailable` (root names only), attributes,
//! compilation, docs and info trees (spec seams).

use std::collections::HashSet;

use leanr_kernel::bank::terms::Node;
use leanr_kernel::bank::{ExprId, NameId};
use leanr_kernel::{
    ConstantVal, Declaration, DefinitionSafety, DefinitionVal, OpaqueVal, ReducibilityHints,
};
use leanr_meta::{sort_decl_level_params, CollectLevelParams};
use leanr_syntax::kind::KindInterner;

use super::header::{self, Header};
use super::view::{DefKind, DefView};
use super::Built;
use crate::builtin::binder::fun::cleanup_annotations;
use crate::elab::TermElabM;
use crate::error::ElabError;

pub(super) fn elab_def(
    elab: &mut TermElabM,
    view: &DefView,
    kinds: &KindInterner,
) -> Result<Built, ElabError> {
    let id = header::expand_decl_id(elab, view)?;
    let header = header::elab_header(elab, view, &id, kinds)?;
    let value = elab_value(elab, view, &header, kinds)?;
    // `finishElab` (`MutualDef.lean:1398-1403`): synthesize once more, then
    // instantiate the values and the headers.
    elab.synthesize_synthetic_mvars_no_postponing(kinds)?;
    let value = elab.mctx.instantiate_mvars(value)?;
    let ty = elab.mctx.instantiate_mvars(header.ty)?;
    // `levelMVarToParamTypesPreDecls` under `withLevelNames allUserLevelNames`
    // (`MutualDef.lean:1431`; `PreDefinition/Basic.lean:56-58`): TYPES only.
    let ty = elab.with_level_names(header.level_names.clone(), |elab| {
        elab.level_mvar_to_param(ty)
    })?;
    // `instantiateMVarsAtPreDecls` (`:1432`).
    let ty = elab.mctx.instantiate_mvars(ty)?;
    let value = elab.mctx.instantiate_mvars(value)?;
    // `fixLevelParams preDefs scopeLevelNames allUserLevelNames` (`:1434-1435`).
    let level_params = fix_level_params(elab, &[ty, value], &header.level_names)?;
    // `addPreDefinitions` → `ensureNoUnassignedMVarsAtPreDef` (`Main.lean:294`).
    ensure_no_unassigned_mvars_at_pre_def(elab, &id.short, ty, value)?;
    // `addNonRecAux` → `letToHaveType`/`letToHaveValue` (`Basic.lean:181-182`):
    // a seam (spec decision 5). Checked before `abstractNestedProofs` (oracle
    // order: after it); both orders end in a seam.
    reject_let(elab, ty)?;
    reject_let(elab, value)?;
    let decl = build_decl(elab, view.kind, id.name, level_params, ty, value)?;
    Ok(if view.kind == DefKind::Example {
        Built::Check(decl)
    } else {
        Built::Add(vec![decl])
    })
}

/// oracle: `elabFunValues`' per-header body (`MutualDef.lean:533-554`).
fn elab_value(
    elab: &mut TermElabM,
    view: &DefView,
    header: &Header,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let value_stx = view
        .value
        .clone()
        .ok_or_else(|| ElabError::Internal("a definition without a value".into()))?;
    elab.with_level_names(header.level_names.clone(), |elab| {
        let cp = elab.mctx.lctx_checkpoint();
        let out = (|| {
            // `forallBoundedTelescope header.type header.numParams
            // (cleanupAnnotations := true)` (`:536`): fresh locals whose
            // types drop `optParam`/`autoParam`/`outParam` wrappers.
            let base = Some(elab.view.store);
            let mut xs = Vec::with_capacity(header.num_params);
            let mut cur = header.ty;
            for _ in 0..header.num_params {
                let Node::Forall {
                    binder_name,
                    binder_type,
                    body,
                    binder_info,
                } = elab.mctx.store().expr_node(base, cur)
                else {
                    return Err(ElabError::Internal(
                        "header type has fewer binders than the header".into(),
                    ));
                };
                let dom = cleanup_annotations(elab, binder_type);
                let x = elab.mctx.push_local_decl(binder_name, dom, binder_info)?;
                xs.push(x);
                cur = elab.mctx.instantiate1(body, x)?;
            }
            let val = elab.elab_term_ensuring_type(&value_stx, kinds, Some(cur))?;
            elab.synthesize_synthetic_mvars_no_postponing(kinds)?;
            let val = elab.mctx.instantiate_mvars(val)?;
            Ok(elab.mctx.mk_lambda(&xs, val)?)
        })();
        elab.mctx.lctx_restore(cp);
        out
    })
}

/// oracle: `getLevelParamsPreDecls` (`PreDefinition/Basic.lean:66-73`):
/// collect from each expression, then `sortDeclLevelParams [] allUser used`.
pub(super) fn fix_level_params(
    elab: &mut TermElabM,
    exprs: &[ExprId],
    all_user: &[NameId],
) -> Result<Vec<NameId>, ElabError> {
    let mut s = CollectLevelParams::default();
    for &e in exprs {
        elab.mctx.collect_level_params(&mut s, e)?;
    }
    let base = Some(elab.view.store);
    sort_decl_level_params(elab.mctx.store(), base, &[], all_user, &s.params).map_err(|u| {
        ElabError::UnusedUniverseParam(elab.mctx.store().to_name(base, Some(u)).to_string())
    })
}

/// oracle: `ensureNoUnassignedMVarsAtPreDef` (`PreDefinition/Main.lean:99-110`)
/// and `ensureNoUnassignedLevelMVarsAtPreDef` (`:76-97`, value only).
pub(super) fn ensure_no_unassigned_mvars_at_pre_def(
    elab: &mut TermElabM,
    decl: &str,
    ty: ExprId,
    value: ExprId,
) -> Result<(), ElabError> {
    // `getMVarsAtPreDef`: the type's mvars, then the value's.
    let mut pending = elab.get_mvars(ty)?;
    for m in elab.get_mvars(value)? {
        if !pending.contains(&m) {
            pending.push(m);
        }
    }
    if let Some(e) = elab.log_unassigned_using_error_infos(&pending)? {
        return Err(e);
    }
    let base = Some(elab.view.store);
    if !elab.mctx.store().expr_data(base, value).has_level_mvar() {
        return Ok(());
    }
    let lpending = elab.get_level_mvars(value)?;
    if let Some(e) = elab.log_unassigned_level_mvars_using_error_infos(&lpending)? {
        return Err(e);
    }
    // The fallback when no level error info covers them (`:84-93`).
    Err(ElabError::UnassignedLevelMVars(format!(
        "declaration `{decl}` contains universe level metavariables at the expression"
    )))
}

/// The `letToHave` seam (spec decision 5): any `let`/`have` left in the
/// final type or value.
pub(super) fn reject_let(elab: &TermElabM, e: ExprId) -> Result<(), ElabError> {
    let base = Some(elab.view.store);
    let mut seen: HashSet<ExprId> = HashSet::new();
    let mut stack = vec![e];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match elab.mctx.store().expr_node(base, t) {
            Node::LetE { .. } => {
                return Err(ElabError::UnsupportedSyntax(
                    "`let`/`have` in a declaration's type or value (letToHave) — later M4".into(),
                ))
            }
            Node::App { f, arg } => {
                stack.push(f);
                stack.push(arg);
            }
            Node::Lam { binder_type, body, .. } | Node::Forall { binder_type, body, .. } => {
                stack.push(binder_type);
                stack.push(body);
            }
            Node::MData { expr, .. } => stack.push(expr),
            Node::Proj { structure, .. } | Node::ProjBig { structure, .. } => {
                stack.push(structure)
            }
            _ => {}
        }
    }
    Ok(())
}

/// `addNonRecAux`'s declaration (`PreDefinition/Basic.lean:183-205`).
fn build_decl(
    elab: &mut TermElabM,
    kind: DefKind,
    name: NameId,
    level_params: Vec<NameId>,
    ty: ExprId,
    value: ExprId,
) -> Result<Declaration, ElabError> {
    let val = ConstantVal {
        name,
        level_params,
        ty,
    };
    Ok(match kind {
        // `mkDefDecl`: `regular (getMaxHeight env value + 1)`, safe.
        DefKind::Def | DefKind::Example => {
            let h = elab.mctx.get_max_height(value)?;
            Declaration::Defn(DefinitionVal {
                val,
                value,
                hints: ReducibilityHints::Regular(h + 1),
                safety: DefinitionSafety::Safe,
                all: vec![name],
            })
        }
        DefKind::Abbrev => Declaration::Defn(DefinitionVal {
            val,
            value,
            hints: ReducibilityHints::Abbrev,
            safety: DefinitionSafety::Safe,
            all: vec![name],
        }),
        DefKind::Opaque => Declaration::Opaque(OpaqueVal {
            val,
            value,
            is_unsafe: false,
            all: vec![name],
        }),
        DefKind::Theorem | DefKind::Axiom => {
            return Err(ElabError::Internal(format!("build_decl: {kind:?}")))
        }
    })
}
```

`elab.mctx.instantiate1`, `push_local_decl`, `mk_lambda` and `mk_forall` return `MetaError`; `?` converts it via `From`. If `cleanup_annotations` is unreachable as `crate::builtin::binder::fun::cleanup_annotations`, make `fun` `pub(crate) mod fun` (it already is) and make `binder` reachable.

- [ ] **Step 6: Write `CommandElab` in `command/mod.rs`.**

```rust
pub(crate) mod view;
mod def;
mod header;
mod levels;

use leanr_kernel::bank::scratch::promote_name;
use leanr_kernel::bank::{NameId, Store};
use leanr_kernel::{check_declaration, Declaration, Environment};
use leanr_meta::{Config, EnvExtensions, MetaCtx};
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::SyntaxNode;

use crate::elab::TermElabM;
use crate::error::ElabError;
use view::{DefKind, DefView};

/// What one declaration's elaboration scope hands to the commit step.
pub(crate) enum Built {
    /// Admit these in order: aux `_proof_N` theorems first, then the main
    /// declaration (each aux's `addDecl` precedes the main one's in the
    /// oracle, `Meta/Tactic/AuxLemma.lean:43-73`).
    Add(Vec<Declaration>),
    /// `example`: kernel-checked, then discarded (`withoutModifyingEnv`,
    /// `MutualDef.lean:1195-1203`).
    Check(Declaration),
}

/// The M4c-1 command elaborator: an environment that grows by one
/// declaration per [`CommandElab::elab_decl`] (spec § Architecture, Approach A).
pub struct CommandElab<'x> {
    env: Environment,
    exts: EnvExtensions<'x>,
}

impl<'x> CommandElab<'x> {
    pub fn new(env: Environment, exts: EnvExtensions<'x>) -> Self {
        CommandElab { env, exts }
    }

    pub fn env(&self) -> &Environment {
        &self.env
    }

    pub fn into_env(self) -> Environment {
        self.env
    }

    /// Elaborate one declaration command. Returns the admitted constants'
    /// persistent names in admission order; empty for `example`. On `Err`,
    /// the constants already admitted (aux theorems before a rejected main
    /// declaration) stay, as in the oracle.
    pub fn elab_decl(
        &mut self,
        cmd: &SyntaxNode,
        kinds: &KindInterner,
    ) -> Result<Vec<NameId>, ElabError> {
        let view = DefView::from_syntax(cmd, kinds)?;
        // One scratch store per declaration: `add_decl_in`'s scratch
        // lifecycle contract (`leanr_kernel/src/env.rs`).
        let mut scratch = Store::scratch();
        let built = {
            let env_view = self.env.view();
            let mctx = MetaCtx::new(env_view, &mut scratch, Config::default(), self.exts);
            let mut elab = TermElabM::new(mctx, env_view);
            match view.kind {
                DefKind::Theorem => Err(ElabError::UnsupportedSyntax(
                    "theorem — not yet ported (M4c-1 P2 Task 7)".into(),
                )),
                DefKind::Axiom => Err(ElabError::UnsupportedSyntax(
                    "axiom — not yet ported (M4c-1 P2 Task 9)".into(),
                )),
                _ => def::elab_def(&mut elab, &view, kinds),
            }?
        };
        self.commit(&mut scratch, built)
    }

    fn commit(&mut self, scratch: &mut Store, built: Built) -> Result<Vec<NameId>, ElabError> {
        match built {
            Built::Check(d) => {
                check_declaration(self.env.view(), scratch, d).map_err(ElabError::Kernel)?;
                Ok(Vec::new())
            }
            Built::Add(decls) => {
                // Promote the names first: after the first `add_decl_in` the
                // scratch store may only be passed to further `add_decl_in`s.
                // `promote_name` only reads it.
                let mut names = Vec::with_capacity(decls.len());
                for d in &decls {
                    let n = decl_name(d)?;
                    names.push(
                        promote_name(self.env.store_mut(), scratch, n).map_err(ElabError::Kernel)?,
                    );
                }
                for d in decls {
                    self.env.add_decl_in(scratch, d).map_err(ElabError::Kernel)?;
                }
                Ok(names)
            }
        }
    }
}

fn decl_name(d: &Declaration) -> Result<NameId, ElabError> {
    match d {
        Declaration::Axiom(v) => Ok(v.val.name),
        Declaration::Defn(v) => Ok(v.val.name),
        Declaration::Thm(v) => Ok(v.val.name),
        Declaration::Opaque(v) => Ok(v.val.name),
        _ => Err(ElabError::Internal(
            "command elaboration built an inductive/quot declaration".into(),
        )),
    }
}
```

Keep the module doc from Task 5 at the top, extended by one paragraph that names the files (`view.rs`, `header.rs`, `def.rs`, `levels.rs`) and what each ports.

- [ ] **Step 7: Run the gate and the smoke tests until they pass.**

Run: `cargo test -p leanr_elab --test oracle_decl`
Expected: `oracle_decl_gate`, `header_unknown_ident_is_the_auto_bound_seam`, `header_unknown_universe_is_the_auto_bound_seam`, `let_and_have_in_a_value_are_the_let_to_have_seam`, `example_is_checked_but_not_added` and `decl_corpus_sources_parse_as_one_command` all PASS.

A divergence lists `leanr` vs `oracle` JSON. Debug with superpowers:systematic-debugging: re-read the oracle step for the field that differs. If a record cannot be matched without porting something this plan does not list, stop and report it (spec amendment), rather than special-casing.

- [ ] **Step 8: Run the whole crate's suite.**

Run: `cargo test -p leanr_elab && cargo clippy -p leanr_elab --all-targets -- -D warnings`
Expected: PASS, no warnings.

- [ ] **Step 9: Run the mutations.** Each must FAIL the named test; then revert.
  1. In `levels.rs`, drop `names.reverse()` → `oracle_decl_gate` FAILS (`univ/skipUsedName` or the u_N records).
  2. In `def.rs`, skip `cleanup_annotations` → FAILS `type/optParamCleanup`.
  3. In `def.rs`, run `level_mvar_to_param` on the VALUE as well → FAILS `err/levelMVarValue` (it would admit `lv.{u_1}`).
  4. In `header.rs`, `level_names.push(id)` instead of `insert(0, id)` → FAILS `univ/orderRev`. Record the outcome; if it survives, explain why in the commit body.
  5. In `def.rs`, `Regular(h)` instead of `Regular(h + 1)` → FAILS `height/pick`.
  6. In `header.rs`, skip the `view.ty.is_some()` header unassigned check → FAILS `err/defTypeHole`.
  7. In `def.rs`, the level fallback returns `Ok(())` → FAILS `err/levelMVarValue` (`lv` would reach the kernel). If the level info already catches it, record the mutation as unkilled-by-gate and add a unit test where no level info matches (for example, an `id`-headed term whose level mvar is created by a constant, not a binder).
  8. Make `unknown_ident_to_auto_bound_seam` the identity → FAILS `header_unknown_ident_is_the_auto_bound_seam`.
  9. In `commit`, `add_decl_in` without promoting names first (return `decl_name(d)` directly) → FAILS `oracle_decl_gate`, because the gate's `env.get(n)` misses a scratch id.

- [ ] **Step 10: Commit.**

```bash
git add crates/leanr_elab/src/command crates/leanr_elab/src/builtin crates/leanr_elab/tests/support/mod.rs \
  crates/leanr_elab/tests/oracle_decl.rs
git commit -m "leanr_elab: CommandElab + def/abbrev/opaque/example pipeline; oracle_decl gate (43 records)"
```

### Task 7: Theorems and Prop-typed headers

**Files:**
- Modify: `crates/leanr_elab/src/command/def.rs` (header conversion, async signature, Prop check, `Thm` build)
- Modify: `crates/leanr_elab/src/command/mod.rs` (route `DefKind::Theorem` to `def::elab_def`; delete its Task-7 seam)
- Modify: `crates/leanr_elab/tests/oracle_decl.rs` (`ENABLED` += 17 ids)

**Interfaces:**
- Consumes: Task 6's `elab_def`, `fix_level_params`, `with_level_names`, `level_mvar_to_param`.
- Produces (private to `def.rs`):
  - `fn level_mvar_to_param_headers(elab: &mut TermElabM, kind: DefKind, header: Header) -> Result<Header, ElabError>`
  - `fn check_async_signature(elab: &mut TermElabM, header: &Header) -> Result<(), ElabError>`
  - `fn is_prop_full(elab: &mut TermElabM, e: ExprId) -> Result<bool, ElabError>`

The oracle:
- **`levelMVarToParamHeaders`** (`MutualDef.lean:1148-1160`): for a theorem, OR when `isProp header.type`, under `withLevelNames header.levelNames`: `type := levelMVarToParam type` and `levelNames := getLevelNames` (the new `u_N` join the header's names). Then `instantiateMVars` every header.
- **The async test** (`:1239-1247`): `Elab.async && view.kind.isTheorem && !type.hasMVar` → `elabAsync`. Otherwise `elabSync`. The test runs AFTER the conversion, so only expression mvars block it.
- **`elabAsync`'s signature** (`:1275-1297`):
  - `type ← withLevelNames allUser (levelMVarToParam type)`, a no-op after the conversion, kept for fidelity;
  - `instantiateMVars`;
  - `collectLevelParams` over the TYPE ONLY;
  - `sortDeclLevelParams [] allUser used`, which raises the unused-universe error before the body;
  - `letToHave` on the type: a seam via `reject_let`.

  The body then runs `finishElab` as for a def, so the rest of the pipeline is shared.
- **`pushMain`** (`:1052-1053`): a theorem whose type is not a proposition → `TheoremTypeNotProp`. This runs after the values and headers are instantiated, before `levelMVarToParamTypesPreDecls`.
- **`Meta.isProp`** (`Meta/InferType.lean:323-332`): infer the type, `whnfD`, `Sort u` with `isAlwaysZero (instantiateLevelMVars u)` (`Level.lean:212-218`: `zero` → true, `max a b` → both, `imax _ b` → `b`, otherwise false). `MetaCtx::is_prop` narrows `isAlwaysZero` to a literal `zero`, which can miss `imax u 0` (the level of `∀ x, P` over a Prop body), so port the full test locally in `def.rs`. Do not change `leanr_meta`.
- **`addNonRecAux`'s theorem arm** (`PreDefinition/Basic.lean:189-195`): `thmDecl { name, levelParams, type, value, all }`.

- [ ] **Step 1: Enable the records (the failing test).** Append to `ENABLED` in `oracle_decl.rs`:

```rust
    // Task 7 — theorems and Prop-typed headers
    "kind/theorem", "kind/propDef", "kind/abbrevProp", "kind/opaqueProp",
    "univ/thmElevenNumeric", "univ/propDefElevenNumeric", "univ/thmSortHole",
    "univ/thmExplicit", "univ/thmUserAndHole", "univ/thmLevelOnlyBody",
    "err/thmAlready", "err/thmUnivValueOnly", "err/thmTypeNotProp", "err/propDefHeaderUniv",
    "err/thmHeaderUnivByBody", "err/thmTypeHole", "err/levelMVarThm",
```

- [ ] **Step 2: Run the gate to confirm it fails.**

Run: `cargo test -p leanr_elab --test oracle_decl oracle_decl_gate`
Expected: FAIL. The theorem records report `theorem — not yet ported (M4c-1 P2 Task 7)`, and `univ/propDefElevenNumeric` reports lexicographic level params.

- [ ] **Step 3: Implement.** In `command/mod.rs`, delete the `DefKind::Theorem` arm, so theorems fall through to `def::elab_def`. In `def.rs`:

(a) In `elab_def`, right after `let header = header::elab_header(...)?;`:

```rust
    let header = level_mvar_to_param_headers(elab, view.kind, header)?;
    // `Elab.async` is on, as on the `lean` command line (`CoreM.lean:35`):
    // a theorem whose header has no mvars takes `elabAsync`
    // (`MutualDef.lean:1239-1247`).
    let base = Some(elab.view.store);
    let d = elab.mctx.store().expr_data(base, header.ty);
    if view.kind == DefKind::Theorem && !d.has_expr_mvar() && !d.has_level_mvar() {
        check_async_signature(elab, &header)?;
    }
```

(b) In `elab_def`, after `let ty = elab.mctx.instantiate_mvars(header.ty)?;` and BEFORE the `level_mvar_to_param` on types:

```rust
    // `MutualClosure.pushMain` (`MutualDef.lean:1052-1053`).
    if view.kind == DefKind::Theorem && !is_prop_full(elab, ty)? {
        return Err(ElabError::TheoremTypeNotProp(id.short.clone()));
    }
```

(c) In `build_decl`, replace the `DefKind::Theorem | DefKind::Axiom` arm with:

```rust
        // `mkThmDecl` (`PreDefinition/Basic.lean:189-195`).
        DefKind::Theorem => Declaration::Thm(TheoremVal {
            val,
            value,
            all: vec![name],
        }),
        DefKind::Axiom => return Err(ElabError::Internal("build_decl: axiom".into())),
```

(add `TheoremVal` to the `leanr_kernel` import).

(d) Add the helpers:

```rust
/// oracle: `levelMVarToParamHeaders` (`MutualDef.lean:1148-1160`).
fn level_mvar_to_param_headers(
    elab: &mut TermElabM,
    kind: DefKind,
    mut header: Header,
) -> Result<Header, ElabError> {
    if kind == DefKind::Theorem || is_prop_full(elab, header.ty)? {
        let ty0 = header.ty;
        let (ty, names) = elab.with_level_names(header.level_names.clone(), |elab| {
            let ty = elab.level_mvar_to_param(ty0)?;
            Ok((ty, elab.level_names.clone()))
        })?;
        header.ty = ty;
        header.level_names = names;
    }
    header.ty = elab.mctx.instantiate_mvars(header.ty)?;
    Ok(header)
}

/// oracle: `elabAsync`'s committed signature (`MutualDef.lean:1281-1297`):
/// the level params come from the header TYPE alone, so a universe used
/// only in the proof is "unused" (probe: `theorem ta.{u} : True :=
/// (fun (_ : Sort u) => True.intro) PUnit.{u}`).
fn check_async_signature(elab: &mut TermElabM, header: &Header) -> Result<(), ElabError> {
    let ty0 = header.ty;
    let ty = elab.with_level_names(header.level_names.clone(), |elab| {
        elab.level_mvar_to_param(ty0)
    })?;
    let ty = elab.mctx.instantiate_mvars(ty)?;
    fix_level_params(elab, &[ty], &header.level_names)?;
    // `Meta.letToHave type` (`:1293-1296`): the letToHave seam.
    reject_let(elab, ty)
}

/// oracle: `Meta.isProp` (`Meta/InferType.lean:323-332`, the `inferType` +
/// `whnfD` path) with the full `isAlwaysZero` (`Level.lean:212-218`).
fn is_prop_full(elab: &mut TermElabM, e: ExprId) -> Result<bool, ElabError> {
    let ty = elab.mctx.infer_type(e)?;
    let ty = elab.mctx.whnf(ty)?;
    let ty = elab.mctx.instantiate_mvars(ty)?;
    let base = Some(elab.view.store);
    let Node::Sort { level } = elab.mctx.store().expr_node(base, ty) else {
        return Ok(false);
    };
    Ok(is_always_zero(elab, level))
}

fn is_always_zero(elab: &TermElabM, l: LevelId) -> bool {
    use leanr_kernel::bank::levels::LevelRow;
    match *elab.mctx.store().level_row(Some(elab.view.store), l) {
        LevelRow::Zero => true,
        LevelRow::Max(a, b) => is_always_zero(elab, a) && is_always_zero(elab, b),
        LevelRow::IMax(_, b) => is_always_zero(elab, b),
        _ => false,
    }
}
```

`elab.mctx.whnf` runs at the elaborator's transparency (`set_elab_config`: `.default`), which is `whnfD`. If the config's transparency differs, use whatever `MetaCtx` method gives default transparency and say so in the doc comment.

- [ ] **Step 4: Run the gate to confirm it passes.**

Run: `cargo test -p leanr_elab --test oracle_decl`
Expected: PASS (60 records).

- [ ] **Step 5: Run the mutations.** Each must FAIL `oracle_decl_gate` on the named record; then revert.
  1. Drop the `|| is_prop_full(...)` from the header conversion → `univ/propDefElevenNumeric` (lexicographic order) and `err/propDefHeaderUniv` (admitted instead of the application mismatch).
  2. Skip `check_async_signature` → `err/thmUnivValueOnly` (admitted with `[u]`).
  3. Pass `&[ty, value]`-style input to the async check (collect from the value too) → `err/thmUnivValueOnly`. This needs a small rewrite to thread the value in. If it is not practical, record mutation 2 as covering it.
  4. Drop the `pushMain` Prop check → `err/thmTypeNotProp` (the kernel rejects it, with no first line).
  5. Replace `is_prop_full` with `elab.mctx.is_prop` → record whether `univ/propDefElevenNumeric` FAILS. If it passes, leanr's `infer_type` already simplifies `imax u 0`. Record it as equivalent with that reason, and keep `is_prop_full` because it is the oracle's test.
  6. In `level_mvar_to_param_headers`, keep `header.level_names` unchanged (do not adopt `names`) → `univ/thmElevenNumeric` (lexicographic).

- [ ] **Step 6: Commit.**

```bash
git add crates/leanr_elab/src/command crates/leanr_elab/tests/oracle_decl.rs
git commit -m "leanr_elab: theorems and Prop headers (levelMVarToParamHeaders, async signature, pushMain Prop check)"
```

### Task 8: Nested-proof abstraction and aux commits

**Files:**
- Modify: `crates/leanr_elab/src/command/def.rs`
- Modify: `crates/leanr_elab/tests/oracle_decl.rs` (`ENABLED` += 13 ids)

**Interfaces:**
- Consumes: P1's `AuxLemmas::new(decl_name)`, `MetaCtx::abstract_nested_proofs(&mut AuxLemmas, ExprId)`, `AuxLemmas::into_pending()`.
- Produces: `elab_def` returns `Built::Add(aux… ++ [main])`.

The oracle: `addNonRecAux` → `abstractNestedProofs preDef` (`PreDefinition/Basic.lean:120-127`, `:180`). It is skipped for `theorem` and `example`, and runs under `withDeclNameForAuxNaming declName` (fresh `_proof_N`, index from 1). Each aux is `addDecl`'d immediately (`Meta/Tactic/AuxLemma.lean:43-73`), so it lands BEFORE the main declaration, and `getMaxHeight` sees the abstracted value (aux theorems contribute nothing). Amendment 1 items 2-4 hold:
- the per-declaration cache is observably identical to the env-wide one here;
- pending aux names count as "in env";
- a pending-aux lookup inside the walk is `MetaError::Unsupported` (a seam).

Map that to `ElabError::UnsupportedSyntax`, following `coe.rs`'s `mk_coe` precedent for `MetaError::Unsupported`.

- [ ] **Step 1: Enable the records.** Append to `ENABLED`:

```rust
    // Task 8 — abstractNestedProofs
    "np/one", "np/trivial", "np/shared", "np/distinct", "np/binder", "np/univ", "np/theorem",
    "np/example", "np/abbrev", "np/opaque", "np/twoBinders", "np/lambdaArg", "np/nestedTwice",
```

- [ ] **Step 2: Run the gate to confirm it fails.**

Run: `cargo test -p leanr_elab --test oracle_decl oracle_decl_gate`
Expected: FAIL. `np/one` and the other aux-minting records admit no `_proof_N` and get `regular 2` instead of `1`. `np/trivial`, `np/theorem` and `np/example` may already pass.

- [ ] **Step 3: Implement.** In `elab_def`, replace the tail (from `let decl = build_decl(...)` on) with:

```rust
    // `addNonRecAux` → `abstractNestedProofs` (`PreDefinition/Basic.lean:
    // 120-127`, `:180`): not for theorems or examples. The aux theorems are
    // committed BEFORE the main declaration, as the oracle's `mkAuxLemma`
    // has already `addDecl`'d them (`Meta/Tactic/AuxLemma.lean:43-73`).
    let mut aux = AuxLemmas::new(id.name);
    let value = if matches!(view.kind, DefKind::Theorem | DefKind::Example) {
        value
    } else {
        elab.mctx
            .abstract_nested_proofs(&mut aux, value)
            .map_err(|e| match e {
                // P1's named seams (Amendment 1 item 4), e.g. the pending-aux lookup.
                MetaError::Unsupported(m) => ElabError::UnsupportedSyntax(m),
                e => ElabError::Meta(e),
            })?
    };
    // `getMaxHeight` sees the abstracted value: aux theorems add nothing.
    let decl = build_decl(elab, view.kind, id.name, level_params, ty, value)?;
    if view.kind == DefKind::Example {
        return Ok(Built::Check(decl));
    }
    let mut decls = aux.into_pending();
    decls.push(decl);
    Ok(Built::Add(decls))
```

(import `leanr_meta::{AuxLemmas, MetaError}`). Update `elab_def`'s doc comment and the module doc to say the aux theorems come first.

- [ ] **Step 4: Run the gate to confirm it passes.**

Run: `cargo test -p leanr_elab --test oracle_decl`
Expected: PASS (73 records).

- [ ] **Step 5: Run the mutations.** Each must FAIL `oracle_decl_gate`; then revert.
  1. Push the main declaration BEFORE the aux theorems → `np/one` (`Kernel(UnknownConstant(np1._proof_1))`).
  2. Compute `build_decl` (the height) on the value from BEFORE abstraction → `np/one` (`regular 2`, since `rfl` is a regular-1 def in Elab0).
  3. Skip abstraction for `abbrev` → `np/abbrev`.
  4. Abstract `example` values too → `np/example` (its checked declaration references an aux that was never admitted, so the kernel rejects it).
  5. Abstract `theorem` values too → EQUIVALENT: a theorem's value is a proof, and `abstract_nested_proofs` returns a proof unchanged (`AbstractNestedProofs.lean:111-116`). Record it as equivalent.

- [ ] **Step 6: Commit.**

```bash
git add crates/leanr_elab/src/command/def.rs crates/leanr_elab/tests/oracle_decl.rs
git commit -m "leanr_elab: abstractNestedProofs in the def pipeline; aux theorems committed first"
```

### Task 9: `axiom`

**Files:**
- Create: `crates/leanr_elab/src/command/axiom.rs`
- Modify: `crates/leanr_elab/src/command/mod.rs` (route `DefKind::Axiom`; delete its Task-9 seam; `mod axiom;`)
- Modify: `crates/leanr_elab/tests/oracle_decl.rs` (`ENABLED` += 6 ids; one smoke test)

**Interfaces:**
- Consumes:
  - `header::{expand_decl_id, intern_atomic, unknown_ident_to_auto_bound_seam}`
  - `def::fix_level_params`
  - `builtin::binder::{extract_binder_group, push_binder_group, elab_type}`
- Produces: `pub(super) fn elab_axiom(elab: &mut TermElabM, view: &DefView, kinds: &KindInterner) -> Result<Built, ElabError>`.

The oracle: `elabAxiom` (`Elab/Declaration.lean:101-135`):
1. `expandDeclId`.
2. Under `withAutoBoundImplicit` and `withLevelNames allUserLevelNames`:
   - `elabBinders`;
   - `elabType typeStx`;
   - `synthesizeSyntheticMVarsNoPostponing`;
   - `instantiateMVars`;
   - `mkForallFVars xs`;
   - `mkForallFVars vars (usedOnly := true)` (no section variables in M4c-1);
   - `Term.levelMVarToParam type`, whose new names join the scoped level names only.
3. `collectLevelParams type`, then `sortDeclLevelParams scope allUserLevelNames used`. This uses the ORIGINAL user names, so leftover `u_N` sort lexicographically: `univ/axiomElevenLex`. An unused name raises `throwErrorAt`.
4. `instantiateMVars`, then `axiomDecl { …, isUnsafe := false }`.
5. `Term.ensureNoUnassignedMVars decl` (`TermElabM.lean:1041-1044`), then `addDecl`.

There is no `letToHave` and no abstraction for axioms. There is also no `registerFailedToInferDefTypeInfo`, so `axiom ahole : _` reports the plain hole: "don't know how to synthesize placeholder".

- [ ] **Step 1: Enable the records and add the smoke test.** Append to `ENABLED`:

```rust
    // Task 9 — axiom
    "kind/axiom", "univ/axiomSortHole", "univ/axiomElevenLex", "err/axiomUnusedUniv",
    "err/axiomBinderHole", "err/axiomTypeHole",
```

and add:

```rust
#[test]
fn axiom_header_unknown_ident_is_the_auto_bound_seam() {
    // `elabAxiom` also runs under `withAutoBoundImplicit` (`Declaration.lean:108`).
    let m = seam_message("axiom aa (a : α) : α");
    assert!(m.contains("auto-bound"), "{m}");
}
```

- [ ] **Step 2: Run them to confirm they fail.**

Run: `cargo test -p leanr_elab --test oracle_decl`
Expected: FAIL with `axiom — not yet ported (M4c-1 P2 Task 9)`.

- [ ] **Step 3: Implement `command/axiom.rs`.**

```rust
//! `axiom`: oracle `elabAxiom` (`Elab/Declaration.lean:101-135`).

use leanr_kernel::bank::ExprId;
use leanr_kernel::{AxiomVal, ConstantVal, Declaration};
use leanr_syntax::kind::KindInterner;

use super::def::fix_level_params;
use super::header::{expand_decl_id, unknown_ident_to_auto_bound_seam};
use super::view::DefView;
use super::Built;
use crate::builtin::binder::{elab_type, extract_binder_group, push_binder_group};
use crate::elab::TermElabM;
use crate::error::ElabError;

pub(super) fn elab_axiom(
    elab: &mut TermElabM,
    view: &DefView,
    kinds: &KindInterner,
) -> Result<Built, ElabError> {
    let id = expand_decl_id(elab, view)?;
    let ty_stx = view
        .ty
        .clone()
        .ok_or_else(|| ElabError::Internal("axiom without a type".into()))?;
    let ty: ExprId = elab
        .with_level_names(id.level_names.clone(), |elab| {
            let cp = elab.mctx.lctx_checkpoint();
            let out = (|| {
                let mut xs = Vec::new();
                for b in &view.binders {
                    let g = extract_binder_group(elab, b, kinds)?;
                    xs.extend(push_binder_group(elab, &g, kinds)?);
                }
                let ty = elab_type(elab, &ty_stx, kinds)?;
                elab.synthesize_synthetic_mvars_no_postponing(kinds)?;
                let ty = elab.mctx.instantiate_mvars(ty)?;
                let ty = elab.mctx.mk_forall(&xs, ty)?;
                // `Term.levelMVarToParam type` (`Declaration.lean:118`); the new
                // names extend only this scope's level names.
                elab.level_mvar_to_param(ty)
            })();
            elab.mctx.lctx_restore(cp);
            out
        })
        .map_err(unknown_ident_to_auto_bound_seam)?;
    // `sortDeclLevelParams scopeLevelNames allUserLevelNames usedParams`
    // (`:119-122`) against the ORIGINAL user names: leftovers sort
    // lexicographically.
    let level_params = fix_level_params(elab, &[ty], &id.level_names)?;
    let ty = elab.mctx.instantiate_mvars(ty)?;
    // `Term.ensureNoUnassignedMVars decl` (`:131`; `TermElabM.lean:1041-1044`).
    let pending = elab.get_mvars(ty)?;
    if let Some(e) = elab.log_unassigned_using_error_infos(&pending)? {
        return Err(e);
    }
    Ok(Built::Add(vec![Declaration::Axiom(AxiomVal {
        val: ConstantVal {
            name: id.name,
            level_params,
            ty,
        },
        is_unsafe: false,
    })]))
}
```

Verify the `Declaration.lean` line numbers in the comments against the pinned source. In `command/mod.rs`, add `mod axiom;` and route `DefKind::Axiom => axiom::elab_axiom(&mut elab, &view, kinds)`.

- [ ] **Step 4: Run the tests to confirm they pass.**

Run: `cargo test -p leanr_elab --test oracle_decl`
Expected: PASS (79 records plus the smoke tests).

- [ ] **Step 5: Run the mutations.** Each must FAIL the named test; then revert.
  1. Sort against the post-`levelMVarToParam` names (pass `elab.level_names` from inside the scope instead of `id.level_names`) → `univ/axiomElevenLex` (declaration order instead of lexicographic).
  2. Skip `ensureNoUnassignedMVars` → `err/axiomTypeHole` (the kernel rejects the mvar instead, with no first line).
  3. Drop the auto-bound mapping → `axiom_header_unknown_ident_is_the_auto_bound_seam`.

- [ ] **Step 6: Commit.**

```bash
git add crates/leanr_elab/src/command crates/leanr_elab/tests/oracle_decl.rs
git commit -m "leanr_elab: axiom (elabAxiom); oracle_decl gate covers the whole corpus"
```

### Task 10: Full gate, seam audit, docs, spec Landed

**Files:**
- Modify: `crates/leanr_elab/tests/oracle_decl.rs` (delete `ENABLED`; gate everything with the floor)
- Modify: `crates/leanr_elab/tests/seam_audit.rs` (end-to-end seam tests through `elab_decl`; retired-label gate)
- Modify: `crates/leanr_elab/src/lib.rs` (module doc: an M4c-1 bullet)
- Modify: `docs/superpowers/specs/2026-10-03-m4c1-single-decl-design.md` (`## Landed` → `### P2 (command elaborator)`)

**Interfaces:**
- Consumes: everything above. Produces no new API.

- [ ] **Step 1: Gate the whole corpus.** In `oracle_decl.rs`, delete `ENABLED` and replace `oracle_decl_gate` with:

```rust
#[test]
fn oracle_decl_gate() {
    let checked = support::run_decl_corpus("decl-queries.jsonl", |_| true);
    assert!(
        checked >= CORPUS_FLOOR,
        "decl corpus shrank: checked {checked}, floor {CORPUS_FLOOR}. Check \
         `dump_decls.lean`'s stderr for a dropped record, or lower the floor deliberately."
    );
}
```

Run: `cargo test -p leanr_elab --test oracle_decl`
Expected: PASS, with all 79 records checked.

- [ ] **Step 2: Add the end-to-end seam tests and the retired-label gate.** Append to `seam_audit.rs`:

```rust
/// M4c-1 P2: every declaration-level seam is reachable through
/// `CommandElab::elab_decl` as a named `UnsupportedSyntax`, never a panic
/// and never a wrong `Ok` (plan `2026-10-03-m4c1-p2-command-elab.md`
/// § Global Constraints). One source per seam family; `command/view.rs`'s
/// unit tests cover each `DefView` seam individually.
#[test]
fn declaration_seams_are_named_end_to_end() {
    let cases: &[(&str, &str)] = &[
        ("@[simp] def a : Nat := Nat.zero", "attributes"),
        ("private def a : Nat := Nat.zero", "visibility modifier"),
        ("def Foo.bar : Nat := Nat.zero", "M4c-2"),
        ("def sr : Nat := sr", "recursive reference"),
        ("def f : Nat → Nat\n  | n => n", "pattern-matching equations"),
        ("instance : Wrap Nat := ⟨fun x => x⟩", "declaration kind"),
        ("opaque o2 : Nat", "`opaque` without a value"),
        ("def sl : Nat := let x := Nat.zero; x", "letToHave"),
        ("def ab (a : α) : α := a", "auto-bound"),
        ("namespace Foo", "command loop"),
    ];
    for (src, needle) in cases {
        let got = support::with_command_elab(src, |ce, cmd, kinds| ce.elab_decl(cmd, kinds));
        match got {
            Err(leanr_elab::ElabError::UnsupportedSyntax(m)) => {
                assert!(m.contains(needle), "{src:?}: seam {m:?} lacks {needle:?}")
            }
            other => panic!("{src:?}: expected a named seam, got {other:?}"),
        }
    }
}

/// The plan's temporary task seams (`not yet ported (M4c-1 P2 Task N)`) must
/// all be gone once the plan lands.
#[test]
fn no_seam_points_at_an_m4c1_p2_task_label() {
    let src_dir = concat!(env!("CARGO_MANIFEST_DIR"), "/src");
    let needle = "not yet ported (M4c-1 P2 Task";
    let mut offenders = Vec::new();
    for path in walk_rs_files(src_dir) {
        let text = std::fs::read_to_string(&path).expect("readable source");
        for (n, line) in text.lines().enumerate() {
            if line.contains(needle) {
                offenders.push(format!("{}:{}", path.display(), n + 1));
            }
        }
    }
    assert!(offenders.is_empty(), "stale M4c-1 P2 task seam at {offenders:?}");
}
```

Run: `cargo test -p leanr_elab --test seam_audit`
Expected: PASS. Mutation: re-add a `"theorem — not yet ported (M4c-1 P2 Task 7)"` string anywhere in `src/`, confirm `no_seam_points_at_an_m4c1_p2_task_label` FAILS, then revert.

- [ ] **Step 3: Update the crate doc.** In `crates/leanr_elab/src/lib.rs`'s module doc, after the last slice bullet, add one in the same style:

```rust
//! - **M4c-1** — command elaboration of ONE non-recursive
//!   `def`/`theorem`/`abbrev`/`opaque`/`axiom`/`example`, in `command/`:
//!   `DefView` (syntax + named seams), header (`expandDeclId`,
//!   `elabHeaders`), body (`elabFunValues`), level params
//!   (`levelMVarToParam*`, `sortDeclLevelParams`), the unassigned-mvar
//!   report (`unassigned.rs`), `abstractNestedProofs`, and commit through
//!   `Environment::add_decl_in` (an `example` is only kernel-checked).
//!   Gated by `tests/oracle_decl.rs` over `decl-queries.jsonl`
//!   (docs/superpowers/specs/2026-10-03-m4c1-single-decl-design.md).
```

- [ ] **Step 4: Write the spec's Landed section.** Append to `docs/superpowers/specs/2026-10-03-m4c1-single-decl-design.md` under `## Landed`:

```markdown
### P2 (command elaborator)

Commits (`git log --oneline main..HEAD`): <paste the list>.

Mutation outcomes (from each commit body): <one line per task>.

Open seams carried forward:
- M4c-2: the command loop, namespaces/`protected`/dotted names, auto-bound implicits (header unknown identifier or universe), the env-wide `auxLemmasExt` cache (Amendment 1 item 2).
- later M4: recursion (self-reference), `declValEqns`/`where`/termination hints, attributes, modifiers, `deriving`, `instance`/`structure`/`inductive`, `opaque` without a value, `letToHave`, compilation, the parser's missing `binderDefault`.
- P1's pending-aux lookup seam (Amendment 1 item 4), now surfaced as `UnsupportedSyntax` by `def.rs`.
```

Fill the placeholders from `git log` and the commit bodies at the time you write it. They are filled at execution time, not left in.

- [ ] **Step 5: Run the full CI, blocking.**

Run: `mise run ci; echo CI_EXIT=$?`
Expected: `CI_EXIT=0` (fmt, clippy `-D warnings`, the whole workspace test suite). Fix anything red and re-run. Never background this.

- [ ] **Step 6: Run the citation sweep.** For every `oracle:`/`(`*.lean:N`)` citation added on this branch (`git diff main --stat` lists the files; `git diff main | grep -n '\.lean:[0-9]'`), open the cited line in the pinned toolchain and fix any drift, in code, plan and spec together. Record the corrections in the commit body.

- [ ] **Step 7: Commit.**

```bash
git add crates/leanr_elab/tests/oracle_decl.rs crates/leanr_elab/tests/seam_audit.rs crates/leanr_elab/src \
  docs/superpowers/specs/2026-10-03-m4c1-single-decl-design.md docs/superpowers/plans/2026-10-03-m4c1-p2-command-elab.md
git commit -m "M4c-1 P2: full oracle_decl gate (79 records), declaration seam audit, docs, spec Landed"
```

After this task: the whole-branch final review (superpowers:requesting-code-review), then the PR. Per the standing workflow, merge on green CI, verify, and delete the branch.
