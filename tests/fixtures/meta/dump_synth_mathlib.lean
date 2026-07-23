/- Sharded ORACLE metaprogram for the tier-2 nightly Mathlib DISCOVERY sweep
(M4a plan-4 spec, PR-C task C1). Sibling of `dump_synth.lean` (tier-1's
CURATED corpus): same canonical expr/level scheme, same encoders
(`biStr`/`encLevel`/`EncSt`/`encExpr`, copied VERBATIM below so all three
dumper files in this directory share one scheme by construction), same
hermetic-encoding discipline. What differs: instead of a hand-curated list
of ~15 queries, this file MINES `synthInstance` queries directly out of
REAL Mathlib declarations, sharded by constant index so a nightly workflow
can spread the sweep across parallel jobs (mirroring the existing
`parse:mathlib:shard` convention in spirit; see AGENTS.md's
"nightly-sweep.yml" section) — but PR-C's nightly is a SEPARATE workflow
with its own pass-list, never this repo's parse sweep (global constraint).

This file is NOT part of `meta:fast` and is never run by CI. It requires
the pinned Mathlib checkout on disk (`.mathlib/`, `mathlib-pin`) and a
sysroot Lean toolchain; run it only from the (future) nightly workflow or
by hand for local development.

═══════════════════════════════════════════════════════════════════════
ENV CONTRACT
═══════════════════════════════════════════════════════════════════════
  LEANR_SYNTH_SHARD = "I/N"   1-based shard index I, shard count N (1<=I<=N)
  LEANR_SYNTH_OUT   = <path>  where the JSONL output is written
  LEAN_PATH                   must resolve the pinned Mathlib build, e.g.
                              `LEAN_PATH="$(cd .mathlib && lake env printenv LEAN_PATH)"`

Malformed/missing env vars are a `throw (IO.userError ..)` in plain `IO`
BEFORE any Lean environment is touched — a genuine uncaught IO exception,
so `lean --run` exits non-zero (unlike `panic!`, see the FATAL-SHAPE
GUARDS section below).

═══════════════════════════════════════════════════════════════════════
RECORD SCHEMA
═══════════════════════════════════════════════════════════════════════
One JSON object per line. The common case (the oracle answered cleanly):
  { "const"      : <name>          -- rendered name of the mined constant
  , "id"         : "<const>/synth/<i>"  -- <i> is 0-based, PER CONSTANT,
                                        -- in telescope order (NOT global)
  , "goal"       : <E>             -- the synthesis goal type (canonical
                                        -- expr scheme; see `encExpr` below)
  , "ok"         : true|false      -- oracle verdict (`synthInstance?`)
  , "val"        : <E>             -- present iff ok; the instance TERM
  , "near_budget": true|false      -- see NEAR_BUDGET below
  }
This is exactly the 6-field shape task C1's brief specifies; there is no
`mvars` field (unlike `dump_synth.lean`'s curated corpus) because every
mined `goal` is constructed to be closed w.r.t. BOTH bound variables and
metavariables by the mining algorithm below — see MINING ALGORITHM and
FATAL-SHAPE GUARDS, which enforce that invariant rather than merely
assuming it.

NAMED SEAM — the `exc` record (owner: whoever writes C2's replay/diff
binary; cite this note + `oracle_synth.rs`'s `SEAM_EXCLUSIONS` handling of
`dump_synth.lean`'s `q:"exc"` records for precedent):
  { "const":<name>, "id":<id>, "goal":<E>, "exc":<message> }
`dump_synth.lean`'s header explains why an exception escaping the oracle
call must NEVER be conflated with `ok:false` — an honest "no instance" is
`none` from `synthInstance?`, not a thrown exception. Task C1's literal
6-field schema (`const`/`id`/`goal`/`ok`/`val`/`near_budget`) has no field
for this case, but at Mathlib scale (thousands of mined queries per
shard, drawn from declarations nobody curated for niceness) hitting an
exception — most likely a heartbeat-budget exceeded under the per-query
reset described in NEAR_BUDGET below, but in principle any other escaping
`Exception` too — is a real, nonzero-probability outcome, not a
theoretical one as it is for the tiny curated tier-1 corpus. This record
shape is therefore a deliberate, minimal extension of the brief's schema:
distinguishable from an ordinary record by the presence of the `exc` key
and the ABSENCE of `ok`. C2 must skip these from the gate, exactly as
`oracle_synth.rs` skips `q:"exc"` — a query the oracle itself could not
answer cleanly is not part of any regression gate.

═══════════════════════════════════════════════════════════════════════
SORT KEY + SHARD STRIDE — C2 MUST MIRROR THIS EXACTLY
═══════════════════════════════════════════════════════════════════════
After importing the pinned module set below, take EVERY constant in
`(← getEnv).constants` (no filtering — core/Std/Batteries constants
transitively present in the Mathlib closure are included, exactly as
`dump_synth.lean`'s `Synth0` environment includes its own transitively
generated scaffold; this is "the environment", not "constants literally
declared under the `Mathlib.` namespace"). Render each constant's `Name`
via `n.toString (escape := false)` (the SAME rendering `encExpr`'s
`const`/`proj` cases and every other dumper in this directory already
use). Sort the list of (renderedName, constant) pairs ASCENDING by
`renderedName`, using Lean's default `String` order — `String.lt` is
`List Char` lexicographic order by `Char` codepoint
(`Init/Data/String/Basic.lean`), i.e. plain Unicode-codepoint order on the
rendered string. Number the sorted list 0-based: `idx`. A shard `I/N`
(1-based `I`, `1 <= I <= N`) selects exactly the constants with
  idx % N == I - 1
— a STRIDE, not a chunk (matching `mathlib_sweep.rs`'s own
`parse_shard_spec`/stride convention, chosen there so neighbours of
similar cost are dealt out round-robin rather than left in one shard).

C2's mirror obligation, spelled out: render each `leanr_kernel::Name` the
SAME way Lean's `toString (escape := false)` would (this repo's `Name`
rendering must already agree — it is exercised against real `.olean`
names throughout `leanr_olean`); sort the resulting `Vec<String>`
(or equivalent) using Rust's DEFAULT `Ord` for `String`/`str`. That default
is byte-wise UTF-8 comparison, which is PROVABLY identical to Lean's
codepoint-wise comparison for any valid UTF-8 string, because UTF-8's
encoding is monotonic in codepoint value under byte-wise comparison (no
extra normalization needed on either side). Apply the identical
`idx % N == I - 1` test with the SAME 1-based `I`. If C2 ever needs a
tie-break (two DISTINCT `Name`s rendering to the identical string — not
expected for real top-level Mathlib/Std declaration names, since the
elaborator's own redeclaration checking is string-based at that level),
none is defined here; that is an unresolved, believed-vacuous seam, not a
silent behavior — flag it loudly on the Rust side if `idx` assignment is
ever found to depend on a tie.

═══════════════════════════════════════════════════════════════════════
MINING ALGORITHM (per constant, in telescope order)
═══════════════════════════════════════════════════════════════════════
For a constant `c` with type `T` (a `∀`-telescope followed by some
non-`forallE` head), walk the telescope LEFT TO RIGHT, introducing one
binder at a time as a free variable via `Lean.Meta.withLocalDecl name bi d
fun fvar => ...` (see `mineFromType` below). This is a manual,
single-binder-at-a-time telescope walk rather than `Lean.Meta.
forallTelescope`, DELIBERATELY: `Lean.Meta.Basic.forallTelescope`'s
non-`maxFVars`-bounded path (confirmed by reading
`forallTelescopeReducingAuxAux`/`withNewLocalInstancesImp` in the pinned
toolchain's `Lean/Meta/Basic.lean`) introduces EVERY fvar in the WHOLE
telescope into the local context FIRST, and only registers local
instances for ALL of them in one batch immediately before running the
continuation. That would let a mined goal at position `i` see fvars
introduced at positions `> i` as candidate local instances — an
impossible resolution path in the real declaration (a binder's type can
only mention EARLIER binders; a term elaborated for position `i` can
never reference a variable bound strictly later in the same telescope),
so using batched `forallTelescope` here could manufacture a "successful"
synthesis that Lean's own elaborator could never have produced at that
call site. `Lean.Meta.withLocalDecl` (confirmed via `withLocalDeclImp`/
`withNewFVar` in the same file) does not have this problem: it calls
`isClass?` on EACH binder's type INCREMENTALLY, the moment that one fvar
is introduced, and registers it as a local instance immediately — which
is exactly how the real elaborator processes a declaration's signature
binder-by-binder (`Lean.Elab.Term.elabBinders` and friends). Using
`withLocalDecl` one binder at a time therefore reproduces the real
scoping discipline: by the time we reach binder `i`, exactly the
INSTANCE-typed binders at positions `< i` are available as local
instances, never any at positions `>= i`.

At each binder position `i` (0-based) whose `BinderInfo` is
`instImplicit`, the binder's domain type `d` — already free of loose
bound variables, because it is read off the ALREADY-SUBSTITUTED telescope
tail threaded in from the recursion (see `mineFromType`'s use of
`Expr.instantiate1`) — is emitted as a mined goal. `withLocalDecl` then
introduces this binder's own fvar and (per the paragraph above)
AUTOMATICALLY registers it as a local instance before the walk continues
into the rest of the telescope, regardless of what verdict THIS mining
step's own `synthInstance?` call reaches for it: subsequent positions in
the SAME constant must see the REAL local instance the actual declaration
has, not a re-derived one, exactly like the real elaborator.

This mines both "boring" negative records (an abstract, unconstrained
type variable's instance requirement, which no candidate can satisfy —
still a legitimate oracle answer) and meaningful positive records where a
LATER instance argument is derivable from an EARLIER one via a superclass
projection (the real-world analogue of `dump_synth.lean`'s curated
`superclass`/`chain` queries, but sourced from Mathlib's actual instance
graph instead of a hand-built one).

═══════════════════════════════════════════════════════════════════════
NEAR_BUDGET
═══════════════════════════════════════════════════════════════════════
Identical formula to `dump_synth.lean`: for one query, `hb0`/`hb1` bracket
the `synthInstance?` call via `IO.getNumHeartbeats`, and `near_budget :=
(hb1 - hb0) * 100 > maxHb * nearBudgetPercent` (`nearBudgetPercent := 20`,
`maxHb` = the ambient `Core.Context.maxHeartbeats`, i.e. the toolchain's
registered `maxHeartbeats` OPTION default — never overridden here, same
as `dump_synth.lean`'s `coreCtx`). This is the ORACLE's own margin against
ITS budget (leanr counts a deterministic step counter instead, per the
global constraint, so the two budgets are not comparable — see
`dump_synth.lean`'s header for the full rationale); C2 excludes any
`near_budget:true` record from its gate.

DEVIATION from `dump_synth.lean`, cited: each mined query runs under
`Lean.Core.withCurrHeartbeats` (`Lean/CoreM.lean`, confirmed present in
the pinned toolchain), which resets the heartbeat BASELINE for the
enclosed computation. `dump_synth.lean`'s 15-query curated corpus never
needed this — heartbeats accumulate over the WHOLE `CoreM` run, and 15
tiny queries never approach `maxHeartbeats`. A Mathlib-scale mined corpus
can have thousands of queries per shard; without a per-query reset,
cumulative heartbeats would eventually exceed `maxHeartbeats` on some
UNRELATED later query and abort the entire shard with a heartbeat
exception, which is not what "near_budget flags one query" is supposed to
mean. Resetting per query keeps `near_budget`'s meaning exactly what
`dump_synth.lean`'s header already says it is ("heartbeats consumed by
THIS SINGLE `synthInstance?` call"), and keeps one slow/divergent query
from taking down the rest of the shard's output.

═══════════════════════════════════════════════════════════════════════
FATAL-SHAPE GUARDS — panic! is NOT fatal under `lean --run`
═══════════════════════════════════════════════════════════════════════
`panic!` in Lean, evaluated in most monads (including the pure `Id`/plain
value context `encLevel`/`encExpr` run in via `EncM = StateM EncSt`),
prints to stderr and returns the `Inhabited` `default` — it does NOT throw
a Lean `Exception`, so `lean --run` still exits 0 and nothing downstream
sees anything wrong until it silently misinterprets whatever default
value came out. That is fine for `dump_synth.lean`'s tiny curated corpus
(the panicking branches there are argued, per-query, to be unreachable),
but is NOT an acceptable risk for a corpus mined from thousands of
uncurated real declarations: hitting one of those branches here would
corrupt the oracle corpus the entire nightly sweep diffs against, with no
signal that anything went wrong. `encLevel`/`encExpr`/`EncSt`/`biStr`
below are reused VERBATIM from `dump_synth.lean` (including their
existing internal `panic!` branches) precisely so this file shares the
byte-identical canonical scheme with the other two dumpers — changing
their types to thread a `throwError`-capable monad would break that
invariant for a one-off gain. Instead, the call sites below (in `main`)
add an explicit, `throwError`-based (genuinely fatal: `MetaM`'s
`Exception` DOES propagate through `.toIO`, unlike `panic!`) precondition
check IMMEDIATELY BEFORE handing an expression to `encExpr`:
  * every mined `goal` must satisfy `!e.hasLooseBVars && !e.hasMVar`
    (closed by construction per MINING ALGORITHM above; this re-verifies
    the invariant rather than merely assuming it forever holds under
    future changes to the mining walk or to Lean's binder semantics);
  * every returned `val` (after `instantiateMVars`) must satisfy
    `!e.hasMVar` — a real risk `dump_synth.lean` does not face: a
    universe-polymorphic instance whose LEVEL parameter is unconstrained
    by the mined goal could come back from `synthInstance?` with that
    level metavariable still unassigned (no "generalize leftover
    universes" defaulting pass runs during a raw `synthInstance?` call,
    unlike at the end of elaborating a real `def`/`theorem`). Silently
    encoding such a `val` would not hit `encLevel`'s `panic!` at all —
    `encExpr`'s `.mvar` case just numbers it like any other node — but
    since this schema (unlike `dump_synth.lean`'s) carries no `mvars`
    field, the emitted record would reference an unexplained mvar index
    C2 could never replay correctly. Catching it here and failing loudly
    turns that "silently wrong record" failure mode into a hard, visible
    one instead.
Any malformed env var, or a violation of either guard above, is a
`throwError`/`IO.userError` — never a `panic!` — so it is genuinely fatal.
-/
-- NOT `import Synth0`/`import Meta0`: this file needs the real `Init` for
-- the `Lean`/`Lean.Meta` API (same reason `dump_synth.lean`/
-- `dump_defeq.lean` import `Lean` directly). The QUERY environment (the
-- pinned Mathlib module set) is loaded purely at RUNTIME via
-- `importModules` in `main` below.
import Lean
open Lean Lean.Meta

-- ===== canonical expr/level encoder (verbatim from dump_synth.lean, which
-- copies it verbatim from dump_defeq.lean — see that file's header for the
-- authoritative statement of every canonicalization rule) =====

/-- `default`->d, `implicit`->i, `strictImplicit`->s, `instImplicit`->c
(binder NAMES are erased everywhere; only this kind letter survives). -/
def biStr : BinderInfo → String
  | .default => "d"
  | .implicit => "i"
  | .strictImplicit => "s"
  | .instImplicit => "c"

/-- Levels never carry mvars in a fully-elaborated corpus — the canonical
scheme has no `lmvar` case, so an actual `Level.mvar` here would be a real
gap; fail loudly rather than silently emit a wrong-but-well-formed record.
(For THIS file, the `main` loop below additionally guards every `goal`/
`val` for `hasMVar` before it ever reaches this function — see this file's
header, FATAL-SHAPE GUARDS — so this branch is expected truly unreachable,
not merely argued so per-query as in `dump_synth.lean`.) -/
partial def encLevel : Level → Json
  | .zero => Json.mkObj [("k", "zero")]
  | .succ u => Json.mkObj [("k", "succ"), ("u", encLevel u)]
  | .max a b => Json.mkObj [("k", "max"), ("a", encLevel a), ("b", encLevel b)]
  | .imax a b => Json.mkObj [("k", "imax"), ("a", encLevel a), ("b", encLevel b)]
  | .param n => Json.mkObj [("k", "param"), ("n", n.toString (escape := false))]
  | .mvar _ => panic! "dump_synth_mathlib: unexpected Level.mvar (not in the canonical scheme)"

/-- Per-record numbering state for fvars, first-occurrence order. Threaded
across ONE record's `goal` -> `val` encodes, so an fvar referenced in both
gets one stable number. (No `mvars` map is exercised in practice — every
mined `goal`/`val` is guarded `!hasMVar` before reaching `encExpr` — but
the field stays, matching `dump_synth.lean`'s `EncSt` verbatim, both for
byte-identical reuse and because `encExpr`'s `.mvar` case still needs
SOMEWHERE to number into if a guard were ever loosened.) -/
structure EncSt where
  fvars : Std.HashMap FVarId Nat := {}
  fNext : Nat := 0
  mvars : Std.HashMap MVarId Nat := {}
  mNext : Nat := 0

abbrev EncM := StateM EncSt

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
  | .sort u => pure <| Json.mkObj [("k", "sort"), ("u", encLevel u)]
  | .const n us =>
    pure <| Json.mkObj
      [("k", "const"), ("n", n.toString (escape := false)),
       ("us", Json.arr (us.map encLevel).toArray)]
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

-- ===== pinned Mathlib module set (import order is PINNED — see header) =====

/-- Explicit, order-pinned module list — NOT a single `import Mathlib`
umbrella. Two reasons: (1) the global constraint ("Nightly pins import
order explicitly") and the design's risk-3 discussion both call for an
explicit list rather than relying on however `Mathlib.lean` happens to
order its transitive re-exports upstream (that ordering is not this
project's to pin, and PR-A/PR-B's decoded instance/default-instance
extensions are themselves order-sensitive structures); (2) a fixed,
named, moderately-sized set keeps a single shard's wall-clock cost
legible and gives this v1 corpus explicit boundaries to expand from,
rather than committing on day one to sweeping literally every Mathlib
module (~8.3k files) every night.

Chosen for BREADTH across the areas of the library most likely to
exercise interesting instance graphs (superclass chains, diamonds,
parametrized/derived instances): core algebra (group/ring/field),
order, foundational data types (Nat/Int/Rat/Real), topology, linear
algebra, category theory, and ring theory. All twenty are confirmed to
exist in the pinned checkout (`.mathlib`, commit `c732b96d0…` per
`mathlib-pin`).

NAMED SEAM (owner: PR-C follow-up / whoever schedules the nightly
workflow): expanding this list — up to the limit of `import Mathlib`
itself — is deferred, gated only by nightly wall-clock budget, not by
anything structural in this file; the sharding/mining machinery below
does not change shape as this list grows. -/
def pinnedModules : Array Name :=
  #[ `Mathlib.Algebra.Group.Defs
   , `Mathlib.Algebra.Group.Basic
   , `Mathlib.Algebra.Group.Subgroup.Defs
   , `Mathlib.Algebra.Order.Group.Defs
   , `Mathlib.Algebra.Order.Ring.Defs
   , `Mathlib.Algebra.Ring.Defs
   , `Mathlib.Algebra.Field.Defs
   , `Mathlib.Algebra.Field.Basic
   , `Mathlib.Data.Nat.Basic
   , `Mathlib.Data.Int.Basic
   , `Mathlib.Data.Rat.Defs
   , `Mathlib.Data.Real.Basic
   , `Mathlib.Order.Basic
   , `Mathlib.Order.Lattice
   , `Mathlib.Topology.Basic
   , `Mathlib.Topology.MetricSpace.Basic
   , `Mathlib.LinearAlgebra.Finsupp.Span
   , `Mathlib.Analysis.SpecialFunctions.Pow.Real
   , `Mathlib.CategoryTheory.Category.Basic
   , `Mathlib.RingTheory.Ideal.Basic
   ]

-- ===== shard spec =====

/-- 1-based shard index `i` of `n` total shards, `1 <= i <= n`. -/
structure ShardSpec where
  i : Nat
  n : Nat

/-- Parses `"I/N"`. Mirrors `mathlib_sweep.rs`'s `parse_shard_spec`
validation exactly (same error shape, same 1-based bounds) so the two
sharding conventions read as one scheme even though this is the synthesis
sweep's own independent shard spec, never the parse sweep's. -/
def parseShardSpec (raw : String) : Except String ShardSpec := do
  let parts := raw.splitOn "/"
  let (iRaw, nRaw) ← match parts with
    | [a, b] => pure (a, b)
    | _ => throw s!"expected the form I/N (1-based), e.g. 3/12, got {raw.quote}"
  let i ← match iRaw.toNat? with
    | some v => pure v
    | none => throw s!"shard index {iRaw.quote} is not a non-negative integer"
  let n ← match nRaw.toNat? with
    | some v => pure v
    | none => throw s!"shard count {nRaw.quote} is not a non-negative integer"
  if n == 0 then throw "shard count N must be >= 1"
  if i == 0 || i > n then throw s!"shard index I must be in 1..={n} (1-based), got {i}"
  pure { i, n }

-- ===== instance-argument mining (see header, MINING ALGORITHM) =====

/-- Walk `ty`'s `∀`-telescope left to right via `withLocalDecl` (one
binder at a time — see header for why not `forallTelescope`), invoking
`onGoal i d` for every `instImplicit` binder's (already bvar-free) domain
type `d` (`i` is the 0-based, per-constant instance-position index).

CRITICAL, TWO empirically-found ordering bugs this shape avoids (both
caught during this task's smoke test — see the report):

1. `onGoal` must be called from INSIDE the ancestor chain of
   `withLocalDecl` calls for the EARLIER binders, NEVER after
   `mineFromType` returns. `withLocalDecl`'s own doc comment says it
   reverts the local context once its continuation returns — so an
   `Expr` mentioning one of its fvars is only well-formed (lookups like
   `synthInstance?`'s own `inferType` on that fvar only succeed) WHILE
   still nested inside that continuation. Collecting mined goals into a
   returned `Array Expr` and processing them in a SEPARATE loop after
   `mineFromType` returns hands `synthInstance?` a goal mentioning an
   fvar the ambient local context no longer contains — an "unknown free
   variable" failure.

2. `onGoal idx d` must run BEFORE `withLocalDecl` introduces THIS
   binder's OWN fvar, not from inside its continuation. `withLocalDecl`
   (via `withLocalDeclImp`/`withNewFVar`, confirmed in the pinned
   toolchain's `Lean/Meta/Basic.lean`) registers the NEW fvar as a local
   instance and ONLY THEN invokes the continuation — so calling `onGoal`
   from inside that continuation would let the search trivially resolve
   the goal to the binder's OWN, not-yet-really-introduced fvar (`d`
   itself never mentions it — `d` is the ALREADY-SUBSTITUTED domain of
   the forall currently being destructured, closed over strictly EARLIER
   binders only per the recursion invariant below — but the AMBIENT
   local-instance list would contain it regardless, and `synthInstance?`
   doesn't care whether a candidate is "meant" to be in scope yet). The
   real elaborator never has this problem because a binder's own type is
   fully elaborated BEFORE that binder exists as a local hypothesis; this
   walk must reproduce that ordering explicitly since `withLocalDecl`
   bundles registration together with introduction. Mining every
   position of every constant in the smoke test's truncated run came
   back 100% `ok:true` with `val` a bare self-referential fvar before
   this fix — the giveaway that something was structurally wrong. -/
partial def mineFromType (ty : Expr) (onGoal : Nat → Expr → MetaM Unit) : MetaM Unit := do
  let rec go (ty : Expr) (idx : Nat) : MetaM Nat := do
    match ty with
    | .mdata _ e => go e idx -- mdata ERASED, matching encExpr's own rule
    | .forallE n d b bi => do
      -- `d` is already bvar-free here (closed over strictly earlier
      -- binders only — see the recursion's `instantiate1` below), so the
      -- query needs no fvar of its OWN to be introduced yet.
      if bi.isInstImplicit then
        onGoal idx d
      withLocalDecl n bi d fun fvar =>
        go (b.instantiate1 fvar) (if bi.isInstImplicit then idx + 1 else idx)
    | _ => pure idx
  discard <| go ty 0

-- ===== main =====

/-- Anything over this fraction (in percent) of the oracle's
`maxHeartbeats` marks the record `near_budget` — identical constant and
meaning to `dump_synth.lean`'s `nearBudgetPercent`. -/
def nearBudgetPercent : Nat := 20

unsafe def main : IO Unit := do
  let shardRaw ← match (← IO.getEnv "LEANR_SYNTH_SHARD") with
    | some v => pure v
    | none => throw <| IO.userError "LEANR_SYNTH_SHARD is required, e.g. LEANR_SYNTH_SHARD=3/12"
  let spec ← match parseShardSpec shardRaw with
    | .ok s => pure s
    | .error e => throw <| IO.userError s!"LEANR_SYNTH_SHARD={shardRaw.quote} is malformed: {e}"
  let outPath ← match (← IO.getEnv "LEANR_SYNTH_OUT") with
    | some v => pure v
    | none => throw <| IO.userError "LEANR_SYNTH_OUT is required, e.g. LEANR_SYNTH_OUT=/tmp/shard.jsonl"
  -- Must run before any `importModules (loadExts := true)` or the import
  -- throws internally (same pitfall dump_synth.lean/dump_defeq.lean
  -- document).
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  -- `loadExts := true` is REQUIRED: `instanceExtension`/
  -- `defaultInstanceExtension` ARE the tables synthesis reads. Without it
  -- every mined query below would report "no instance".
  let env ← Lean.importModules (pinnedModules.map (fun m => { module := m })) {}
    (trustLevel := 0) (loadExts := true)
  let coreCtx : Core.Context := { fileName := "<dump_synth_mathlib>", fileMap := default }
  let coreState : Core.State := { env }
  IO.FS.withFile outPath IO.FS.Mode.write fun h => do
    let go : MetaM Unit := do
      let maxHb := (← readThe Core.Context).maxHeartbeats
      -- ===== SORT KEY + SHARD STRIDE — see header for the exact contract
      -- C2 must mirror. =====
      let named : Array (String × Name) :=
        env.constants.fold (fun acc n _ => acc.push (n.toString (escape := false), n)) #[]
      let sorted := named.qsort (fun a b => a.1 < b.1)
      -- `Array.zipIdx` pairs `(elem, idx)` — NOT `(idx, elem)` — 0-based.
      let shardConsts : Array Name :=
        sorted.zipIdx.filterMap
          (fun ((_, n), idx) => if idx % spec.n == spec.i - 1 then some n else none)
      for cName in shardConsts do
        let some cinfo := env.find? cName
          | throwError "dump_synth_mathlib: constant {cName} vanished from the environment \
              between sorting and lookup — should be impossible for an immutable `Environment`"
        mineFromType cinfo.type fun i goal => do
          -- FATAL-SHAPE GUARD (goal): see header, closed by construction —
          -- re-verify rather than assume.
          if goal.hasLooseBVars || goal.hasMVar then
            throwError "dump_synth_mathlib: mined goal for {cName} position {i} is not closed \
                (hasLooseBVars={goal.hasLooseBVars}, hasMVar={goal.hasMVar}) — the telescope walk's \
                bvar-free invariant was violated; this is a hard bug, not an encodable record"
          let id := s!"{cName.toString (escape := false)}/synth/{i}"
          let hb0 ← IO.getNumHeartbeats
          let r : Except String (Option Expr) ←
            withCurrHeartbeats (do
              try
                Except.ok <$> Meta.synthInstance? goal
              catch ex => Except.error <$> ex.toMessageData.toString)
          let hb1 ← IO.getNumHeartbeats
          match r with
          | Except.error msg =>
            -- NAMED SEAM: see header, "the `exc` record". Not part of the
            -- gate — a query the oracle itself could not answer cleanly.
            let (goalJ, _) := (encExpr goal).run {}
            h.putStrLn <| Json.compress <| Json.mkObj
              [("const", Json.str (cName.toString (escape := false))), ("id", Json.str id),
               ("goal", goalJ), ("exc", Json.str msg)]
          | Except.ok val? =>
            let val? ← val?.mapM instantiateMVars
            -- FATAL-SHAPE GUARD (val): see header — an unassigned leftover
            -- universe/level mvar in the witness term would otherwise be
            -- silently mis-encoded as an unexplained `mvar` node (this
            -- schema carries no `mvars` field to declare it against).
            match val? with
            | some v =>
              if v.hasMVar then
                throwError "dump_synth_mathlib: instance term for {cName} position {i} still \
                    has an mvar after instantiateMVars — likely an unconstrained universe \
                    parameter left unassigned by a raw synthInstance? call (see header, \
                    FATAL-SHAPE GUARDS); this schema has no `mvars` field to declare it against, \
                    so it cannot be honestly encoded"
            | none => pure ()
            let nearBudget := maxHb != 0 && (hb1 - hb0) * 100 > maxHb * nearBudgetPercent
            let (goalJ, st0) := (encExpr goal).run {}
            let fields :=
              [("const", Json.str (cName.toString (escape := false))), ("id", Json.str id),
               ("goal", goalJ), ("ok", Json.bool val?.isSome)]
              ++ (match val? with
                  | some v => [("val", (encExpr v).run' st0)]
                  | none => [])
              ++ [("near_budget", Json.bool nearBudget)]
            h.putStrLn <| Json.compress <| Json.mkObj fields
    discard <| go.toIO coreCtx coreState
