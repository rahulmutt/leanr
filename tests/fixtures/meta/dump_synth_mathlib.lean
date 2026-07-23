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

TWO independent miners feed the same per-constant loop (see MINING
ALGORITHM below for both): (1) the original BINDER miner, which mines
each constant's own `instImplicit` telescope positions (its HYPOTHESES —
what a caller must supply); (2) an APPLICATION-SITE miner (added in the
fix round documented at the bottom of this header), which walks each
constant's `.type` AND `.value?` for `.app` spines whose callee has
instance-implicit parameter positions, and mines the (already-saturated,
concrete) argument found there (a DEMAND the constant itself makes on the
instance graph, at a call site where the real elaborator already solved
it once). Both feed the identical oracle-query/encode/near_budget
pipeline (`runQuery` below); records carry a `"src":"binder"|"app"` field
so C2 — and a human — can always tell which miner produced which record
(see RECORD SCHEMA).

This file is NOT part of `meta:fast` and is never run by CI. It requires
the pinned Mathlib checkout on disk (`.mathlib/`, `mathlib-pin`) and a
sysroot Lean toolchain; run it only from the (future) nightly workflow or
by hand for local development.

═══════════════════════════════════════════════════════════════════════
FIX ROUND 1 (post opus-review) — summary, see the report for detail
═══════════════════════════════════════════════════════════════════════
C1 (CRITICAL, heartbeat exhaustion): the original per-QUERY
`withCurrHeartbeats` (wrapping only each `synthInstance?` call) left the
TELESCOPE WALK itself (`withLocalDecl`'s incremental `isClass?` → `whnf`
→ `checkSystem "whnf"`) running under the run-wide heartbeat baseline, so
heartbeats accumulated monotonically across the WHOLE shard and it died
partway through with a heartbeat-exceeded exception — producing a
syntactically-valid but SILENTLY TRUNCATED JSONL, exactly the corruption
class this file is supposed to guard against, via a different door than
`panic!`. Fixed by moving the reset UP to wrap the WHOLE per-constant body
(mining + every query for that constant), so heartbeats reset at each new
constant rather than accumulating shard-wide; the original per-query reset
is KEPT NESTED inside (see `runQuery`) so one runaway query still can't eat
the rest of that same constant's budget. A completion SENTINEL line (see
RECORD SCHEMA) is now written as the last line of the file so C2 can
positively confirm the shard ran to completion rather than trusting exit
status alone (the whole point of C1 is that a truncation is otherwise
indistinguishable from a complete run by grepping the JSONL). As a second,
belt-and-suspenders layer against the SAME failure mode recurring on some
future pathological constant (the app-site miner below walks `.value?`
too, which can be large auto-generated proof terms), each constant's
ENTIRE body (both miners, all their queries) also runs under a `try`
that soft-catches any exception NOT recognizably one of this file's own
FATAL-SHAPE GUARDS (see below — distinguished by message prefix) and
emits a single `{"src":"const","exc":...}` record for that constant
instead of aborting the shard; guard violations still re-throw and remain
genuinely fatal, unchanged.

I1 (near_budget computed against the wrong limit): `near_budget` compared
elapsed heartbeats against the ambient `maxHeartbeats` option (~200M
scaled) but `synthInstance?` internally enforces its OWN, separate,
FIVE-TIMES-SMALLER budget via `synthInstance.maxHeartbeats` (default
20000 → 20M scaled, confirmed at `Lean/Meta/SynthInstance.lean:20-23`,
enforced through a private `SynthInstance.Context.maxHeartbeats` field,
never the ambient `Core.Context.maxHeartbeats`) — so the old 20%
threshold (40M) could never be reached and `near_budget` was inert (0/N
in the original shard-1/12 run). Fixed: `near_budget` now compares against
`synthInstance.maxHeartbeats.get (← getOptions) * 1000`.

M3: both miners now additionally filter a candidate `instImplicit`
domain/argument type through `isClass?` before ever handing it to
`synthInstance?`, so the `exc` seam stays reserved for genuine oracle
failures (a non-class `instImplicit` binder, e.g. an abstract `[inst : α]`
pattern some Mathlib declarations use, otherwise reliably produces
`synthInstance?`'s own "type class instance expected" exception — real,
observed once in the original shard-1/12 run, not hypothetical).

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
  , "id"         : <id>            -- see ID SCHEME below
  , "src"        : "binder"|"app"  -- which miner produced this record
  , "goal"       : <E>             -- the synthesis goal type (canonical
                                        -- expr scheme; see `encExpr` below)
  , "ok"         : true|false      -- oracle verdict (`synthInstance?`)
  , "val"        : <E>             -- present iff ok; the instance TERM
  , "near_budget": true|false      -- see NEAR_BUDGET below
  }
This is task C1's original 6-field shape (`const`/`id`/`goal`/`ok`/`val`/
`near_budget`) plus the one field the fix round added, `src` (see below);
there is still no `mvars` field (unlike `dump_synth.lean`'s curated
corpus) because every mined `goal` is constructed to be closed w.r.t.
BOTH bound variables and metavariables by the mining algorithm below —
see MINING ALGORITHM and FATAL-SHAPE GUARDS, which enforce that invariant
rather than merely assuming it.

ID SCHEME (both miners are per-constant, 0-based, in each miner's own
discovery order — NOT a global index):
  "<const>/synth/<i>"     -- BINDER miner: <i> is the 0-based position of
                              this `instImplicit` binder in `c`'s own
                              `∀`-telescope (gaps possible since M3 skips
                              non-class positions without consuming an id)
  "<const>/synthapp/<i>"  -- APP-SITE miner: <i> is the 0-based sequential
                              count of EMITTED app-site records for `c`
                              (type walked before value; left-to-right,
                              depth-first within each) — contiguous by
                              construction, since it only increments when
                              a record is actually emitted
The two id NAMESPACES never collide (`synth` vs `synthapp` segments), so
a human or C2 can also tell provenance from the `id` alone; `src` is the
belt-and-suspenders machine-readable field.

NAMED SEAM — the `exc` record (owner: whoever writes C2's replay/diff
binary; cite this note + `oracle_synth.rs`'s `SEAM_EXCLUSIONS` handling of
`dump_synth.lean`'s `q:"exc"` records for precedent):
  { "const":<name>, "id":<id>, "src":<src>, "goal":<E>, "exc":<message> }
`dump_synth.lean`'s header explains why an exception escaping the oracle
call must NEVER be conflated with `ok:false` — an honest "no instance" is
`none` from `synthInstance?`, not a thrown exception. Task C1's literal
6-field schema has no field for this case, but at Mathlib scale (thousands
of mined queries per shard, drawn from declarations nobody curated for
niceness) hitting an exception — most likely a heartbeat-budget exceeded
under the per-query reset described in NEAR_BUDGET below, but in
principle any other escaping `Exception` too — is a real, nonzero-
probability outcome, not a theoretical one as it is for the tiny curated
tier-1 corpus. This record shape is therefore a deliberate, minimal
extension of the brief's schema: distinguishable from an ordinary record
by the presence of the `exc` key and the ABSENCE of `ok`. C2 must skip
these from the gate, exactly as `oracle_synth.rs` skips `q:"exc"` — a
query the oracle itself could not answer cleanly is not part of any
regression gate.

A THIRD, CONSTANT-LEVEL `exc` variant, added in the fix round (see C1
above): `{ "const":<name>, "id":"<const>/const-exc", "src":"const",
"exc":<message> }`, emitted when an exception escapes the per-constant
`try` around BOTH miners' entire walk+query bodies for `c` (this is
distinct from the per-query `exc` above, which comes from `synthInstance?`
itself failing on ONE goal; a `src:"const"` record means something
escaped the MINING machinery — most plausibly a heartbeat-exceeded from
walking/querying one unusually large constant even after its fresh
per-constant budget — and every OTHER position for `c` that hadn't been
reached yet is simply absent, not falsely reported). C2 must skip these
too, for the same reason.

SENTINEL LINE — the LAST line of a complete file, distinguishable from
every record above by having neither `const` nor `id`:
  { "sentinel":true, "shard":"<I>/<N>", "records":<n> }
`<n>` is the total count of JSON lines written BEFORE the sentinel
(ordinary + both `exc` variants). Its presence is C2's positive proof
that this shard ran to completion rather than dying mid-write (see C1
above) — a truncated file (crashed shard, killed job, disk full) simply
lacks this line, which a bare exit-code check cannot distinguish from a
genuine empty-but-complete shard. C2 MUST treat a JSONL file with no
sentinel line (or one whose `records` count disagrees with the number of
non-sentinel lines actually present) as INCOMPLETE and refuse to gate on
it, exactly as it must already skip `exc` records from the gate itself.

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
MINING ALGORITHM — BINDER MINER (per constant, in telescope order)
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

M2 (doc note, no code change): this walk is DELIBERATELY purely
SYNTACTIC — it never calls `whnf` on `d` itself (only `isClass?`, inside
`withLocalDecl`, does its own internal `whnf` to find the head of `d`'s
TYPE, which is a different thing). A divergence from
`Lean.Meta.forallTelescopeReducing`'s naming-implied habit of reducing as
it walks. Deliberate: C2's own mirror of this walk, over
`leanr_kernel`/`leanr_meta` `Expr`/`Name` data, should not need a `whnf`
either to reproduce which positions this file calls `instImplicit` — the
binder's own `BinderInfo` in the stored `Expr` already says so, with no
reduction required to see it.

M3 (fix round): every `instImplicit` position, BEFORE it is handed to
`runQuery`, is additionally checked with `isClass? d` at the call site in
`main` — a binder with `BinderInfo.instImplicit` whose domain type is NOT
actually a class (Mathlib has a handful of these, e.g. abstract `[inst :
α]`-shaped patterns) is skipped entirely: no record, no `exc`, no
`runQuery` call, and its `idx` position is NOT reused by a later position
(the id numbering has a gap there, not a renumbering) — see ID SCHEME.

═══════════════════════════════════════════════════════════════════════
MINING ALGORITHM — APPLICATION-SITE MINER (fix round addition)
═══════════════════════════════════════════════════════════════════════
Binder mining alone mines a constant's HYPOTHESES — what a caller must
supply — which are, from inside that constant's own body, unsolvable
abstract type variables almost by construction (confirmed empirically in
the pre-fix-round smoke test: 239/29073 ok, 195 of those one single
degenerate instance (`instSizeOfDefault`) — a ~99.2%-trivially-negative
corpus). Real synthesis PRESSURE — the kind leanr's own synthesis engine
actually needs to get right — lives at APPLICATION sites: a place in a
constant's `.type` or `.value?` where some function `f`'s `instImplicit`
parameter is already SATURATED with a concrete argument, because the real
elaborator already solved that exact goal once to produce the stored
term. Mining that argument's TYPE as the goal and checking the ORACLE
still answers it the same way is a much higher-signal query than mining
an abstract hypothesis.

`mineAppSites` (below) walks a root `Expr` (called once on `c.type`, then
again on `c.value?` if present, threading ONE running `idx` counter across
both so ids are contiguous per ID SCHEME) with a manual structural
recursion: `forallE`/`lam` binders are entered via `withLocalDecl`
(substituting the body with the fresh fvar, exactly like the binder
miner, so any subterm found beneath a binder is automatically expressed
in terms of already-in-scope fvars rather than raw loose bvars); `letE`
similarly via `withLetDecl`; `mdata`/`proj` recurse straight through
(mirroring `encExpr`'s own erase/pass-through rules). At every `.app`
node, the FULL application spine is decomposed once via
`Expr.getAppFn`/`Expr.getAppArgs` (so a spine `f a b c`, itself nested as
`.app (.app (.app f a) b) c`, is inspected exactly ONCE, not once per
nesting level), and `Lean.Meta.getFunInfoNArgs fn args.size` identifies
which of those argument POSITIONS are instance-implicit
(`ParamInfo.isInstance`, which itself already applies an `isClass?` test
— see `Lean/Meta/FunInfo.lean:89-111` — so M3's filter is applied by
construction for this miner, re-checked below anyway for a single
uniform code path with the binder miner). Unlike the binder walk (M2
above), this NECESSARILY is not purely syntactic: `getFunInfoNArgs`
internally calls `inferType`/`whnf`/`isClass?` to learn the callee's OWN
signature — there is no way to know which argument positions are
instance-implicit from the call site's syntax alone, since Lean does not
re-annotate arguments at their use sites the way it annotates binders at
their declaration sites.

For each instance-implicit position found, the corresponding argument
`a` is checked `!a.hasLooseBVars && !a.hasMVar` (should always hold, since
every enclosing binder up to this point was walked via `withLocalDecl`/
`withLetDecl` and therefore already substituted into fvars — but unlike
the binder miner's OWN construction invariant, this is not a hand-proved
structural guarantee over arbitrary elaborator-generated terms, so a
violation here is a SKIP, not a fatal `throwError` — see FATAL-SHAPE
GUARDS). If closed, `argTy := ← inferType a` is computed and the SAME
closed check + M3's `isClass?` filter is applied to `argTy` before it is
handed to `runQuery` as the goal; `a` itself (the syntactic witness the
constant actually carries) is deliberately NOT emitted as part of the
record — see SOUNDNESS below for why. `getFunInfoNArgs fn args.size`
itself runs under a `try`/`catch _ => skip this spine's instance
positions, but still recurse into it`, since `fn` can in principle be an
arbitrary reducible-to-something-else term for which fun-info inference
is not guaranteed to succeed; a failure there is a missed mining
OPPORTUNITY, not a corpus-correctness violation, so it is silently
skipped rather than treated as fatal. After a spine is processed, the
walk recurses into `fn` and EVERY argument (including ones just mined as
instance positions — a derived/parametrized instance argument, e.g.
`@Module.compHom R M f _ inst`, can itself contain further nested
application sites worth mining), so nesting is fully explored.

SOUNDNESS: the recorded `val`/`ok` for an app-site record is ALWAYS the
ORACLE's own fresh `synthInstance?` answer on the mined `argTy`, exactly
like the binder miner — NEVER the syntactic argument term `a` the
constant happens to carry at that position. This is deliberate: `a` and a
fresh `synthInstance?` result for the SAME type can be DEFEQ but not
SYNTACTICALLY equal (e.g. two different, definitionally-equal derivations
of the same instance), and C2's whole purpose is to diff leanr's
synthesis against the ORACLE, not against "whatever term happens to be
sitting in a Mathlib declaration" — recording `a` as the expected value
would make C2 fail on a correct-but-differently-derived leanr answer.
Recording the oracle's own answer keeps the app-site corpus exactly as
sound as the binder corpus, just far more likely to be a NON-trivial
positive (this is the whole point of adding this miner — see the fix
round report for measured before/after counts).

═══════════════════════════════════════════════════════════════════════
NEAR_BUDGET
═══════════════════════════════════════════════════════════════════════
For one query, `hb0`/`hb1` bracket the `synthInstance?` call via
`IO.getNumHeartbeats`, and `near_budget := synthMaxHb != 0 && (hb1 - hb0)
* 100 > synthMaxHb * nearBudgetPercent` (`nearBudgetPercent := 20`).

I1 (fix round): `synthMaxHb := synthInstance.maxHeartbeats.get (←
getOptions) * 1000` — the ORACLE's OWN internal budget for a single
typeclass-resolution problem (`Lean/Meta/SynthInstance.lean:20-23`,
default 20000 → 20,000,000 scaled), enforced through a PRIVATE
`SynthInstance.Context.maxHeartbeats` field the resolution procedure
threads through itself (see `SynthInstance.lean:676,683,196`) — NEVER the
ambient `Core.Context.maxHeartbeats` this file used before the fix round
(five times larger scaled, ~200,000,000, so the old 20% threshold, 40M,
could never be crossed by a budget that tops out at 20M: `near_budget`
was measuring the query against a limit `synthInstance?` was never even
subject to, and fired 0/29073 times in the original full-shard run as a
direct, mechanical consequence — not because the mined queries were
uniformly cheap). This is the ORACLE's own margin against ITS budget
(leanr counts a deterministic step counter instead, per the global
constraint, so the two budgets are not comparable — see
`dump_synth.lean`'s header for the full rationale); C2 excludes any
`near_budget:true` record from its gate.

DEVIATION from `dump_synth.lean`, cited, EXPANDED in the fix round (see
C1 above): each mined query still runs under its OWN, innermost
`Lean.Core.withCurrHeartbeats` (`Lean/CoreM.lean`, confirmed present in
the pinned toolchain) — `dump_synth.lean`'s 15-query curated corpus never
needed even this, since 15 tiny queries never approach `maxHeartbeats` —
but `main` NOW ALSO wraps EACH CONSTANT'S ENTIRE body (both miners'
walks and every query for that constant) in its OWN, OUTER
`withCurrHeartbeats`, nested one level up from the per-query one. The
original code only had the inner (per-query) reset, which left the
TELESCOPE WALK's own `whnf`/`checkSystem` calls (inside `withLocalDecl`'s
`isClass?`) running under the run-wide baseline, accumulating across
EVERY constant in the shard — this is exactly what caused the CRITICAL
bug (see C1 at the top of this header): the shard died of a heartbeat
exception partway through, having walked ~17% of the pinned constant
list, leaving a truncated-but-valid JSONL. The outer, per-constant reset
fixes that: heartbeats now reset at each new constant, so the WALK's own
cost never leaks into the NEXT constant's budget. The inner, per-query
reset is kept nested inside it (see `runQuery`) for a narrower, orthogonal
reason: it stops ONE runaway query from silently eating the REST of the
SAME constant's freshly-reset budget (so a later position in a
many-instance-argument constant still gets a fair shot), and it keeps
`near_budget`'s own meaning exactly what it always was — "heartbeats
consumed by THIS SINGLE `synthInstance?` call", not by everything that
ran before it for the same constant.

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
  * every BINDER-mined `goal` must satisfy `!e.hasLooseBVars &&
    !e.hasMVar` (closed by construction per MINING ALGORITHM above; this
    re-verifies the invariant rather than merely assuming it forever
    holds under future changes to the mining walk or to Lean's binder
    semantics) — a violation here is FATAL (`throwError`), because for
    the binder miner it can only mean the walk's own construction
    invariant broke;
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
    C2 could never replay correctly.
    - For a BINDER-sourced record (`src:"binder"`): FATAL (`throwError`).
      Empirically 0/29073 in the full pre-fix-round shard-1/12 run —
      "should never happen" for this miner, so a violation IS evidence
      this file's own logic broke, worth crashing loudly over.
    - For an APP-sourced record (`src:"app"`): NOT fatal — emits the SAME
      `exc` shape used for an escaping oracle exception instead (this
      position genuinely cannot be honestly recorded as `ok`/`val`
      either, for the identical "no `mvars` field" reason) and moves on.
      Found LIVE during this fix round (not hypothetical): mining
      `MonadAttach (ExceptT ε m)` — itself discovered inside a Std
      declaration's own hidden extends-instance embedding, a legitimate
      app-site — and re-running `synthInstance?` on it FRESH comes back
      with the witness instance's own auxiliary universe parameters
      unconstrained by that goal alone. This is a genuine, reproducible
      property of that class hierarchy, not a mining defect; treating it
      as fatal would let ONE under-determined app-site query take down an
      entire shard, exactly the failure mode C1 exists to prevent. The
      binder miner's corpus was exhaustively run once already with zero
      occurrences (see above), which is why it keeps the stricter,
      FATAL treatment; the app miner's corpus is orders of magnitude
      larger and newly added, so leniency here is the correct match for
      how much LESS this miner's every query has been individually
      vetted.
An APP-SITE-mined `argTy` failing the closed check (BEFORE ever reaching
`runQuery`) is likewise a SKIP, not a `throwError` (see MINING ALGORITHM —
APPLICATION-SITE MINER above for why: unlike the binder miner's
hand-proved construction invariant, an arbitrary elaborator-generated
subterm not being closed at the point this walk finds it is a plausible,
non-catastrophic miss, not necessarily evidence this file's own logic is
broken) — the SAME asymmetry as the val guard above, for the same reason.

Any malformed env var is a `throw (IO.userError ..)`/`.error`, never a
`panic!`, so it is genuinely fatal, unconditionally. A violation of
either FATAL guard above is a `throwError` whose message is prefixed
`"dump_synth_mathlib: "` — this prefix is load-bearing (fix round, see C1
above): the per-constant `try` that soft-catches escaped exceptions (to
survive a heartbeat-exceeded from mining/querying one outsized constant
without aborting the whole shard) inspects the CAUGHT exception's message
for exactly this prefix and RE-THROWS (preserving fatality) if present,
rather than swallowing it into a soft `const-exc` record — a genuine
invariant violation must still bring the whole shard down loudly, exactly
as before the fix round; only a plausibly-external escape (heartbeats,
or anything else this file did not deliberately throw) is treated as
recoverable at the per-constant granularity.
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
validation (same error shape, same 1-based bounds) so the two sharding
conventions read as one scheme even though this is the synthesis sweep's
own independent shard spec, never the parse sweep's — including trimming
the raw env var before splitting (M1 fix round: the Rust side trims
before its own `split_once`; this parser now mirrors that instead of
leaving `raw` untrimmed and un-mirrored — `trimAscii` rather than the
deprecated `String.trim`, since the shard spec is plain ASCII digits and
a slash). -/
def parseShardSpec (raw : String) : Except String ShardSpec := do
  let parts := raw.trimAscii.toString.splitOn "/"
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

/-- APPLICATION-SITE miner (fix round addition — see header, MINING
ALGORITHM — APPLICATION-SITE MINER, for the full rationale/soundness
argument). Walks `root` (called once on a constant's `.type`, once more
on its `.value?` if present, THREADING `startIdx`/the returned `Nat`
across both calls so app-site ids stay contiguous per constant — see ID
SCHEME in the header), entering every binder via `withLocalDecl`/
`withLetDecl` (so any subterm found beneath one is expressed in terms of
already-in-scope fvars, never a raw loose bvar), and at every `.app`
spine (decomposed ONCE via `getAppFn`/`getAppArgs`, not once per nesting
level) calling `onGoal idx argTy` for every argument position the
callee's OWN `getFunInfoNArgs` marks `isInstance` — provided that
argument is closed and its type both closed and an actual class (mirrors
the binder miner's guard + the M3 filter, but a violation here is a SKIP
of just that one position, never fatal — the binder miner's closedness
violation is fatal because it is a hand-proved construction invariant;
this walk's is not, since it is inspecting arbitrary elaborator-generated
subterms, not positions this file's own recursion controls end to end).
Returns the updated idx counter so the caller can chain `.type` then
`.value?` under one running count. -/
partial def mineAppSites (root : Expr) (onGoal : Nat → Expr → MetaM Unit) (startIdx : Nat) :
    MetaM Nat := do
  let rec walk (e : Expr) (idx : Nat) : MetaM Nat := do
    match e with
    | .mdata _ b => walk b idx -- mdata ERASED, matching encExpr's own rule
    | .proj _ _ b => walk b idx
    | .forallE n d b bi => do
      let idx ← walk d idx
      withLocalDecl n bi d fun fvar => walk (b.instantiate1 fvar) idx
    | .lam n d b bi => do
      let idx ← walk d idx
      withLocalDecl n bi d fun fvar => walk (b.instantiate1 fvar) idx
    | .letE n t v b _ => do
      let idx ← walk t idx
      let idx ← walk v idx
      withLetDecl n t v fun fvar => walk (b.instantiate1 fvar) idx
    | e@(.app ..) => do
      let fn := e.getAppFn
      let args := e.getAppArgs
      -- Identify instance-implicit argument POSITIONS from the callee's
      -- own signature (`ParamInfo.isInstance`, itself already `isClass?`
      -- filtered — see `Lean/Meta/FunInfo.lean:89-111`). A failure HERE
      -- (e.g. `fn`'s type can't be inferred in isolation) is a missed
      -- mining opportunity, not a corpus fault: skip this spine's
      -- instance-position mining but still recurse into it below. This
      -- `try` is DELIBERATELY scoped to ONLY the `getFunInfoNArgs` call —
      -- NOT the `for` loop below that calls `onGoal` — see the comment on
      -- `idxAfterSpine` for why (a subtle, empirically-found idx-threading
      -- bug: catching around the loop too discarded already-emitted
      -- progress on ANY later exception, including a heartbeat-exceeded
      -- from `isClass?`/`inferType`, silently REWINDING `idx` to its
      -- pre-loop value while the `onGoal` calls it already made had
      -- already fired as real side effects — producing duplicate ids).
      let finfo? ← try some <$> getFunInfoNArgs fn args.size catch _ => pure none
      -- `idxAfterSpine`: NO try/catch here. If `isClass?`/`inferType`/
      -- `onGoal` throws partway through, it propagates naturally out of
      -- `walk`/`mineAppSites` to the per-constant `try` installed in
      -- `main` (see header, C1) — which is the CORRECT granularity to
      -- soft-skip at (abandon the rest of THIS constant, not silently
      -- desync this one spine's counter).
      let idxAfterSpine ← do
        match finfo? with
        | none => pure idx
        | some finfo => do
          let mut idx := idx
          for (pinfo, a) in finfo.paramInfo.zip args do
            if pinfo.isInstance then
              -- SKIP (not fatal) if not closed — see doc comment above.
              unless a.hasLooseBVars || a.hasMVar do
                let argTy ← inferType a
                unless argTy.hasLooseBVars || argTy.hasMVar do
                  if (← isClass? argTy).isSome then
                    onGoal idx argTy
                    idx := idx + 1
          pure idx
      let idx ← walk fn idxAfterSpine
      args.foldlM (fun idx a => walk a idx) idx
    | _ => pure idx
  walk root startIdx

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
    -- Total JSONL lines written so far (every ordinary/`exc`/`const-exc`
    -- record) — the SENTINEL line's `records` field, and C2's positive
    -- proof this shard ran to completion (see header, RECORD SCHEMA).
    let recCount ← IO.mkRef (0 : Nat)
    let go : MetaM Unit := do
      -- I1 fix: `synthInstance?`'s OWN budget, never the ambient
      -- `Core.Context.maxHeartbeats` — see header, NEAR_BUDGET.
      let synthMaxHb := synthInstance.maxHeartbeats.get (← getOptions) * 1000
      -- ===== SORT KEY + SHARD STRIDE — see header for the exact contract
      -- C2 must mirror. =====
      let named : Array (String × Name) :=
        env.constants.fold (fun acc n _ => acc.push (n.toString (escape := false), n)) #[]
      let sorted := named.qsort (fun a b => a.1 < b.1)
      -- `Array.zipIdx` pairs `(elem, idx)` — NOT `(idx, elem)` — 0-based.
      let shardConsts : Array Name :=
        sorted.zipIdx.filterMap
          (fun ((_, n), idx) => if idx % spec.n == spec.i - 1 then some n else none)
      -- Shared by BOTH miners: runs the oracle on one already-closed,
      -- already-`isClass?`-filtered `goal`, writes exactly one JSONL
      -- record, and enforces the val FATAL-SHAPE GUARD (see header). Only
      -- `id`/`src` differ between a binder-mined and an app-site-mined
      -- call — everything else (encoding, near_budget, the guard) is
      -- byte-identical by construction, on purpose.
      let runQuery : Name → String → String → Expr → MetaM Unit :=
        fun cName id src goal => do
          let hb0 ← IO.getNumHeartbeats
          -- Per-query heartbeat reset, NESTED inside the per-constant one
          -- installed below — see header, NEAR_BUDGET, DEVIATION.
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
               ("src", Json.str src), ("goal", goalJ), ("exc", Json.str msg)]
            recCount.modify (· + 1)
          | Except.ok val? =>
            let val? ← val?.mapM instantiateMVars
            -- FATAL-SHAPE GUARD (val): see header — an unassigned leftover
            -- universe/level mvar in the witness term would otherwise be
            -- silently mis-encoded as an unexplained `mvar` node (this
            -- schema carries no `mvars` field to declare it against).
            --
            -- BINDER-sourced (`src == "binder"`): FATAL (`throwError`,
            -- message prefixed `"dump_synth_mathlib: "` DELIBERATELY — the
            -- per-constant soft-catch below relies on that prefix to
            -- re-throw and preserve fatality). Empirically 0/29073 in the
            -- full pre-fix-round shard-1/12 run, so this really is
            -- "should never happen" for this miner, worth crashing loudly
            -- over if it ever does.
            --
            -- APP-sourced (`src == "app"`): NOT fatal — empirically REAL,
            -- not hypothetical, for this miner (found live during this fix
            -- round: `MonadAttach (ExceptT ε m)`, mined from a hidden
            -- extends-instance embedded in a Std declaration's own type,
            -- comes back from a FRESH `synthInstance?` with the witness
            -- instance's own auxiliary universe params unconstrained by
            -- that goal alone — a genuine, reproducible property of that
            -- specific class hierarchy, not a mining bug; see the fix
            -- round report). Crashing the whole shard over one
            -- under-determined app-site query would defeat C1's own goal
            -- (never let one bad position take down the corpus). Emits the
            -- SAME `exc` shape used for an oracle exception instead —
            -- this position genuinely cannot be honestly recorded as an
            -- `ok`/`val` either, for the identical "no `mvars` field"
            -- reason — and does NOT re-use the `throwError`/prefix path,
            -- so the per-constant catch never sees it as fatal.
            match val? with
            | some v =>
              if v.hasMVar then
                if src == "binder" then
                  throwError "dump_synth_mathlib: instance term for {cName} id {id} still \
                      has an mvar after instantiateMVars — likely an unconstrained universe \
                      parameter left unassigned by a raw synthInstance? call (see header, \
                      FATAL-SHAPE GUARDS); this schema has no `mvars` field to declare it against, \
                      so it cannot be honestly encoded"
                else
                  let (goalJ, _) := (encExpr goal).run {}
                  h.putStrLn <| Json.compress <| Json.mkObj
                    [("const", Json.str (cName.toString (escape := false))), ("id", Json.str id),
                     ("src", Json.str src), ("goal", goalJ),
                     ("exc", Json.str "instance term still has an mvar after instantiateMVars \
                         (an auxiliary universe parameter of the witness instance, unconstrained \
                         by this app-site goal alone) — not fatal for an app-sourced record, \
                         see header FATAL-SHAPE GUARDS")]
                  recCount.modify (· + 1)
                  return ()
            | none => pure ()
            let nearBudget := synthMaxHb != 0 && (hb1 - hb0) * 100 > synthMaxHb * nearBudgetPercent
            let (goalJ, st0) := (encExpr goal).run {}
            let fields :=
              [("const", Json.str (cName.toString (escape := false))), ("id", Json.str id),
               ("src", Json.str src), ("goal", goalJ), ("ok", Json.bool val?.isSome)]
              ++ (match val? with
                  | some v => [("val", (encExpr v).run' st0)]
                  | none => [])
              ++ [("near_budget", Json.bool nearBudget)]
            h.putStrLn <| Json.compress <| Json.mkObj fields
            recCount.modify (· + 1)
      for cName in shardConsts do
        let some cinfo := env.find? cName
          | throwError "dump_synth_mathlib: constant {cName} vanished from the environment \
              between sorting and lookup — should be impossible for an immutable `Environment`"
        let cStr := cName.toString (escape := false)
        -- Both miners' entire walk + every query for `cName`, run under
        -- ONE per-constant body so the C1 fix's outer heartbeat reset
        -- (below) covers all of it.
        let body : MetaM Unit := do
          -- ----- BINDER miner (see header, MINING ALGORITHM — BINDER
          -- MINER) -----
          mineFromType cinfo.type fun i goal => do
            -- FATAL-SHAPE GUARD (goal): see header, closed by construction
            -- — re-verify rather than assume.
            if goal.hasLooseBVars || goal.hasMVar then
              throwError "dump_synth_mathlib: mined goal for {cName} position {i} is not closed \
                  (hasLooseBVars={goal.hasLooseBVars}, hasMVar={goal.hasMVar}) — the telescope walk's \
                  bvar-free invariant was violated; this is a hard bug, not an encodable record"
            -- M3 fix: skip non-class instImplicit domains before querying.
            if (← isClass? goal).isSome then
              runQuery cName s!"{cStr}/synth/{i}" "binder" goal
          -- ----- APPLICATION-SITE miner (see header, MINING ALGORITHM —
          -- APPLICATION-SITE MINER) — walks `.type` then `.value?`,
          -- chaining ONE running idx counter across both. -----
          let onAppGoal : Nat → Expr → MetaM Unit :=
            fun i goal => runQuery cName s!"{cStr}/synthapp/{i}" "app" goal
          let idx1 ← mineAppSites cinfo.type onAppGoal 0
          match cinfo.value? with
          | some v => discard <| mineAppSites v onAppGoal idx1
          | none => pure ()
        -- C1 fix: reset heartbeats for the WHOLE constant body (mining +
        -- every query), not just each individual `synthInstance?` call —
        -- see header, NEAR_BUDGET, DEVIATION, for why the old per-query-
        -- only reset let heartbeats accumulate shard-wide and killed the
        -- run partway through. Also soft-catches anything that STILL
        -- escapes (most plausibly a heartbeat-exceeded on one outsized
        -- constant even under its fresh budget — the app-site miner walks
        -- `.value?`, which can be a large elaborator-generated proof term)
        -- so one pathological constant can never abort the whole shard —
        -- but RE-THROWS this file's own FATAL-SHAPE GUARD violations
        -- unchanged (recognized by their `"dump_synth_mathlib: "` message
        -- prefix — see header, FATAL-SHAPE GUARDS).
        try
          withCurrHeartbeats body
        catch ex => do
          let msg ← ex.toMessageData.toString
          if msg.startsWith "dump_synth_mathlib: " then
            throw ex
          else
            -- NAMED SEAM: the constant-level `exc` variant — see header,
            -- RECORD SCHEMA.
            h.putStrLn <| Json.compress <| Json.mkObj
              [("const", Json.str cStr), ("id", Json.str s!"{cStr}/const-exc"),
               ("src", Json.str "const"), ("exc", Json.str msg)]
            recCount.modify (· + 1)
      -- Completion SENTINEL — see header, RECORD SCHEMA. Written ONLY if
      -- every constant above was processed (a re-thrown FATAL guard
      -- violation skips straight past this, by design).
      let n ← recCount.get
      h.putStrLn <| Json.compress <| Json.mkObj
        [("sentinel", Json.bool true), ("shard", Json.str s!"{spec.i}/{spec.n}"), ("records", n)]
    discard <| go.toIO coreCtx coreState
