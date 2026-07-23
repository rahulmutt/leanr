/- Emits the tier-1 typeclass-SYNTHESIS query corpus as canonical JSONL
(M4a plan-4 spec § The gate). Sibling of `dump_defeq.lean`: same
canonical expr/level scheme, same canonicalization rules, same
hermetic contract — runs with `LEAN_PATH` set to this directory so
`import Synth0` resolves to the committed fixture and NOTHING else.
`Synth0` is prelude-mode and import-free, so the oracle environment
here is exactly the environment `crates/leanr_meta/tests/
oracle_synth.rs` replays from `Synth0.olean`.

The canonical expr/level scheme and every canonicalization rule
(binder names erased, `MData` erased, mvars/fvars numbered in
first-occurrence order WITHIN one record, literals as decimal strings,
binder-info kind letters) are documented in `dump_defeq.lean`'s module
header — that file is the authoritative statement; the encoders below
(`biStr`/`encLevel`/`EncSt`/`encExpr`) are copied from it VERBATIM so
the two corpora share one scheme by construction. They are duplicated
rather than factored because Lean has no shared-module story here that
does not break the "import ONLY the fixture" hermeticity contract (a
common `Enc.lean` would have to live in this directory and would then
be importable — and thus a second module in the oracle environment —
unless built separately; not worth it for ~70 lines).

Record shape (one per curated query):
  { "id"   : "<tag>/synth/<i>"
  , "q"    : "synth"
  , "goal" : <E>                     -- the synthesis goal type
  , "mvars": [ {"i":<N>, "t":<E>} ]  -- goal mvars: canonical index + TYPE
  , "ok"   : true|false              -- oracle verdict
  , "val"  : <E>                     -- present iff ok; the instance TERM
  , "near_budget": true|false        -- see below
  }

`mvars` exists because the canonical expr scheme carries no mvar-type
field, yet the replay side must DECLARE every goal metavariable before
calling `synth_instance` (a goal mvar that is merely interned but not
declared makes leanr's `synth_pending` raise `MetaError::MVar`).
`dump_defeq.lean`'s `defeq_mvar` records dodge this by having the gate
re-derive the type from the structurally-parallel `b` side; a
synthesis record has no such parallel side, so the type is emitted
EXPLICITLY here. Indices are numbered in the SAME `EncSt` that
numbered `goal`, so they line up with the `{"k":"mvar","i":N}` nodes
inside it.

`near_budget` implements the global determinism constraint ("queries
near any step/depth budget are recorded and excluded from the gate").
leanr counts deterministic `MetaCtx::step`s and the oracle counts
heartbeats, so the two budgets are not comparable — what this flag
records is the ORACLE's own margin: heartbeats consumed by this single
`synthInstance?` call as a fraction of `Core.Context.maxHeartbeats`.
Anything over 20% is flagged, and `oracle_synth.rs` skips it: a query
that close to the oracle's own limit is one whose recorded verdict
could flip on an unrelated performance change, which is exactly the
kind of record a regression gate must not contain. Every curated query
below is tiny, so the expected flag is `false` throughout — the field
is the mechanism, not a current exclusion.

`synthInstance?` (not `synthInstance`) is called: it returns
`Option Expr`, so an honest "no instance" is `none` (-> `ok:false`)
and is not conflated with the `throwFailedToSynthesize` that
`synthInstance` also raises after an `isDefEqStuck`
(`SynthInstance.lean:1024-1030`). Any exception that DOES escape is
emitted as an `"exc"` record instead of a query record, and such a
query is not part of the committed gate — a corpus entry must be one
the oracle answered cleanly.
-/
-- NOT `import Synth0`: like `dump_defeq.lean`/`Meta0`, Synth0 is
-- prelude-mode and declares its own `PProd`/`Prod`/`Eq`/`HEq`/...
-- scaffold, which collides with the real `Init` this file needs for
-- the `Lean`/`Lean.Meta` API. The query environment is loaded purely
-- at RUNTIME via `importModules` in `main` below.
import Lean
open Lean Lean.Meta

-- ===== canonical expr/level encoder (verbatim from dump_defeq.lean) =====

/-- `default`->d, `implicit`->i, `strictImplicit`->s, `instImplicit`->c
(binder NAMES are erased everywhere; only this kind letter survives). -/
def biStr : BinderInfo → String
  | .default => "d"
  | .implicit => "i"
  | .strictImplicit => "s"
  | .instImplicit => "c"

/-- Levels never carry mvars in a fully-elaborated corpus — the
canonical scheme has no `lmvar` case, so an actual `Level.mvar` here
would be a real gap; fail loudly rather than silently emit a
wrong-but-well-formed record. -/
partial def encLevel : Level → Json
  | .zero => Json.mkObj [("k", "zero")]
  | .succ u => Json.mkObj [("k", "succ"), ("u", encLevel u)]
  | .max a b => Json.mkObj [("k", "max"), ("a", encLevel a), ("b", encLevel b)]
  | .imax a b => Json.mkObj [("k", "imax"), ("a", encLevel a), ("b", encLevel b)]
  | .param n => Json.mkObj [("k", "param"), ("n", n.toString (escape := false))]
  | .mvar _ => panic! "dump_synth: unexpected Level.mvar (not in the canonical scheme)"

/-- Per-record numbering state for mvars/fvars, first-occurrence order.
Threaded across ONE record's `goal` -> `mvars[].t` -> `val` encodes, so
an mvar referenced in several of them gets one stable number. -/
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

-- ===== query corpus =====

/-- `Sort 0`'s successor, i.e. `Type` — the universe every class and
every carrier type in `Synth0.lean` is declared at once its `u` is
instantiated to `0`. -/
def type0 : Expr := mkSort (mkLevelSucc Level.zero)

/-- `C.{0} a` for a single-parameter class `C`. -/
def cls1 (c : Name) (a : Expr) : Expr := mkApp (mkConst c [Level.zero]) a

/-- `Prod.{0,0} a b`. -/
def prod2 (a b : Expr) : Expr :=
  mkApp (mkApp (mkConst `Prod [Level.zero, Level.zero]) a) b

def nTy : Expr := mkConst `N

/-- The curated synthesis corpus. `(tag, index, goal-builder)`; the
builder runs in `MetaM` so a query can mint a metavariable (the stuck
case). The index is per-TAG, never a global counter, matching
`dump_defeq.lean`'s `constant/kind/index` id contract.

What each entry exercises (task B7's brief):
* `simple`      — one-step resolution against a concrete instance.
* `diamond`     — `Mul N` is derivable directly (`instMulN`) AND via
                  `Semigroup.toMul instSemigroupN` AND via
                  `Monoid.toSemigroup`; the search must pick ONE
                  deterministic derivation, which the committed `val`
                  pins. (Redundant-path sense — `Synth0.lean`'s own
                  comment explains why the superclass chain is linear.)
* `superclass`  — resolving the class that OWNS the projection
                  instances (`Semigroup N`, `Monoid N`).
* `chain`       — subgoal chaining through the parametrized
                  `instAddProd`/`instChainProd` (one and two levels
                  deep), so the committed `val` carries the recursively
                  synthesized sub-instances as arguments.
* `default`     — the `@[default_instance]`-tagged `instOfNN`. NOTE:
                  `synthInstance` itself never CONSULTS the default-
                  instance table (that is the elaborator's
                  `synthesizeUsingDefault`, M4b); what this pins is
                  that a default-tagged instance is still an ordinary
                  instance for resolution, and that the extra
                  `defaultInstanceExtension` entry does not perturb it.
* `priority`    — `Pri N`: `instPriLow` is declared LATER but at LOWER
                  priority, so declaration order and priority order
                  disagree and the committed `val` (`instPriHigh`)
                  distinguishes them.
* `negative`    — `NoInst N`: no candidate at all -> `ok:false`.
* `negativeSub` — `Chain (Prod NoBase N)`: fails only AFTER
                  `instChainProd` was applied and its first subgoal
                  failed.
* `cyclic`      — `CycA N`: `CycA`/`CycB` are derivable ONLY from each
                  other (a 2-cycle with NO base instance anywhere), so
                  the goal is genuinely unsolvable -> `ok:false`. The
                  point of the query is that DECIDING so terminates
                  rather than loops (design-spec tier-1 shape; same
                  graph shape as B5's `InstancesCyclic.lean`, exercised
                  here differentially rather than only as a leanr-side
                  termination unit test).
* `mvarGoal`    — `OfN ?n N` with `?n : N` an UNASSIGNED mvar minted
                  OUTSIDE the search. Unlike `stuck` below, `?n` sits
                  in a position the search never needs to ASSIGN (the
                  candidate `instOfNN`'s own `n` binder becomes a fresh
                  INNER mvar, and it is that inner one that gets
                  assigned `?n`), so the oracle answers cleanly and the
                  answer term still MENTIONS `?n`. This is the record
                  that exercises the `mvars` field.
* `stuck`       — `Add ?a` with `?a` an UNASSIGNED mvar minted OUTSIDE
                  the search. `synthInstanceCore?` runs `main` under
                  `withNewMCtxDepth`, so `?a` is read-only there and
                  `isDefEqStuckEx := true` makes the first unification
                  throw. See this file's header on `"exc"` records. -/
def synthQueries : List (Name × Nat × MetaM Expr) :=
  [ (`simple,      0, pure (cls1 `Add nTy))
  , (`simple,      1, pure (cls1 `Mul nTy))
  , (`diamond,     0, pure (cls1 `Mul nTy))
  , (`superclass,  0, pure (cls1 `Semigroup nTy))
  , (`superclass,  1, pure (cls1 `Monoid nTy))
  , (`chain,       0, pure (cls1 `Add (prod2 nTy nTy)))
  , (`chain,       1, pure (cls1 `Add (prod2 nTy (prod2 nTy nTy))))
  , (`chain,       2, pure (cls1 `Chain (prod2 nTy nTy)))
  , (`default,     0, pure (mkApp (mkApp (mkConst `OfN [Level.zero]) (mkConst `N.zero)) nTy))
  , (`priority,    0, pure (cls1 `Pri nTy))
  , (`negative,    0, pure (cls1 `NoInst nTy))
  , (`negativeSub, 0, pure (cls1 `Chain (prod2 (mkConst `NoBase) nTy)))
  , (`cyclic,      0, pure (cls1 `CycA nTy))
  , (`mvarGoal,    0, do
      pure (mkApp (mkApp (mkConst `OfN [Level.zero]) (← mkFreshExprMVar nTy)) nTy))
  , (`stuck,       0, do pure (cls1 `Add (← mkFreshExprMVar type0)))
  ]

/-- Anything over this fraction (in percent) of the oracle's
`maxHeartbeats` marks the record `near_budget` (this file's header
explains why the flag exists and why every current entry is under it). -/
def nearBudgetPercent : Nat := 20

unsafe def main : IO Unit := do
  -- Must run before any `importModules (loadExts := true)` or the
  -- import throws internally (same pitfall dump_defeq.lean documents).
  Lean.enableInitializersExecution
  Lean.initSearchPath (← Lean.findSysroot)
  -- `loadExts := true` is REQUIRED here for a stronger reason than in
  -- dump_defeq.lean: `instanceExtension`/`defaultInstanceExtension`
  -- ARE the tables synthesis reads. Without it every query below would
  -- report "no instance".
  let env ← Lean.importModules #[{ module := `Synth0 }] {} (trustLevel := 0) (loadExts := true)
  let coreCtx : Core.Context := { fileName := "<dump_synth>", fileMap := default }
  let coreState : Core.State := { env }
  let go : MetaM Unit := do
    let maxHb := (← readThe Core.Context).maxHeartbeats
    for (tag, i, mkGoal) in synthQueries do
      let id := s!"{tag.toString (escape := false)}/synth/{i}"
      let goal ← mkGoal
      -- Every mvar reachable from the goal, with its declared type —
      -- see this file's header for why `mvars` is emitted explicitly.
      let goalMVars := (← getMVars goal)
      let hb0 ← IO.getNumHeartbeats
      let r : Except String (Option Expr) ←
        try
          Except.ok <$> Meta.synthInstance? goal
        catch ex => Except.error <$> ex.toMessageData.toString
      let hb1 ← IO.getNumHeartbeats
      -- `goal`/`mvars` encoding, shared by BOTH the `exc` and the
      -- ordinary-record branches below (task-B7-review Important-2: the
      -- `exc` record used to carry neither, so nothing could replay its
      -- goal without hand-constructing it independently of the corpus).
      -- Run AFTER the `try/catch` above so it reflects whatever the
      -- mctx actually looks like post-attempt, exactly like the
      -- ordinary-record branch already did — an `isDefEqStuckException`
      -- is thrown before any assignment happens to the OUTER mvar these
      -- queries mint, so this is not expected to ever exercise the loud
      -- failure below for a stuck-style exc record, but it is the same
      -- honest choice either way.
      let encGoalAndMVars : MetaM (Json × Array Json × EncSt) := do
        -- ONE `EncSt` per record, threaded goal -> mvar types -> val
        -- (the canonicalization rule: numbering is per RECORD).
        let (goalJ, st0) := (encExpr (← instantiateMVars goal)).run {}
        let (mvarsJ, st1) ← goalMVars.foldlM
          (fun (acc, st) (m : MVarId) => do
            let ty ← instantiateMVars (← m.getType)
            let (tyJ, st') := (encExpr ty).run st
            -- `m` MUST already have been numbered while encoding `goal`
            -- above (that is the whole point of threading one `EncSt`
            -- from `goal` into this fold). If it was NOT — e.g. because
            -- `m` got ASSIGNED during `synthInstance?` and
            -- `instantiateMVars goal` therefore dropped it from the
            -- encoding — a silent `getD 0` fallback here would point
            -- this record's `"i":0` at a DIFFERENT mvar (or at nothing),
            -- and the replay side would then declare the wrong type and
            -- could pass or fail for the wrong reason. Fail loudly
            -- instead, matching `encLevel`'s existing idiom above for an
            -- out-of-scheme level mvar.
            let idx := match st'.mvars.get? m with
              | some i => i
              | none => panic! s!"dump_synth: mvar {m.name} not numbered by `goal` (collected \
                  by getMVars before synthInstance? but no longer reachable from goal after \
                  instantiateMVars — likely got ASSIGNED during synthesis; a corpus record \
                  cannot honestly report an index for it)"
            pure (acc.push (Json.mkObj [("i", idx), ("t", tyJ)]), st'))
          (#[], st0)
        pure (goalJ, mvarsJ, st1)
      match r with
      | Except.error msg =>
        -- Not a corpus record in the ordinary sense (no oracle VERDICT
        -- to compare against, so it is skipped by the gate), but `goal`/
        -- `mvars` are still emitted so the query it names can be
        -- replayed directly rather than hand-reconstructed — see this
        -- file's header and `oracle_synth.rs`'s `SEAM_EXCLUSIONS`
        -- sibling test for the `isDefEqStuckEx` seam.
        let (goalJ, mvarsJ, _) ← encGoalAndMVars
        IO.println <| Json.compress <| Json.mkObj
          [("id", id), ("q", "exc"), ("goal", goalJ), ("mvars", Json.arr mvarsJ), ("msg", msg)]
      | Except.ok val? =>
        let val? ← val?.mapM instantiateMVars
        let (goalJ, mvarsJ, st1) ← encGoalAndMVars
        let nearBudget := maxHb != 0 && (hb1 - hb0) * 100 > maxHb * nearBudgetPercent
        let fields :=
          [("id", Json.str id), ("q", Json.str "synth"), ("goal", goalJ),
           ("mvars", Json.arr mvarsJ), ("ok", Json.bool val?.isSome)]
          ++ (match val? with
              | some v => [("val", (encExpr v).run' st1)]
              | none => [])
          ++ [("near_budget", Json.bool nearBudget)]
        IO.println <| Json.compress <| Json.mkObj fields
  discard <| go.toIO coreCtx coreState
