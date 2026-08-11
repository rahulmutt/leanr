//! The term elaborator. `TermElabM` over `leanr_meta`'s MetaM core.
//! Built in slices, each with its own design spec:
//!
//! - **M4b-1** — leaf forms: string literals, sorts, ascription, holes
//!   (docs/superpowers/specs/2026-07-23-m4b1-leaf-term-elaborator-design.md).
//! - **M4b-2** — binders and the let/have family: `fun`, `forall`,
//!   `arrow`, `depArrow`, `let`, `have`
//!   (docs/superpowers/specs/2026-07-24-m4b2-binders-postponement-design.md).
//! - **M4b-3 P1** — the application machinery, in `app/`: `elabApp` /
//!   `elabAtom` / `elabAppFn`'s ident case / `ElabAppArgs.main`,
//!   including implicit and strict-implicit insertion,
//!   `propagateExpectedType`, named arguments, eta-expansion, the `..`
//!   ellipsis, `@` explicit mode, and `.{u}` explicit universes
//!   (docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md).
//!   Identifiers moved here too: `elabIdent := elabAtom`
//!   (`App.lean:2246`), so a bare identifier is a zero-argument
//!   application, and M4b-1's leaf `builtin/ident.rs` is gone.
//! - **M4b-3 P2a** — the synthetic-mvar fixpoint (`synthesizeSyntheticMVars`'s
//!   ladder, `synthetic/`) and instance-implicit arguments
//!   (`processInstImplicitArg`, `trySynthesizeAppInstMVars` /
//!   `synthesizeAppInstMVars`, `app/args.rs` and `app/finalize.rs`), plus
//!   `withSynthesize` wrapping ascription and `let`/`have`, and the
//!   `elab_term_and_synthesize` entry point running the fixpoint before
//!   instantiation
//!   (docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md
//!   § P2a, as amended 2026-07-27). `Elab0.lean` grows a `class`/`instance`
//!   scaffold (`Wrap`/`Pair`/`NoInst`/`Dflt`) to exercise it, and
//!   `tests/oracle_elab.rs`'s `tc/*` records plus
//!   `tests/synthetic_smoke.rs` cover it end to end. **Not** included:
//!   `classExtension` and the `resultTypeOutParam?` producer/branch —
//!   those are P2b. `classExtension` (and the whole synthesis-side
//!   outParam mechanism) landed in P2b-i; the producer/branch is still a
//!   named seam below, owned by P2b-ii.
//! - **M4b-3 P3** — default instances and the non-leaf literals. Rung 3
//!   of the ladder is real (`synthesizeUsingDefault` /
//!   `synthesizeSomeUsingDefaultPrio` / `synthesizeUsingDefaultPrio` /
//!   `synthesizeUsingDefaultInstance` and the nested
//!   `synthesizePending` fixpoint, `synthetic/default_inst.rs`, plus
//!   `synthesizeUsingDefaultLoop` in `synthetic/ladder.rs`), and
//!   `num`/`char`/`scientific` are registered kinds — NOT leaves, the
//!   one thing they have in common with each other and not with `str`:
//!   each elaborates through an application, respectively
//!   `@OfNat.ofNat.{u}`, `Char.ofNat` and
//!   `@OfScientific.ofScientific.{u}`
//!   (`builtin/lit/`). P2a shipped rung 3 as a shape-guarded seam; P3
//!   RETIRED that seam rather than retargeting it, and
//!   `tests/seam_audit.rs`'s
//!   `no_seam_points_at_the_retired_p3_default_instance_label` gates
//!   that the old label never comes back
//!   (docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md
//!   § P3 and § Amendment 2). `Elab0.lean` grows `Tag`/`OfNat`/
//!   `OfScientific`/`Char` and, with P2a's `instDfltNat`, a three-level
//!   default-instance priority ladder (1000 / 100 / 50) so the
//!   descending priority walk is observable rather than assumed.
//!   **Not** included: `rawNatLit`, which no leanr parser
//!   production builds, so it is deliberately unregistered rather than
//!   implemented against a syntax kind that cannot occur.
//!
//! ## What is NOT built yet
//!
//! Every remaining construct is a *named* deferral, never a gap
//! discovered later: `dispatch::dispatch` routes every unregistered
//! syntax kind to `ElabError::UnsupportedSyntax(kind)`, and every seam
//! inside `app/` carries its owning slice in the message. Never a
//! silent no-op, never a panic, never a wrong `ExprId`.
//!
//! - **local-instance outParam result types** — `Context.resultIsOutParamSupport`
//!   and `State.resultTypeOutParam?` exist (P1), but nothing yet
//!   *produces* a `resultTypeOutParam?`. The blocker used to be that
//!   `leanr_olean` had no `classExtension` decode (`ClassEntry` = name +
//!   outParam positions); **M4b-3 P2b-i has since landed that decode and
//!   the whole SYNTHESIS-side mechanism** — `leanr_meta`'s `synth.rs`
//!   now has `preprocess` / `preprocess_out_param` / `assign_out_params`
//!   and its committed corpus pins `Op N N ?c` answered with `?c := N`
//!   assigned. So what remains here is purely the ELABORATOR half:
//!   `app/args.rs`'s `add_implicit_arg` and `app/finalize.rs`'s outParam
//!   branch each still raise a named seam for the missing PRODUCER
//!   — M4b-3 P2b-ii, which runs AFTER P3 rather than before it (design
//!   spec § Amendment 2). The reason is not sequencing taste: P2b's own
//!   headline behavior was UNVERIFIABLE before P3. `finalize`'s outParam
//!   branch runs `synthesizeSyntheticMVarsUsingDefault` only when the
//!   outParam mvar is still unassigned, and the way one stays unassigned
//!   is the oracle's own motivating shape, `getElem xs 0`, where the `0`
//!   is undetermined until the `OfNat` default instance fires. Without
//!   `num` and rung 3, every corpus term reachable took the degenerate
//!   `else` arm. P3 has no reciprocal dependency on P2b, so the swap was
//!   free.
//!
//!   Both callees that branch needs now exist, which is a change from
//!   what this entry recorded before P3. The oracle's own outParam
//!   branch (`App.lean:638-646`) calls `synthesizeAppInstMVars` (`:639`)
//!   and `synthesizeSyntheticMVarsUsingDefault` (`:643`); the first is
//!   P2a's `AppElab::synthesize_app_inst_mvars`, and the second is
//!   `synthesizeSyntheticMVars (postpone := .yes)` followed by
//!   `synthesizeUsingDefaultLoop` (`SyntheticMVars.lean:658-660`), both
//!   of which P3 made real — `TermElabM::synthesize_synthetic_mvars` and
//!   `TermElabM::synthesize_using_default_loop`. leanr does not wrap
//!   that pair under a single name because nothing calls it yet; P2b-ii
//!   is the slice that adds both the producer and the wrapper. So what
//!   is missing is the `resultTypeOutParam?` PRODUCER, nothing
//!   downstream of it and — since P2b-i — nothing underneath it either:
//!   `Elab0.lean` also still declares no class with an `outParam`, which
//!   is what keeps this arm unreachable from the corpus today.
//! - **coercions** (`mkCoe`, `CoeT`/`CoeFun`/`CoeSort`) —
//!   `ensure_has_type`/`elab_term_ensuring_type` and `app`'s own
//!   `ensureArgType` ERROR on a defeq mismatch rather than inserting a
//!   coercion — M4b-3 P4.
//! - **optParam/autoParam default filling and implicit-lambda
//!   insertion** — M4b-3 P5. (The implicit-lambda *guard* is P1's, in
//!   `elab.rs`; only the insertion is deferred.)
//! - **overload resolution** (more than one candidate from
//!   `elabAppFn`) — the slice that grows `resolve_global`, since it is
//!   unreachable while only exact names resolve.
//! - **`elabAsElim`** — M4b-4, and the one deferral whose seam is
//!   PARTIAL. `shouldElabAsElim` (`App.lean:1322-1328`) has five
//!   disjuncts; `app::head` can decide only `isRec`
//!   (`ConstantInfo::Rec`), so a genuine recursor head is seamed while
//!   an aux-recursor head (`Nat.casesOn`, `Nat.recOn`, `Nat.brecOn`) or
//!   an `@[elab_as_elim]` head is not — the other four read the
//!   `auxRecExt`/`elabAsElim` tag extensions, which leanr does not
//!   decode. Those cases still emit a term the oracle does not, with no
//!   seam; `tests/seam_audit.rs`'s fixture-source gate is the backstop
//!   until M4b-4 lands the decodes and `ElabElim`.
//! - **dot notation / LVal machinery (`Term.proj`, `pipeProj`,
//!   `dotIdent`, `namedPattern`, `choice`), `binop%`, anonymous
//!   constructor `⟨⟩`** — M4b-4.
//! - **macro expansion** — `dispatch` never expands a macro form; the
//!   dispatch table only ever matches a syntax kind directly against a
//!   registered elaborator. Deferred to the slice that first needs a
//!   macro form.
//! - **`open`/alias/`export`/`_root_` resolution** — `resolve.rs`'s
//!   `resolve_global` only resolves a global constant declared under
//!   the name exactly as written; namespace-prefix search, exported
//!   aliases, and root-qualification are a later slice.
//!
//! See `dispatch.rs`'s doc comment for the kind-by-kind deferral table,
//! `app/mod.rs`'s for the site-by-site seam index inside the
//! application elaborator, and `tests/seam_audit.rs` for the gate that
//! holds all three lists to the code.
//!
//! ## Recorded coverage gaps
//!
//! Three things below ARE built — none is a named seam — but each has
//! a known hole in what the corpus can currently prove about it.
//! Recording the hole here is the alternative to either leaving it to
//! be rediscovered or quietly asserting more coverage than exists.
//!
//! - **`SyntheticMVarKind::Postponed` has no producer anywhere in this
//!   branch** (re-verified by grep over `src/` and `tests/` at the end
//!   of P3: outside its own declaration at `synthetic/state.rs:58`,
//!   every CODE occurrence of the variant is a match arm —
//!   `synthetic/ladder.rs:264` and `synthetic/report.rs:106` — never a
//!   construction site). So this is stronger than "no differential
//!   coverage yet": `SavedContext`, `save_context` (zero callers),
//!   `with_saved_context`, `resume_postponed`, and the `check_occurs`
//!   accessor it uses for its assignment guard are UNREACHABLE from
//!   every code path in this branch, not merely undiffable.
//!
//!   **This entry used to predict that the first producer arrives with
//!   P3's `elabNum`. P3 landed and it did not — the prediction was
//!   simply wrong, measured against the pinned source rather than
//!   inferred.** `elabNumLit` (`BuiltinTerm.lean:210-229`) contains no
//!   `tryPostpone*` call at all; the only thing it registers is a
//!   `.typeClass` decl, through `mkInstMVar`. In the oracle the SOLE
//!   producer of a `.postponed` decl is `postponeElabTermCore`
//!   (`Term/TermElabM.lean:1449-1453`; the construction itself is
//!   `:1452`). It has TWO call sites, both in that file — the public
//!   `postponeElabTerm` at `:1608-1610`, and `elabUsingElabFnsAux`'s
//!   `Exception.postpone` handler at `:1651`, which restores the saved
//!   state and re-postpones. Note `elabUsingElabFnsAux` (`:1615`), NOT
//!   its caller `elabUsingElabFns` (`:1663`), which only saves state and
//!   delegates; the `Aux` one is the recursive walk over the registered
//!   elaborators and is where the postpone handler lives. (The pin's own
//!   docstring on `postponeElabTermCore`, `:1444-1448`, says the method
//!   "is used only at `elabUsingElabFnsAux`" — it names the right
//!   function but undercounts, since `postponeElabTerm` calls it too.)
//!   leanr has no call site for either. So the path
//!   stays dead code kept correct for whichever slice first postpones a
//!   term elaboration — M4b-4's `resolveLValLoop` is still the most
//!   likely candidate, but it is a candidate, not a schedule.
//! - **`may_postpone` is written but never read in production code.**
//!   Re-verified by grep at the end of P3: `elab.rs:86`
//!   (`TermElabM::new`) and `synthetic/state.rs:306`/`:308`
//!   (`without_postponing`, saving and restoring the flag) are its only
//!   writers in `src/`; nothing in `src/` ever reads it back (the only
//!   reads are `tests/synthetic_smoke.rs`'s own assertions on the
//!   field). Combined with `postpone_on_error` being consumed only
//!   inside the dead `resume_postponed` above, the ladder's rungs 2
//!   (postponement suppressed, errors postponed) and 4 (postponement
//!   suppressed, errors not postponed) are today BEHAVIORALLY IDENTICAL
//!   to rung 1 — nothing downstream branches on `may_postpone` or
//!   `postpone_on_error` yet.
//!
//!   What CHANGED with P3: rung 3 is no longer a shape guard that could
//!   only error or fall through, so the effective ladder that runs is
//!   rung 1 → rung 3 (real default instances,
//!   `synthetic/default_inst.rs`) → stuck report, and rung 3 is now the
//!   rung that closes a bare numeral's `OfNat ?α (lit v)` goal. Rungs 2,
//!   4 and 5 remain indistinguishable from rung 1. The five-rung
//!   structure is correct for when producers make the other knobs
//!   observable; recorded here so a reader does not assume five
//!   distinct rungs run today.
//! - **`leanr_meta` cannot report a stuck typeclass goal; the
//!   elaborator approximates it.**
//!   `leanr_meta::error::MetaError` declares `IsDefEqStuck` (`error.rs:36`)
//!   but constructs it nowhere (re-verified at the end of P3 — the only
//!   CODE occurrences are the declaration and `synthetic/ladder.rs:179`'s
//!   match arm; several files, this one included, also name it in prose,
//!   which a raw grep will show and which is not a construction site);
//!   `synth.rs`'s `synth_instance_main` (the private body
//!   behind the public `synth_instance`) documents `isDefEqStuckEx`
//!   (`Meta/Basic.lean` in the pinned oracle) as a named seam in its
//!   inline `Config`-divergence list at `synth.rs:1638-1650` — cited as
//!   `:1636-1650` until P3 task 4's own additions to `synth.rs` shifted
//!   it two lines — because
//!   tier-1 `leanr_meta` has no mctx-depth / read-only-mvar model with
//!   which to DECIDE stuck-vs-assignable. The consequence, measured
//!   rather than assumed and UNCHANGED: `MetaCtx::synth_instance(Wrap ?m)`
//!   called directly still *succeeds*, assigning `?m` from whichever
//!   candidate the search reaches first, where the pinned oracle refuses
//!   and reports the goal stuck. That tier-1 divergence is pinned by
//!   `leanr_meta`'s own gate — `tests/oracle_synth.rs`'s
//!   `exc_record_stuck_synth_0_pins_leanrs_current_divergent_answer`,
//!   whose doc says in as many words that it must be updated when the
//!   seam closes. Owner: whichever slice gives `leanr_meta` an
//!   mctx-depth / read-only-mvar model — not scoped to any M4b-3
//!   sub-slice today.
//!
//!   What CHANGED (M4b-3 P3 task 2): the ELABORATOR no longer depends on
//!   that seam for its own decision, so the consequences this entry used
//!   to record no longer follow. `synthetic/ladder.rs`'s
//!   `TermElabM::try_synth_instance` reconstructs `trySynthInstance`'s
//!   `.undef` from the goal type — a goal still mentioning an unassigned
//!   expr mvar is "not ready" instead of being answered by a guessed
//!   candidate. So the ladder's `.undef` trichotomy arm IS reachable
//!   from a typeclass goal, `report_stuck_synthetic_mvars` DOES fire
//!   from one, and bare `useWrap` now errors `StuckSyntheticMVar` as the
//!   oracle does. The three `tests/synthetic_smoke.rs` tests that were
//!   `#[ignore]`d on this basis
//!   (`stuck_synthesis_is_not_ready_rather_than_failure`,
//!   `bare_typeclass_application_is_reported_stuck`,
//!   `postpone_yes_leaves_the_mvar_pending`) are un-ignored and green.
//!   (P2a task 9's entry-point test was shaped around the old behaviour;
//!   it still passes and has not been revisited.)
//!
//!   What is STILL OPEN on the elaborator side is the price of that
//!   reconstruction: it is exact in the safe direction (a goal with no
//!   unassigned expr mvar can never be `.undef`, so ground goals still
//!   reach the real search) but over-approximates in three cases, which
//!   do NOT share an owner. `try_synth_instance`'s own doc enumerates
//!   them with oracle citations; in short: (1) `outParam` goals such as
//!   `HAdd Nat Nat ?γ`, which the oracle ANSWERS via
//!   `preprocessOutParam`/`assignOutParams` and leanr would defer.
//!   M4b-3 P2b-i ported both into `leanr_meta`, so the MECHANISM is no
//!   longer missing; what is left is teaching this pre-test to exempt
//!   output-parameter positions, which is P2b-ii's, and what keeps the
//!   residue unreachable meanwhile is that `Elab0.lean` declares no
//!   outParam class. Closed by P2b-ii, NOT by the depth model; (2) an
//!   all-polymorphic candidate set; (3) a zero-candidate class with an
//!   mvar goal (`NoInst ?a`), where the oracle throws "failed to
//!   synthesize" and leanr reports stuck — both error, so neither is a
//!   record divergence. `dump_elab.lean`'s dumper drops any query whose
//!   oracle side throws, so no corpus record can cover (3), which is
//!   exactly why it is written down rather than left to be
//!   rediscovered.
pub mod app; // M4b-3 P1
pub mod builtin; // Tasks 4-6
pub mod dispatch;
pub mod elab;
pub mod error;
pub mod resolve; // Task 5
pub mod synthetic; // M4b-3 P2a

pub use elab::TermElabM;
pub use error::ElabError;
