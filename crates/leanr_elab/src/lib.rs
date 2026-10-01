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
//!   outParam mechanism) landed in P2b-i; the producer/branch shipped
//!   in P2b-ii.
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
//! - **M4b-3 P2b-ii** — the elaborator-side local-instance outParam
//!   branch. `app/args.rs`'s
//!   `is_next_out_param_of_local_instance_and_result` is the
//!   `resultTypeOutParam?` PRODUCER, and `app/finalize.rs`'s outParam
//!   branch is the consumer, calling `synthesize_app_inst_mvars` then
//!   the new `synthesize_synthetic_mvars_using_default` composite
//!   (`synthetic/ladder.rs`, wrapping
//!   `synthesize_synthetic_mvars (postpone := yes)` +
//!   `synthesize_using_default_loop`) exactly as the oracle's
//!   `App.lean:638-646` does. `synthetic/ladder.rs`'s
//!   `has_mvar_outside_out_params` is the positional exemption that
//!   lets an `outParam` goal such as `Get Cell Nat ?elem` reach the
//!   real search instead of postponing, while a goal with an mvar in a
//!   NON-output position still postpones. `Elab0.lean` grows the first
//!   `outParam` class (`Get`, with `Cell`) to exercise the branch, a
//!   fourth default-instance priority (75, `instFreshSeed` on `Fresh`)
//!   between `instOfNatNat`'s 100 and `instOfNatTag`'s 50, and
//!   `Lean.Internal.coeM` — the env gate `resultIsOutParamSupport`
//!   reads. `coeM` is an EXISTENCE-ONLY axiom; its real definition
//!   (`Init/Coe.lean:336-339`) is owed by the do-notation slice, the
//!   only one that reaches its other consumer (design spec § Amendment
//!   4 item 7). The corpus grows `dflt/polyInstImplicit` plus
//!   `outParam/getFst`, `outParam/getElem`, `outParam/getElemIdxNat`,
//!   `outParam/getElemUnderDflt` and `outParam/getElemAscribed`
//!   (docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md
//!   § Amendment 4).
//!
//! ## What is NOT built yet
//!
//! Every remaining construct is a *named* deferral, never a gap
//! discovered later: `dispatch::dispatch` routes every unregistered
//! syntax kind to `ElabError::UnsupportedSyntax(kind)`, and every seam
//! inside `app/` carries its owning slice in the message. Never a
//! silent no-op, never a panic, never a wrong `ExprId`.
//!
//! - **coercions** — SHIPPED in M4b-3 P4 (`coe.rs`: `mk_coe` /
//!   `ensure_has_type` / `ensure_type`; the ladder's `Coe` arm).
//!   `mkCoe`/`ensureHasType` and the `CoeT` half landed in task 7, so
//!   `elab_term_ensuring_type`, the `($e :)` ascription arm and `app`'s
//!   own `ensureArgType` insert a `CoeT` coercion instead of erroring on
//!   a defeq mismatch. `coerceToFunction?` on an application head
//!   (`CoeFun`) landed in task 8 (`app/args.rs`'s
//!   `synthesize_pending_and_normalize_fun_type`). `ensureType`'s
//!   `coerceToSort?` on a binder domain (`CoeSort`) landed in task 9
//!   (`coe.rs`'s `ensure_type`). Still deferred: `coerceMonadLift?`
//!   (the do-notation slice; a shape guard in `leanr_meta::coe` names
//!   it) and the `↑`/`⇑`/`↥` notations (the parser slice that adds
//!   them).
//! - **optParam/autoParam default filling and implicit-lambda
//!   insertion** — SHIPPED in M4b-3 P5. `optParam` fills its declared
//!   default (task 8, `app/args.rs`'s `opt_param_default`); an omitted
//!   `autoParam` mints a `.tactic` synthetic mvar the ladder reports
//!   unsolved (task 9, `mk_tactic_mvar`); implicit-lambda insertion
//!   itself landed in `elab.rs` (tasks 5-6, `use_implicit_lambda`/
//!   `elab_implicit_lambda` — the *guard* was P1's, `block_implicit_lambda`).
//!   The `@($t)`/`@$t` wrap that elaborates with insertion explicitly
//!   disabled SHIPPED in the M4b-3 close-out (`app/mod.rs`'s
//!   `elab_explicit`). `useImplicitLambda`'s `.postpone` arm SHIPPED in
//!   M4b-4a P2 (`elab.rs`'s `UseImplicitLambda::Postpone`).
//! - **overload resolution** (more than one candidate from
//!   `elabAppFn`) — the slice that grows `resolve_global_name`, since it is
//!   unreachable while only exact names resolve.
//! - **`elabAsElim`** — SHIPPED in M4b-4c P2 (`app/elim.rs`): every
//!   `shouldElabAsElim` head (`App.lean:1322-1328`) is diverted to
//!   `ElimElab` by `app::elab_app_args`, exactly as `App.lean:1373-1383`
//!   does.
//! - **dot notation / LVal machinery** — M4b-4a. P1 SHIPPED: `Term.proj`
//!   index projections, structure fields and projection functions, the
//!   resolution loop, `numImplicitParams` and `@` on projection heads
//!   (`app/lval.rs`, `app/head.rs`). P2 SHIPPED term-level postponement
//!   (`postpone.rs`; `resolveLValLoop`, `elabAppArgs` and
//!   `useImplicitLambda` produce). P3 SHIPPED generalized field
//!   notation and P4 SHIPPED `pipeProj`/`dotIdent`/`namedPattern`
//!   (`app/head.rs`, `app/dot_ident.rs`). Still deferred, each a named
//!   seam: `choice` the overloading slice, private field projections the slice that models private
//!   names. `binop%` — the macro-expansion slice. The anonymous
//!   constructor `⟨⟩` is elaborated by `builtin::anon_ctor` (M4b-4b); its
//!   pattern position is left to the match slice.
//! - **macro expansion** — `dispatch` never expands a macro form; the
//!   dispatch table only ever matches a syntax kind directly against a
//!   registered elaborator. Deferred to the slice that first needs a
//!   macro form.
//! - **`open`/alias/`export`/`_root_` resolution** — `resolve.rs`'s
//!   `resolve_global_name` only resolves a global constant declared under
//!   the name (or a prefix of it) exactly as written; namespace-prefix search, exported
//!   aliases, and root-qualification are a later slice.
//!
//! See `dispatch.rs`'s doc comment for the kind-by-kind deferral table,
//! `app/mod.rs`'s for the site-by-site seam index inside the
//! application elaborator, and `tests/seam_audit.rs` for the gate that
//! holds all three lists to the code.
//!
//! ## Recorded coverage gaps
//!
//! Each thing below IS built — none is a named seam. The first two
//! entries are closed history (the hole they recorded closed in M4b-4a
//! P2) and are kept for the record; the last still has a known hole in
//! what the corpus can currently prove about it. Recording the hole
//! here is the alternative to either leaving it to be rediscovered or
//! quietly asserting more coverage than exists.
//!
//! - **`SyntheticMVarKind::Postponed` producers (history).** Until
//!   M4b-4a P2 the variant had no producer: M4b-3 P3's `elabNum` was
//!   predicted to be the first and was not (`elabNumLit`,
//!   `BuiltinTerm.lean:210-229`, contains no `tryPostpone*` call). In the
//!   oracle the SOLE producer of a `.postponed` decl is
//!   `postponeElabTermCore` (`Term/TermElabM.lean:1449-1453`), reached
//!   from the public `postponeElabTerm` and from
//!   `elabUsingElabFnsAux`'s `Exception.postpone` handler. Since
//!   M4b-4a P2 leanr's `postpone_elab_term` (`postpone.rs`) is called
//!   from `elab_using_elab_fns`'s catch and from `useImplicitLambda`'s
//!   `.postpone` arm (`elab.rs`), so `save_context`, `with_saved_context`
//!   and `resume_postponed` are live. The `p2/*` corpus records cover
//!   resume end to end (`tests/postpone_smoke.rs` covers the mechanics).
//! - **`may_postpone` readers (history).** Until M4b-4a P2 the flag's
//!   one production reader could only see `true`. Now its readers are
//!   the `try_postpone` family (`postpone.rs`: `try_postpone`,
//!   `try_postpone_if_mvar`, `try_postpone_if_none_or_mvar`) and the
//!   `.postpone` arm of `elab_term_core`. Writers are `TermElabM::new`
//!   and `synthetic/state.rs`'s `without_postponing`, which wraps the
//!   ladder's rungs 2 and 4. Those rungs are now behaviourally distinct
//!   from rung 1, since they resume postponed terms with postponement
//!   off: `resuming_does_not_catch_its_own_postpone` and
//!   `p2/implicit-lambda-postpone` both depend on it. Rung 3 (real
//!   default instances, `synthetic/default_inst.rs`) is what closes a
//!   bare numeral's `OfNat ?α (lit v)` goal. Rung 5 (tactics) and the
//!   stuck report that follows it (`report_stuck_synthetic_mvars`, only
//!   under `postpone == .no`) are unchanged.
//! - **`leanr_meta` cannot report a stuck typeclass goal; the
//!   elaborator approximates it.**
//!   `leanr_meta::error::MetaError` declares `IsDefEqStuck` (`error.rs:39`).
//!   As of macro/binop% P1 it is constructed at two ported defeq sites, only
//!   under `with_def_eq_stuck_ex`, which `synth_instance` does not yet use,
//!   so synthesis still never reports stuck (the elab-side consumer is
//!   `synthetic/ladder.rs:179`'s match arm);
//!   `synth.rs`'s `synth_instance_main` (the private body
//!   behind the public `synth_instance`) documents `isDefEqStuckEx`
//!   (`Meta/Basic.lean` in the pinned oracle) as a named seam in its
//!   inline `Config`-divergence list (`synth.rs:2175-2195` at this
//!   writing) because `synth_instance` does not yet run under
//!   `with_new_mctx_depth` with `isDefEqStuckEx` set (the depth model
//!   itself now exists). The consequence, measured rather than assumed
//!   and UNCHANGED: `MetaCtx::synth_instance(Wrap ?m)`
//!   called directly still *succeeds*, assigning `?m` from whichever
//!   candidate the search reaches first, where the pinned oracle refuses
//!   and reports the goal stuck. That tier-1 divergence is pinned by
//!   `leanr_meta`'s own gate — `tests/oracle_synth.rs`'s
//!   `exc_record_stuck_synth_0_pins_leanrs_current_divergent_answer`,
//!   whose doc says in as many words that it must be updated when the
//!   seam closes. Owner: the synthesis-onto-depth follow-up
//!   (macro/binop% P1 follow-up) — not scoped to any M4b-3 sub-slice.
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
//!   reach the real search) but over-approximates in three cases —
//!   of which residue 1 is closed by M4b-3 P2b-ii; two remain, and
//!   those two do NOT share an owner. `try_synth_instance`'s own doc
//!   enumerates all three with oracle citations; in short: (1)
//!   `outParam` goals — CLOSED by M4b-3 P2b-ii's positional exemption
//!   in `try_synth_instance` (§ Amendment 4 item 6), not by the depth
//!   model; (2) an
//!   all-polymorphic candidate set; (3) a zero-candidate class with an
//!   mvar goal (`NoInst ?a`), where the oracle throws "failed to
//!   synthesize" and leanr reports stuck — both error, so neither is a
//!   record divergence. `dump_elab.lean`'s dumper drops any query whose
//!   oracle side throws, so no corpus record can cover (3), which is
//!   exactly why it is written down rather than left to be
//!   rediscovered.
pub mod app; // M4b-3 P1
pub mod builtin; // Tasks 4-6
pub mod coe; // coercions
pub mod config; // setElabConfig
pub mod dispatch;
pub mod elab;
pub mod error;
mod postpone;
pub mod resolve; // Task 5
pub mod synthetic; // M4b-3 P2a

pub use elab::TermElabM;
pub use error::{
    AnonCtorError, ElabError, EliminatorErrorReason, InvalidDottedIdentReason, InvalidFieldReason,
    InvalidProjectionReason,
};
