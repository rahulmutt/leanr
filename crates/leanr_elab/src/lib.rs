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
//!   `App.lean:638-646` does.
//!   `MetaCtx::try_synth_instance` lets an `outParam` goal such as
//!   `Get Cell Nat ?elem` reach the real search (the out-param mvar is
//!   replaced before it and assigned after it), while a goal with an
//!   mvar in a NON-output position postpones when the search throws
//!   `IsDefEqStuck`. `Elab0.lean` grows the first
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
//!   `elabAppFn`) — landed. An overloaded IDENTIFIER or `.x` is elaborated:
//!   `app::head::elab_app_fn_resolutions` runs each candidate under
//!   `observing` and `app::overload::select` ports `getSuccesses` /
//!   `Ambiguous term` / `mergeFailures`; `.x` candidates go through
//!   the same path (`app/dot_ident.rs`).
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
//!   seam: `choice` choice-node parsing, private field projections the slice that models private
//!   names. The anonymous
//!   constructor `⟨⟩` is elaborated by `builtin::anon_ctor` (M4b-4b); its
//!   pattern position is left to the match slice.
//! - **macro expansion** — `elab_term_core` expands through the
//!   hand-ported table (`macros/`) before dispatch, as `elabTermAux`
//!   does. The table covers the `binop%` op family (24 rows) plus
//!   `∧ ∨ ¬ ↔ <->`; every other Init notation and all non-Init
//!   notations raise `UnsupportedSyntax(kind)` (table extension or the
//!   VM slice). The op family itself is elaborated by `builtin::op`
//!   (macro/binop% P3: `binop%`, `binop_lazy%`, `leftact%`, `rightact%`,
//!   `unop%`, `binrel%`, `binrel_no_prop%`).
//! - **`open`/alias/`_root_` resolution** — SHIPPED in M4c-2b-i
//!   (`resolve.rs`, `names.rs`, `command/scope.rs`): `resolve_global_name`
//!   is the oracle's candidate-list `resolveGlobalName` against the
//!   `ResolveCtx` on `TermElabM` (term-only callers get
//!   `ResolveCtx::root()`). Overloaded identifiers (two or more
//!   `resolveGlobalName` candidates) are elaborated; still deferred:
//!   `export`/`private` — later M4.
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
//! - **Stuck typeclass goals are detected dynamically by the search.**
//!   `MetaCtx::synth_instance` runs under `with_new_mctx_depth` with
//!   `isDefEqStuckEx` set, so a candidate that needs one of the caller's
//!   mvars assigned throws `MetaError::IsDefEqStuck`, and
//!   `MetaCtx::try_synth_instance` reports it as `.undef` exactly as the
//!   oracle's `trySynthInstance` does (the elab-side consumer is
//!   `synthetic/ladder.rs`'s match arm). So the ladder's `.undef` arm is
//!   reachable from a typeclass goal and bare `useWrap` errors
//!   `StuckSyntheticMVar`; `leanr_meta`'s own gate pins the bare
//!   `synth_instance` side in `tests/oracle_synth.rs`'s
//!   `exc_record_stuck_synth_0_is_stuck_in_leanr_too`. Goals the oracle
//!   answers answer here too: `outParam` goals (`Get Cell Nat ?elem`),
//!   an all-polymorphic candidate set (`tc/useAnyHole`), and a
//!   zero-candidate class with an mvar goal (`NoInst ?a` is `.none`, an
//!   `InstanceSynthesisFailed`, not stuck).
//! - **M4c-1** — command elaboration of ONE non-recursive
//!   `def`/`theorem`/`abbrev`/`opaque`/`axiom`/`example`, in `command/`:
//!   `DefView` (syntax + named seams), header (`expandDeclId`,
//!   `elabHeaders`), body (`elabFunValues`), level params
//!   (`levelMVarToParam*`, `sortDeclLevelParams`), the unassigned-mvar
//!   report (`unassigned.rs`), `abstractNestedProofs`, and commit through
//!   `Environment::add_decl_in` (an `example` is only kernel-checked).
//!   Gated by `tests/oracle_decl.rs` over `decl-queries.jsonl`
//!   (docs/superpowers/specs/2026-10-03-m4c1-single-decl-design.md).
//! - **M4c-2c-i** — scope universe names and section variables
//!   (`command/scope.rs`, `command/vars.rs`): the `universe`, `variable`,
//!   `include` and `omit` commands; scope level names threaded into
//!   `expandDeclId`, `fixLevelParams` and the async signature (whose
//!   level params `commitConst` compares with the finished theorem's); a faithful
//!   `runTermElabM` (each declaration re-elaborates the scope's binder
//!   syntax) and the three inclusion regimes — def/abbrev/opaque/example
//!   `withUsed`, theorem `withHeaderSecVars` (body in the restricted lctx,
//!   via `leanr_meta`'s additive `MetaCtx::erase_locals`), axiom
//!   `mkForallFVars (usedOnly := true)`. Gated by `tests/oracle_file.rs`
//!   (corpus 131 → 214;
//!   docs/superpowers/specs/2026-10-05-m4c2c-i-universe-variable-design.md).
//!   Auto-bound implicits in def/theorem/axiom headers landed in M4c-2c-ii
//!   P1 (`auto_bound`; corpus 308;
//!   docs/superpowers/specs/2026-10-05-m4c2c-ii-auto-bound-design.md
//!   § Landed). Auto-bound implicits in `variable` binders and
//!   `runTermElabM`'s mvar-rebuild branch (stale `sectionFVars`,
//!   faithfully) landed in P2 (corpus 376). Open seams: the
//!   `variable {α}` / `variable [x]` binder-annotation update (`replaceBinderAnnotation`, `— later M4`).
//!   Unmodelled: `commitConst`'s type-equality check (no known
//!   reproducer).
//!   Known rendering limits: `OmitUnmatched` prints the item's source text
//!   with whitespace collapsed, not the oracle's syntax formatter (a
//!   comment inside the brackets differs); `IncludeUndeclared` joins the
//!   id's components with `.`, so an escaped id (`«a.b»`) renders
//!   differently from the oracle; `OmitUndeclared` for an mvar binder or an
//!   anonymous instance prints leanr's binder name, not the oracle's
//!   hygienic hash name.
pub mod app; // M4b-3 P1
mod auto_bound; // M4c-2c-ii
pub mod builtin; // Tasks 4-6
pub mod coe; // coercions
pub mod command; // M4c-1 P2
pub mod config; // setElabConfig
pub mod dispatch;
pub mod elab;
pub mod error;
pub mod macros; // macro/binop% P2
pub mod names; // M4c-2b-i
mod postpone;
pub mod resolve; // Task 5
pub mod synthetic; // M4b-3 P2a
#[cfg(test)]
mod test_support;
mod unassigned; // M4c-1 P2 Task 4

pub use elab::TermElabM;
pub use error::{
    AnonCtorError, AppArgMismatch, ElabError, EliminatorErrorReason, InvalidDottedIdentReason,
    InvalidFieldReason, InvalidProjectionReason,
};
