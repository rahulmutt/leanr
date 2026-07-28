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
//!   ladder, `synthetic.rs`) and instance-implicit arguments
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
//!   those are P2b, still a named seam below.
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
//!   and `State.resultTypeOutParam?` exist (P1), and P2a's
//!   `synthesizeAppInstMVars`/`synthesizeSyntheticMVarsUsingDefault` are
//!   the callees `finalize`'s outParam branch needs — but nothing yet
//!   *produces* a `resultTypeOutParam?`, because that needs a
//!   `classExtension` decode (`ClassEntry` = name + outParam positions)
//!   `leanr_olean` does not have. `app/args.rs`'s `add_implicit_arg` and
//!   `app/finalize.rs`'s outParam branch each raise this as a named seam
//!   — M4b-3 P2b.
//! - **`num`/`char` literals** — deliberately *not* leaves (an M4b-1
//!   spec correction): both elaborate through an application
//!   (`OfNat.ofNat`/`Char.ofNat`) requiring instance synthesis and
//!   default instances — M4b-3 P3.
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
//! Two things below ARE built — neither is a named seam — but each has
//! a known hole in what the corpus can currently prove about it.
//! Recording the hole here is the alternative to either leaving it to
//! be rediscovered or quietly asserting more coverage than exists.
//!
//! - **`resumePostponed`'s success path has no differential coverage
//!   yet.** P2a builds the whole ladder, and its stuck paths are
//!   asserted in `tests/synthetic_smoke.rs` — but every term in P2a's
//!   grammar that postpones also ends stuck (the only producer is
//!   `App.lean:1367`'s `tryPostponeIfMVar fType`; every other
//!   `tryPostpone*` site belongs to M4b-4, P3, P5 or later M4). The
//!   first term that postpones and then RESUMES into a term arrives
//!   with P3's numerals. Recorded rather than papered over: the corpus
//!   does not cover this path today.
//! - **`leanr_meta` cannot report a stuck typeclass goal.**
//!   `leanr_meta::error::MetaError` declares `IsDefEqStuck` (`error.rs:36`)
//!   but constructs it nowhere; `synth.rs`'s `synthesize_inst_mvar_core`
//!   (its own doc comment, `synth.rs:1636-1650`) documents
//!   `isDefEqStuckEx` (`Meta/Basic.lean` in the pinned oracle) as a named
//!   seam because tier-1 `leanr_meta` has no mctx-depth / read-only-mvar
//!   model with which to DECIDE stuck-vs-assignable. The consequence,
//!   measured rather than assumed: `synth_instance(Wrap ?m)` *succeeds*
//!   in leanr, assigning `?m := Nat` from the class's sole candidate,
//!   where the pinned oracle refuses and reports the goal stuck. So the
//!   ladder's `.undef` trichotomy arm (`synthetic.rs`'s
//!   `synthesize_inst_mvar_core`) is unreachable from a typeclass goal —
//!   `reportStuckSyntheticMVars` can never fire from one — and
//!   `useWrap` bare (a class instance parameter left as a bare hole)
//!   succeeds in leanr where the oracle errors. This is **not** a
//!   record divergence: `dump_elab.lean`'s dumper drops any query whose
//!   oracle side throws, so no corpus record covers it, which is
//!   exactly why it is written down here instead of left to be
//!   rediscovered. Three groups of tests in
//!   `tests/synthetic_smoke.rs` are `#[ignore]`d on this basis, and
//!   Task 9's entry-point test had to be reshaped around it. This
//!   unblocks: differential coverage of the ladder's stuck-report path
//!   from a typeclass goal, and a correct `useWrap`-bare seam. Owner:
//!   whichever slice gives `leanr_meta` an mctx-depth / read-only-mvar
//!   model — not scoped to any M4b-3 sub-slice today.
pub mod app; // M4b-3 P1
pub mod builtin; // Tasks 4-6
pub mod dispatch;
pub mod elab;
pub mod error;
pub mod resolve; // Task 5
pub mod synthetic; // M4b-3 P2a

pub use elab::TermElabM;
pub use error::ElabError;
