//! M4b-3 P1: the application elaborator. Oracle: `Lean/Elab/App.lean`'s
//! `ElabAppArgs` namespace. See
//! docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md
//! § P1 — the application machinery.
//!
//! IN this plan, so NOT seams (Task 9's reconciliation of this list
//! against what P1 actually shipped): explicit arguments, implicit and
//! strict-implicit insertion, `propagateExpectedType`, named arguments,
//! eta-expansion, the `..` ellipsis (task 7 — `args.rs`'s
//! `if app.ctx.ellipsis { add_implicit_arg }`, oracle `App.lean:856-857`),
//! `@` explicit mode, and `.{u}` explicit universes. **Also no longer a
//! seam, as of M4b-3 P2a task 7**: instance-implicit arguments
//! (`args.rs`'s `process_inst_implicit_arg`/`mk_inst_mvar`) and the
//! three pending-`inst_mvars` guards (`AppElab::try_synthesize_app_inst_mvars`
//! / `synthesize_app_inst_mvars`, called from `propagate.rs` and
//! `finalize.rs` at exactly the oracle's own call sites) — both rows
//! this doc used to carry in the seam table below. **Also no longer a
//! seam, as of M4b-3 P2b-ii**: the local-instance outParam result type —
//! `args.rs`'s `is_next_out_param_of_local_instance_and_result` is the
//! `resultTypeOutParam?` producer and `finalize.rs`'s branch is its
//! consumer (`App.lean:681-727`, `:638-646`), gated by `Elab0.lean`'s
//! `Lean.Internal.coeM` exactly as the oracle's `App.lean:1355` gates
//! it. `tests/seam_audit.rs`'s `no_seam_points_at_the_retired_p2b_ii_label`
//! gates that its message never comes back.
//!
//! NOT in this plan, each a named seam (never a silent fall-through).
//! `Where` is the site that raises it; every message below carries its
//! owning slice, and `tests/seam_audit.rs` asserts that. Reconciled by
//! M4b-3 P2a task 10 against what P2a actually shipped: the
//! instance-implicit arm and the three `inst_mvars` guards this table
//! used to carry as P2 rows are gone (real code — see above), and the
//! "too many args" row closed its P2 half and now splits P4/P5.
//! Reconciled AGAIN by M4b-3 P3 task 8: the row that listed the three
//! non-leaf literal kinds as P3's, not routed by `dispatch.rs`, is gone
//! too. (Its exact wording is deliberately NOT quoted here — the gate
//! below is a text scan, and a doc that reproduces a retired row's text
//! is indistinguishable from the row itself.) All three kinds ARE routed
//! now (`dispatch.rs`'s own table, tasks 6-7) and the rung-3
//! default-instance seam they depended on has
//! a real body in `synthetic/default_inst.rs`, so the row was a stale
//! claim rather than a seam — `tests/seam_audit.rs`'s
//! `literal_kinds_are_registered_not_deferred` gates that it stays gone.
//!
//! ```text
//!   fType still an unassigned mvar after synthesis ... P4/P5 args.rs (`main`'s
//!     synthesize_pending_and_normalize_fun_type) — CoeFun (P4) or
//!     expected-type propagation into `fun` binder domains (P5). A
//!     genuinely non-function fType at the same site is NOT a seam: it
//!     reports `ElabError::FunctionExpected`, matching the oracle's own
//!     diagnostic (`over_application_reports_function_expected`,
//!     `tests/seam_audit.rs`).
//!   coercions (CoeT/CoeFun/CoeSort, mkCoe) ........... P4  args.rs (ensureArgType)
//!   optParam defaults / autoParam .................... P5  args.rs
//!   implicit-lambda insertion ........................ P5  elab.rs, and `@t`/`@(t)` here
//!   overload resolution (candidates > 1) ............. resolve_global slice  overload.rs
//!   elabAsElim, RECURSOR heads only (partial!) ....... M4b-4 head.rs
//!   dot notation, LVal machinery ..................... M4b-4 head.rs, here, dispatch.rs
//!   numImplicitParams (structure projection) ......... M4b-4 args.rs
//! ```
//!
//! **The `elabAsElim` row is a PARTIAL seam, and the only row in this
//! table that does not cover its own construct.** `shouldElabAsElim`
//! (`App.lean:1322-1328`) has five disjuncts; `head::elab_ident_head`
//! can decide exactly one of them (`isRec`, i.e. `ConstantInfo::Rec`),
//! because the other four read the `auxRecExt` / `elabAsElim` tag
//! extensions, which leanr does not decode. So a genuine recursor head
//! (`Nat.rec`, `List.rec`) is seamed, and an AUX recursor head
//! (`Nat.casesOn`, `Nat.recOn`, `Nat.brecOn`) or an
//! `@[elab_as_elim]`-tagged head is NOT — it still takes the ordinary
//! path and still emits a term the oracle does not, with no seam. That
//! is a known open divergence M4b-4 owns; `tests/seam_audit.rs`'s
//! `fixture_declares_no_undecoded_elab_attributes` is the source-text
//! backstop keeping it out of the committed corpus in the meantime.
//!
//! Two of those are not reachable from any source term the hermetic
//! `Elab0` fixture can express, and `tests/seam_audit.rs` records why
//! rather than pretending otherwise (a THIRD, the P2 instance-implicit
//! seams, no longer belongs on this list as of M4b-3 P2a task 7:
//! `Elab0.lean` now declares `Wrap`/`Pair`/`NoInst`/`Dflt`, and
//! `args.rs`'s `InstImplicit` arm and the three `inst_mvars` guards are
//! real code, exercised by `tests/oracle_elab.rs`'s `tc/*` records and
//! `tests/synthetic_smoke.rs`):
//!   * the P5 optParam/autoParam seam — no fixture parameter carries
//!     either wrapper, so it is asserted white-box instead
//!     (`app_smoke.rs`'s `explicit_mode_skips_the_optparam_default`);
//!   * the P4 coercion seam, which is an `ElabError::TypeMismatch` from
//!     `elab_and_add_new_arg`'s `ensureArgType` rather than an
//!     `UnsupportedSyntax` — that IS M4b-1's documented behavior (error
//!     on a defeq mismatch instead of inserting a coercion), so it is a
//!     deliberate wrong-shaped seam, not a missing one.

pub mod args;
pub mod expand;
pub mod finalize;
pub mod head;
pub mod overload;
pub mod propagate;
pub mod state;

use leanr_kernel::bank::{ExprId, LevelId};
use leanr_syntax::kind::KindInterner;
use leanr_syntax::tree::SyntaxNode;

use crate::app::expand::{Arg, NamedArg};
use crate::app::state::{Context, State};
use crate::dispatch::{non_trivia_children, SynElem};
use crate::elab::TermElabM;
use crate::error::ElabError;

/// oracle: `elabApp` (`App.lean:2238-2241`) — `universeConstraintsCheckpoint`
/// wraps the whole thing, running `processPostponed` (leanr_meta's
/// postponed level-constraint queue) after every single `elabApp` call.
/// leanr does not checkpoint per call here: P2a's
/// `process_postponed_universe_constraints` (`synthetic/ladder.rs`) drains the
/// same queue at the end of `synthesize_synthetic_mvars_no_postponing`'s
/// fixpoint — and that fixpoint itself runs more than once per term
/// under the gate as wired (`TermElabM::elab_term_and_synthesize`,
/// `elab.rs`, calls it once at the top level, but ascription's `(e :)`
/// arm calls `with_synthesize(No, ..)` internally too, which drains the
/// queue again) — a coarser grain than the oracle's own per-application
/// checkpoint, and not a single drain. No corpus record distinguishes
/// the two today.
pub fn elab_app(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let (head, named_args, args, ellipsis) = expand::expand_app(node, kinds)?;
    // The WHOLE application syntax — the oracle's ambient `getRef` for
    // everything `elab_app_aux` runs (`Context::stx`'s own doc). Taken
    // from `node` itself, before `expand_app`'s `head` narrows to just
    // the function part.
    let stx = SynElem::Node(node.clone());
    elab_app_aux(
        elab, &head, kinds, named_args, args, ellipsis, expected, stx,
    )
}

/// oracle: `elabAtom` (`App.lean:2243-2244`) — a zero-argument
/// application. This is what `ident`, `@`, `.{u}`, `choice`, `proj` and
/// `dotIdent` all reduce to in the oracle; P1 routes the first three.
pub fn elab_atom(
    elab: &mut TermElabM,
    elem: &SynElem,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    // Zero arguments: the whole application IS `elem` itself, so it is
    // also the `Context::stx` the oracle's ambient `getRef` would see.
    let stx = elem.clone();
    elab_app_aux(
        elab,
        elem,
        kinds,
        Vec::new(),
        Vec::new(),
        false,
        expected,
        stx,
    )
}

/// oracle: `elabExplicit` (`App.lean:2260-2271`), the `@`-in-TERM-
/// position elaborator. It is a pure shape dispatch over seven
/// `elabAtom` forms and two `elabTerm .. (implicitLambda := false)`
/// forms:
///
/// ```text
/// | `(@$_:ident)               => elabAtom stx expectedType?
/// | `(@$_:ident.{$_us,*})      => elabAtom stx expectedType?
/// | `(@$(_).$_:fieldIdx)       => elabAtom stx expectedType?
/// | `(@$(_).$_:ident)          => elabAtom stx expectedType?
/// | `(@$(_).$_:ident.{$_us,*}) => elabAtom stx expectedType?
/// | `(@.$_:ident)              => elabAtom stx expectedType?
/// | `(@.$_:ident.{$_us,*})     => elabAtom stx expectedType?
/// | `(@($t))                   => elabTerm t expectedType? (implicitLambda := false)
/// | `(@$t)                     => elabTerm t expectedType? (implicitLambda := false)
/// ```
///
/// P1 implements the first family and NAMES the other two, because
/// `@t` exists precisely to disable implicit-lambda insertion (P5's) —
/// so routing it to `elab_atom` would not merely be incomplete, it
/// would enter explicit mode the oracle never enters.
///
/// The `.field` forms are the LVal machinery (M4b-4); in leanr's tree
/// a dotted name like `@Nat.succ` is a single `<ident>` TOKEN
/// (`leanr_syntax::lex`'s `hierarchical_idents_are_one_token`), so only
/// a genuine projection off a non-identifier base reaches that seam.
///
/// Note this passes the WHOLE `@..` node to `elab_atom`, exactly as the
/// oracle passes `stx` (not `stx[1]`): `elabAppFn` is what strips the
/// `@`, and `peel_head` below is leanr's transliteration of that.
pub fn elab_explicit(
    elab: &mut TermElabM,
    elem: &SynElem,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let inner = explicit_inner(elem)?;
    match kinds.name(inner.kind()) {
        "<ident>" | "Lean.Parser.Term.explicitUniv" => elab_atom(elab, elem, kinds, expected),
        "Lean.Parser.Term.proj" | "Lean.Parser.Term.dotIdent" => Err(ElabError::UnsupportedSyntax(
            "`@` on a projection / dot-identifier head — dot notation / LVal \
             machinery is M4b-4"
                .to_string(),
        )),
        other => Err(ElabError::UnsupportedSyntax(format!(
            "`@` applied to `{other}` does not enter explicit mode — it DISABLES \
             implicit-lambda insertion (App.lean:2269-2270) — M4b-3 P5"
        ))),
    }
}

/// The single non-trivia child after the `@` atom of a
/// `Lean.Parser.Term.explicit` node (`term.rs`'s own registration:
/// `seq([sym("@"), cat("term", MAX_PREC)])`, so the layout is exactly
/// `[<atom "@">, <inner term>]` — the oracle's `f.getArg 1`,
/// `App.lean:2117`).
fn explicit_inner(elem: &SynElem) -> Result<SynElem, ElabError> {
    let node = elem.as_node().ok_or_else(|| {
        ElabError::IllFormedSyntax("`@`: Term.explicit is not a node".to_string())
    })?;
    non_trivia_children(node)
        .into_iter()
        .nth(1)
        .ok_or_else(|| ElabError::IllFormedSyntax("`@`: no term after `@`".to_string()))
}

/// The base term and the level syntaxes of a
/// `Lean.Parser.Term.explicitUniv` node. Layout (confirmed by a
/// throwaway parse probe, never landed — same precedent as
/// `expand.rs`'s own recorded shapes):
///
/// ```text
/// List.{0, 0}:
///   [0] <ident> "List"
///   [1] <atom>  ".{"
///   [2] null    "0, 0"     <- sepBy1's own wrapper
///         [0] num "0"
///         [1] <atom> ","
///         [2] num "0"
///   [3] <atom>  "}"
/// ```
///
/// The separator atoms live in the `null` wrapper alongside the levels,
/// so the levels are its EVEN-indexed children — the oracle's own
/// `Syntax.getSepArgs` (`$us,*` in `App.lean:2103`'s quotation pattern
/// expands to `getSepArgs`, which takes `args[0], args[2], ..`), not a
/// kind filter invented here.
fn explicit_univ_parts(elem: &SynElem) -> Result<(SynElem, Vec<SynElem>), ElabError> {
    let node = elem.as_node().ok_or_else(|| {
        ElabError::IllFormedSyntax("`.{u}`: Term.explicitUniv is not a node".to_string())
    })?;
    let ch = non_trivia_children(node);
    let inner = ch
        .first()
        .cloned()
        .ok_or_else(|| ElabError::IllFormedSyntax("`.{u}`: no base term".to_string()))?;
    let list = ch
        .get(2)
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::IllFormedSyntax("`.{u}`: no level list".to_string()))?;
    let lvls = non_trivia_children(list).into_iter().step_by(2).collect();
    Ok((inner, lvls))
}

/// oracle: the head-WRAPPER arms of `elabAppFn` — `@` (`App.lean:2110-2118`)
/// and `.{us}` (`App.lean:2103-2105`) — peeled here rather than inside
/// `head.rs`, which stays about NAMES only. `@f a b` and `f.{u} a` wrap
/// the SAME head syntax the plain form has, so stripping the wrapper
/// (setting `explicit := true` / collecting the explicit level list)
/// before `elab_app_fn` is exactly what the oracle's own recursion does.
///
/// ORDER is the oracle's: `@` is stripped FIRST (`App.lean:2117` recurses
/// on `f.getArg 1` with `explicit := true`), and the recursive call is
/// what then matches `` `($id:ident.{$us,*}) `` — which is also the order
/// leanr's tree has (`@List.{0}` parses as `explicit(explicitUniv(..))`).
///
/// `@` applied to anything outside the seven `elabAtom` shapes is
/// `App.lean:2118`'s `` `(@$_) => throwUnsupportedSyntax `` — an INVALID
/// occurrence of `@` in a function position, NOT the implicit-lambda-
/// disabling form (that one is only reachable when the `@..` node is the
/// whole term, i.e. through `elab_explicit` above).
fn peel_head(
    elab: &mut TermElabM,
    head: &SynElem,
    kinds: &KindInterner,
) -> Result<(SynElem, bool, Vec<LevelId>), ElabError> {
    let mut cur = head.clone();
    let mut explicit = false;
    if kinds.name(cur.kind()) == "Lean.Parser.Term.explicit" {
        cur = explicit_inner(&cur)?;
        explicit = true;
        match kinds.name(cur.kind()) {
            "<ident>" | "Lean.Parser.Term.explicitUniv" => {}
            "Lean.Parser.Term.proj" | "Lean.Parser.Term.dotIdent" => {
                return Err(ElabError::UnsupportedSyntax(
                    "`@` on a projection / dot-identifier head — dot notation / LVal \
                     machinery is M4b-4"
                        .to_string(),
                ))
            }
            other => {
                return Err(ElabError::UnsupportedSyntax(format!(
                    "invalid occurrence of `@` in a function position (`{other}`) \
                     — App.lean:2118"
                )))
            }
        }
    }
    let mut explicit_levels = Vec::new();
    if kinds.name(cur.kind()) == "Lean.Parser.Term.explicitUniv" {
        let (inner, lvls) = explicit_univ_parts(&cur)?;
        explicit_levels = head::elab_explicit_univs(elab, &lvls, kinds)?;
        cur = inner;
    }
    Ok((cur, explicit, explicit_levels))
}

/// oracle: `elabAppAux` (`App.lean:2202-2217`) resolving the head, then
/// `elabAppArgs` (`App.lean:1351-1394`) building the `Context`/`State`
/// the loop runs over.
///
/// Task 8 peels `@` and `.{u, v}` HERE, not in `head.rs` (`peel_head`
/// above): `@f a b` and `f.{u} a` wrap the SAME head syntax the plain
/// form has, so stripping the wrapper (setting `explicit := true` /
/// collecting the explicit level list) before `elab_app_fn` keeps
/// `head.rs` about NAMES only. `elab_app_fn` still names any remaining
/// non-`ident` head as an M4b-4 seam rather than mis-elaborating it.
///
/// Task 7 adds the 8th parameter (`stx`, `Context::stx`'s own doc),
/// crossing clippy's default `too_many_arguments` threshold (7). Same
/// judgment call as `MetaCtx::new`'s own precedent
/// (`leanr_meta/src/metactx.rs`): this constructor-shaped private
/// helper has exactly one call style (both call sites — `elab_app`,
/// `elab_atom` — pass every parameter positionally), so a
/// builder/params-struct layer here would be a bigger refactor than
/// this task's own scope for no real call-site simplification.
#[allow(clippy::too_many_arguments)]
fn elab_app_aux(
    elab: &mut TermElabM,
    head: &SynElem,
    kinds: &KindInterner,
    named_args: Vec<NamedArg>,
    args: Vec<Arg>,
    ellipsis: bool,
    expected: Option<ExprId>,
    stx: SynElem,
) -> Result<ExprId, ElabError> {
    let (head, explicit, explicit_levels) = peel_head(elab, head, kinds)?;
    // `heed_elab_as_elim = !explicit && !ellipsis` — the oracle's own
    // early-out at `App.lean:1399` (`if explicit || ellipsis then return
    // none`), so `@Nat.rec` and `Nat.rec ..` take the ordinary path on
    // BOTH sides. See `head::elab_app_fn`'s own doc comment.
    let candidates =
        head::elab_app_fn(elab, &head, kinds, &explicit_levels, !explicit && !ellipsis)?;
    let f = overload::expect_single(candidates)?;

    // oracle: `elabAppArgs`'s first two lines — `let fType ← inferType f;
    // let fType ← instantiateMVars fType`.
    let f_type = elab.mctx.infer_type(f)?;
    let f_type = elab.mctx.instantiate_mvars(f_type)?;

    // oracle: `App.lean:1373`'s `if let some elimInfo ← elabAsElim? then
    // .. ElabElim.main ..` branch, which diverts the WHOLE application
    // to the eliminator elaborator. leanr never takes it — it elaborates
    // the ordinary way or raises a seam.
    //
    // Task 9 correction — the branch is NOT attribute-only, and the plan
    // said it was. `elabAsElim?` (`App.lean:1397-1401`) calls
    // `shouldElabAsElim` (`:1322-1328`), which is
    //   `isRec declName || isCasesOnRecursor env declName
    //    || isBRecOnRecursor env declName || isRecOnRecursor env declName
    //    || elabAsElim.hasTag env declName`
    // — the `@[elab_as_elim]` tag is only the LAST of five triggers.
    // This is live in the hermetic fixture, not hypothetical: measured
    // against the pinned oracle through `dump_elab.lean`'s own entry
    // point, `Nat.rec`, `Nat.recOn` and `Nat.casesOn` each elaborate to
    // a bare `?m` there (the branch postpones on the missing expected
    // type), where leanr emitted `const Nat.rec [?u]`.
    //
    // Fix round 1 splits that finding by what leanr can DECIDE:
    //   * `isRec` is a plain constant-kind test and leanr's environment
    //     carries `ConstantInfo::Rec`, so `head::elab_ident_head` now
    //     raises a named M4b-4 seam for a genuine recursor head. The
    //     `explicit || ellipsis` early-out (`App.lean:1399`) is honoured
    //     — `heed_elab_as_elim` below — so `@Nat.rec` and `Nat.rec ..`
    //     still take the ordinary path, exactly as the oracle does;
    //   * the three `is*Recursor`s read `auxRecExt` and the tag reads
    //     `elabAsElim`, two extensions leanr does not decode. Those four
    //     disjuncts are STILL UNGUARDED: an aux-recursor head
    //     (`Nat.casesOn`, `Nat.recOn`, `Nat.brecOn`) or an
    //     `@[elab_as_elim]` head takes the ordinary path here and emits
    //     a term the oracle does not, with no seam.
    //
    // No committed record covers an eliminator-headed query, and
    // `seam_audit.rs`'s `fixture_declares_no_undecoded_elab_attributes`
    // gates BOTH remaining halves — the attribute in `Elab0.lean` and an
    // eliminator-shaped name in `elab-queries.jsonl` — so the residual
    // divergence cannot be committed without the gate failing first.
    // The complete guard needs the extension decodes and `ElabElim`
    // itself: M4b-4 owns it.
    let ctx = Context {
        ellipsis,
        explicit,
        // oracle: `App.lean:1355`'s `env.contains ``Lean.Internal.coeM &&
        // resultIsOutParamSupport && !explicit`. Computed the same way,
        // not shortcut to `true`: `Lean.Internal.coeM` is declared
        // since M4b-3 P2b-ii, so it is `true` for every non-`@`
        // application in the fixture corpus; computing it rather than
        // shortcutting stays the rule.
        result_is_out_param_support: env_contains_coe_m(elab)? && !explicit,
        // oracle: `Context.numImplicitParams` — the max over `namedArgs`.
        num_implicit_params: named_args
            .iter()
            .map(|n| n.num_implicit_params)
            .max()
            .unwrap_or(0),
        stx,
    };
    let st = State {
        f,
        f_type,
        f_args: Vec::new(),
        args,
        named_args,
        expected_type: expected,
        eta_args: Vec::new(),
        to_set_error_ctx: Vec::new(),
        inst_mvars: Vec::new(),
        // oracle: `propagateExpectedTypeFor f` (`App.lean:1330-1333`,
        // called at `:1393`) is `!hasElabWithoutExpectedType env declName`
        // — and unlike `shouldElabAsElim` above, this one really IS
        // attribute-only (`App.lean:28-32`: a single `TagAttribute`
        // lookup). leanr does not decode that extension, so this is
        // `true` for every head, which is the attribute's own default;
        // `seam_audit.rs`'s fixture-source gate is what keeps that
        // default correct by keeping `@[elab_without_expected_type]` out
        // of `Elab0.lean`.
        propagate_expected: true,
        result_type_out_param: None,
        found_named_args: Vec::new(),
    };
    let mut app = state::AppElab { ctx, st, elab };
    // Bracket the whole loop (M4b-2's `binder.rs:217,226` idiom):
    // `args::add_eta_arg` pushes one fvar per eta-expanded parameter
    // into the ambient `lctx`, and `finalize`'s `mkLambdaFVars`
    // abstracts them back out — but only on the success path. Restoring
    // on EVERY exit is what keeps an eta fvar (or one left behind by a
    // failed argument elaboration) from leaking into the context a
    // caller goes on to elaborate in. The oracle gets this for free from
    // `withLocalDeclD`'s scoping in `addEtaArg`; leanr's
    // `push_local_decl` is unscoped, so the bracket is explicit.
    let checkpoint = app.elab.mctx.lctx_checkpoint();
    let result = args::main(&mut app, kinds);
    app.elab.mctx.lctx_restore(checkpoint);
    result
}

/// oracle: `env.contains ``Lean.Internal.coeM` (`App.lean:1355`). The
/// name has to be interned before it can be looked up — `EnvView` is
/// id-native and has no by-string entry point — which is exactly what
/// `head::intern_dotted` does, `base = Some(view.store)` so an already
/// declared constant's PERSISTENT `NameId` is found rather than shadowed
/// by a fresh scratch row `EnvView::get` would never resolve.
fn env_contains_coe_m(elab: &mut TermElabM) -> Result<bool, ElabError> {
    let name = head::intern_dotted(elab, "Lean.Internal.coeM")?;
    Ok(elab.view.get(name).is_some())
}
