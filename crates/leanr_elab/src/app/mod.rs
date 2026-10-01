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
//! gates that its message never comes back. **Also no longer a seam, as
//! of M4b-3 P5**: the `fType` still-an-unassigned-mvar row (task 4 —
//! `propagateExpectedType`, `builtin/binder/fun.rs`, now pins a `fun`
//! binder's domain from its ascription before `app/args.rs` can ever
//! see an unassigned mvar there; what remains is a genuine
//! `FunctionExpected`, `tests/seam_audit.rs`'s
//! `mvar_function_type_is_closed_by_propagation`), `optParam`/`autoParam`
//! default filling (tasks 8-9 — `app/args.rs`'s `opt_param_default`/
//! `auto_param_tactic`/`mk_tactic_mvar`, real code exercised by
//! `tests/oracle_elab.rs`'s `p5/*` records now that `Elab0.lean`
//! declares `withDefault`/`withTactic`), and implicit-lambda insertion
//! ITSELF (tasks 5-6 — `elab.rs`'s `use_implicit_lambda`/
//! `elab_implicit_lambda`). The M4b-3 close-out then closed the
//! `@($t)`/`@$t` wrap that elaborates with insertion explicitly disabled
//! (`elab_explicit`).
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
//!   coercions (CoeT/CoeFun/CoeSort, mkCoe) ........... P4 SHIPPED — coe.rs, args.rs
//!   optParam defaults / autoParam .................... P5 SHIPPED — args.rs
//!   implicit-lambda insertion (the feature) .......... P5 SHIPPED — elab.rs
//!   `@($t)`/`@$t` disabling implicit-lambda insertion . SHIPPED (close-out) — here, elab.rs
//!   overload resolution (candidates > 1) ............. resolve_global_name slice  overload.rs
//!   elabAsElim, RECURSOR heads only (partial!) ....... M4b-4c head.rs
//!   dot notation: proj, fieldIdx, projFn/projIdx ..... P1 SHIPPED (M4b-4a) — lval.rs, head.rs, here
//!   numImplicitParams (structure projection) ......... P1 SHIPPED (M4b-4a) — args.rs, lval.rs
//!   generalized field notation (.const, Function.f) .. P3 SHIPPED (M4b-4a) — lval.rs
//!   pipeProj / dotIdent / namedPattern heads, `@.f` .. P4 SHIPPED (M4b-4a) — head.rs, dot_ident.rs
//!   `choice` heads ................................... overloading slice  head.rs
//!   private field projections ........................ private-names slice  lval.rs
//! ```
//!
//! **The `elabAsElim` row is a PARTIAL seam, and the only row in this
//! table that does not cover its own construct.** `shouldElabAsElim`
//! (`App.lean:1322-1328`) has five disjuncts; `head::elab_app_fn_id`
//! can decide exactly one of them (`isRec`, i.e. `ConstantInfo::Rec`),
//! because the other four read the `auxRecExt` / `elabAsElim` tag
//! extensions, which leanr does not decode. So a genuine recursor head
//! (`Nat.rec`, `List.rec`) is seamed, and an AUX recursor head
//! (`Nat.casesOn`, `Nat.recOn`, `Nat.brecOn`) or an
//! `@[elab_as_elim]`-tagged head is NOT — it still takes the ordinary
//! path and still emits a term the oracle does not, with no seam. That
//! is a known open divergence M4b-4c owns; `tests/seam_audit.rs`'s
//! `fixture_declares_no_undecoded_elab_attributes` is the source-text
//! backstop keeping it out of the committed corpus in the meantime.
//!
//! Historically this doc also tracked seams unreachable from any source
//! term the hermetic `Elab0` fixture could express — the P2
//! instance-implicit seams (closed as of M4b-3 P2a task 7: `Elab0.lean`
//! now declares `Wrap`/`Pair`/`NoInst`/`Dflt`, real code exercised by
//! `tests/oracle_elab.rs`'s `tc/*` records and `tests/synthetic_smoke.rs`),
//! the P4 coercion seam (closed as of M4b-3 P4: `coe.rs`'s `mk_coe`/
//! `ensure_has_type`/`ensure_type` shipped, so `elab_and_add_new_arg`'s
//! `ensureArgType` inserts a `CoeT` coercion on a defeq mismatch instead
//! of erroring), and the P5 `optParam`/`autoParam` seam (closed as of
//! M4b-3 P5 tasks 8-9: `Elab0.lean` now declares `withDefault`/
//! `withTactic` and both wrappers have real fixture coverage —
//! `tests/oracle_elab.rs`'s `p5/optparam-*`/`p5/autoparam-*` records —
//! so "no fixture parameter carries either wrapper" is no longer true;
//! `app_smoke.rs`'s `explicit_mode_skips_the_optparam_default` stays as
//! a white-box test of the `explicit == true` shape specifically, which
//! no fixture declaration reaches either way, not as a seam assertion).
//! All three are gone from the table above; none of the rows remaining
//! in it are unreachable from fixture source.

pub mod args;
pub mod dot_ident;
pub mod elim;
pub mod elim_info;
pub mod expand;
pub mod finalize;
pub mod head;
pub mod lval;
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
/// `dotIdent` all reduce to in the oracle; leanr routes the first three,
/// `proj` (since M4b-4a P1) and `dotIdent` (since P4).
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

/// oracle: `elabPipeProj` (`App.lean:2250-2258`). `$e |>.$f$[.{us}]? args*`
/// is `elabAppAux` on `$e |>.$f$[.{us}]?` with the trailing arguments
/// expanded (`expandArgs`); `head::elab_app_fn`'s pipeProj arm then reads
/// only `e`, `f` and the levels. The node is passed on intact as `stx`
/// rather than rebuilt without its arguments, and the pipeProj arm uses
/// `stx` to tell this node from a nested pipeProj that still carries its
/// own arguments. `universeConstraintsCheckpoint` is not per-call, as for
/// `elab_app`.
pub fn elab_pipe_proj(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let ch = non_trivia_children(node);
    let args_node = ch
        .get(4)
        .and_then(|el| el.as_node())
        .ok_or_else(|| ElabError::IllFormedSyntax("pipeProj: no argument list".to_string()))?;
    let items = non_trivia_children(args_node);
    let (named_args, args, ellipsis) = expand::expand_args(&items, kinds)?;
    let elem = SynElem::Node(node.clone());
    elab_app_aux(
        elab,
        &elem,
        kinds,
        named_args,
        args,
        ellipsis,
        expected,
        elem.clone(),
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
/// P1 implemented the first family; the M4b-3 close-out implemented the
/// last two, which elaborate `t` through
/// `TermElabM::elab_term_without_implicit_lambda`. `@t` exists precisely
/// to disable implicit-lambda insertion, so routing it to `elab_atom`
/// would enter explicit mode the oracle never enters.
///
/// Since M4b-4a P1 task 7 the projection forms (`@(e).1`, `@(e).f`,
/// `@(e).f.{us}`) are `elab_atom` too, and reach `head::elab_app_fn`'s
/// proj arm with `explicit := true`; since M4b-4a P4 so are the `@.f` /
/// `@.f.{us}` dot-identifier forms, which reach its dotIdent arm. The
/// table has NO `@$(_).$_:fieldIdx.{us}`
/// row, so `@(e).1.{us}` falls to the `` `(@$t) `` arm here, like any
/// other term — see `explicit_head_shape`. In leanr's tree a dotted name
/// like `@Nat.succ` is a single `<ident>` TOKEN
/// (`leanr_syntax::lex`'s `hierarchical_idents_are_one_token`), so it is
/// the ident row, never a projection.
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
    match explicit_head_shape(&inner, kinds)? {
        ExplicitHead::Atom => elab_atom(elab, elem, kinds, expected),
        // oracle: `` `(@($t)) `` / `` `(@$t) `` => `elabTerm t expectedType?
        // (implicitLambda := false)` (`App.lean:2269-2270`). One arm for
        // both: handed the `paren` node itself,
        // `elab_term_without_implicit_lambda` carries the flag through the
        // parentheses to `t`, which is what the `@($t)` arm does by matching
        // `t` out of them.
        ExplicitHead::Other => elab.elab_term_without_implicit_lambda(&inner, kinds, expected),
    }
}

/// Which of the oracle's `@` head rows the term after `@` matches. The
/// rows are the same seven in `elabAppFn` (`App.lean:2110-2116`) and
/// `elabExplicit` (`App.lean:2262-2268`):
///
/// ```text
/// @$_:ident   @$_:ident.{us}                          -> Atom
/// @$(_).$_:fieldIdx   @$(_).$_:ident   @$(_).$_:ident.{us} -> Atom
/// @.$_:ident  @.$_:ident.{us}                          -> Atom
/// ```
///
/// There is NO `@$(_).$_:fieldIdx.{us}` row, so `@(e).1.{us}` is
/// `Other` (measured on the pinned oracle: `unexpected syntax` in a
/// function position, and the `` `(@$t) `` arm's success in a term
/// position — `lval_smoke.rs`'s
/// `explicit_on_projection_heads_matches_the_oracle`).
enum ExplicitHead {
    Atom,
    Other,
}

fn explicit_head_shape(inner: &SynElem, kinds: &KindInterner) -> Result<ExplicitHead, ElabError> {
    let (base, has_univs) = if kinds.name(inner.kind()) == "Lean.Parser.Term.explicitUniv" {
        (explicit_univ_parts(inner)?.0, true)
    } else {
        (inner.clone(), false)
    };
    Ok(match kinds.name(base.kind()) {
        "<ident>" | "Lean.Parser.Term.dotIdent" => ExplicitHead::Atom,
        "Lean.Parser.Term.proj" => {
            let (_, field) = head::proj_parts(&base)?;
            if has_univs && kinds.name(field.kind()) == "fieldIdx" {
                ExplicitHead::Other
            } else {
                ExplicitHead::Atom
            }
        }
        _ => ExplicitHead::Other,
    })
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
pub(crate) fn explicit_univ_parts(elem: &SynElem) -> Result<(SynElem, Vec<SynElem>), ElabError> {
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
/// `@` applied to anything outside the seven accepted shapes
/// (`explicit_head_shape`) is `App.lean:2118`'s `` `(@$_) =>
/// throwUnsupportedSyntax `` — an INVALID occurrence of `@` in a
/// function position, NOT the implicit-lambda-disabling form (that one
/// is only reachable when the `@..` node is the whole term, i.e. through
/// `elab_explicit` above). That includes `@(e).1.{us}`, for which the
/// oracle has no row. leanr reports it as `UnsupportedSyntax` citing
/// `App.lean:2118`, the same mapping every other invalid `@` shape gets.
/// Since M4b-4a P1 task 7 a projection after `@` is accepted and reaches
/// `head::elab_app_fn`'s proj arm with `explicit := true`; since M4b-4a
/// P4 `@.f` (`App.lean:2115-2116`) is an `elabAtom` shape like the others
/// and reaches its dotIdent arm.
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
        match explicit_head_shape(&cur, kinds)? {
            ExplicitHead::Atom => {}
            ExplicitHead::Other => {
                return Err(ElabError::UnsupportedSyntax(format!(
                    "invalid occurrence of `@` in a function position (`{}`) \
                     — App.lean:2118",
                    kinds.name(cur.kind())
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

/// The arguments of one application, as `elabAppFn` threads them
/// (`App.lean:2060-2061`: `namedArgs args expectedType? explicit
/// ellipsis`). Grouped so the recursion in `head::elab_app_fn` and the
/// LVal loop in `lval::elab_app_lvals` pass one value, not six.
/// `stx` is `Context::stx` (the WHOLE application — see that field's doc).
pub struct AppCall {
    pub named_args: Vec<NamedArg>,
    pub args: Vec<Arg>,
    pub expected: Option<ExprId>,
    pub explicit: bool,
    pub ellipsis: bool,
    pub stx: SynElem,
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
/// unported head (`choice` — the overloading slice) as a named seam rather than
/// mis-elaborating it.
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
    let call = AppCall {
        named_args,
        args,
        expected,
        explicit,
        ellipsis,
        stx,
    };
    let candidates = head::elab_app_fn(elab, &head, kinds, &explicit_levels, Vec::new(), call)?;
    overload::expect_single(candidates)
}

/// oracle: `elabAppArgs` (`App.lean:1351-1394`), building the
/// `Context`/`State` the loop runs over. Called from
/// `lval::elab_app_lvals` (the oracle's `elabAppLVals` calls
/// `elabAppArgs`), so it runs on the FINAL head, after any LVals.
pub(crate) fn elab_app_args(
    elab: &mut TermElabM,
    f: ExprId,
    call: AppCall,
    kinds: &KindInterner,
) -> Result<ExprId, ElabError> {
    let AppCall {
        named_args,
        args,
        expected,
        explicit,
        ellipsis,
        stx,
    } = call;

    // oracle: `elabAppArgs`'s first two lines — `let fType ← inferType f;
    // let fType ← instantiateMVars fType`.
    let f_type = elab.mctx.infer_type(f)?;
    let f_type = elab.mctx.instantiate_mvars(f_type)?;
    // oracle: `unless namedArgs.isEmpty && args.isEmpty do
    // tryPostponeIfMVar fType` (`App.lean:1366-1367`) — an mvar-typed
    // head with something to apply waits for its type. With
    // postponement off it falls through to `main`, whose
    // `synthesize_pending_and_normalize_fun_type` reports
    // `FunctionExpected`.
    if !(named_args.is_empty() && args.is_empty()) {
        elab.try_postpone_if_mvar(f_type)?;
    }

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
    //     carries `ConstantInfo::Rec`, so `head::elab_app_fn_id` now
    //     raises a named M4b-4c seam for a genuine recursor head. The
    //     `explicit || ellipsis` early-out (`App.lean:1399`) is honoured
    //     — `head::elab_app_fn_id`'s `heed` — so `@Nat.rec` and `Nat.rec ..`
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
    // itself: M4b-4c owns it.
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
    // Bracket the whole loop (M4b-2's `binder/forall.rs`'s
    // `elab_binders_and_forall` idiom):
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
