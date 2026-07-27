//! M4b-3 P1: the application elaborator. Oracle: `Lean/Elab/App.lean`'s
//! `ElabAppArgs` namespace. See
//! docs/superpowers/specs/2026-07-25-m4b3-application-elaborator-design.md
//! § P1 — the application machinery.
//!
//! NOT in this plan, each a named seam (never a silent fall-through):
//!   instance-implicit arguments + the synthetic-mvar fixpoint . P2
//!   num/char/scientific literals ......................... P3
//!   coercions (CoeT/CoeFun/CoeSort, mkCoe) ............... P4
//!   optParam defaults / autoParam / `..` ellipsis ........ P5
//!   implicit-lambda insertion ............................ P5
//!   overload resolution (candidates > 1) ................. resolve_global slice
//!   elabAsElim, dot notation, LVal machinery ............. M4b-4

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
/// wraps the whole thing; that checkpoint maps onto leanr_meta's postponed
/// level-constraint queue and lands in P2 with `process_postponed`.
pub fn elab_app(
    elab: &mut TermElabM,
    node: &SyntaxNode,
    kinds: &KindInterner,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let (head, named_args, args, ellipsis) = expand::expand_app(node, kinds)?;
    elab_app_aux(elab, &head, kinds, named_args, args, ellipsis, expected)
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
    elab_app_aux(elab, elem, kinds, Vec::new(), Vec::new(), false, expected)
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
fn elab_app_aux(
    elab: &mut TermElabM,
    head: &SynElem,
    kinds: &KindInterner,
    named_args: Vec<NamedArg>,
    args: Vec<Arg>,
    ellipsis: bool,
    expected: Option<ExprId>,
) -> Result<ExprId, ElabError> {
    let (head, explicit, explicit_levels) = peel_head(elab, head, kinds)?;
    let candidates = head::elab_app_fn(elab, &head, kinds, &explicit_levels)?;
    let f = overload::expect_single(candidates)?;

    // oracle: `elabAppArgs`'s first two lines — `let fType ← inferType f;
    // let fType ← instantiateMVars fType`.
    let f_type = elab.mctx.infer_type(f)?;
    let f_type = elab.mctx.instantiate_mvars(f_type)?;

    // oracle: `App.lean:1374`'s `if (← isElabAsElim ..) then
    // elabAppArgsAux ..` branch reads the `@[elab_as_elim]` attribute —
    // an environment EXTENSION leanr does not decode, so there is no way
    // to consult it here and no way for it to be true. Task 9 records
    // this as a fixture-scoped seam and adds the fixture-source gate
    // (no `@[elab_as_elim]` declaration in `Elab0.lean`) that keeps the
    // branch inert rather than silently mis-taken.
    let ctx = Context {
        ellipsis,
        explicit,
        // oracle: `App.lean:1355`'s `env.contains ``Lean.Internal.coeM &&
        // resultIsOutParamSupport && !explicit`. Computed the same way,
        // not shortcut to `false`: it happens to be false throughout the
        // hermetic fixture env because prelude-mode `Elab0` declares no
        // `Lean.Internal.coeM`, and that must stay an OBSERVATION about
        // the env rather than an assumption baked into the code.
        result_is_out_param_support: env_contains_coe_m(elab)? && !explicit,
        // oracle: `Context.numImplicitParams` — the max over `namedArgs`.
        num_implicit_params: named_args
            .iter()
            .map(|n| n.num_implicit_params)
            .max()
            .unwrap_or(0),
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
        // oracle: `propagateExpectedTypeFor f` (`App.lean:1381`) consults
        // the `elab_without_expected_type` attribute — another extension
        // leanr does not decode, so this is `true` for every head, which
        // is the attribute's own default. Task 9 records the seam.
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
